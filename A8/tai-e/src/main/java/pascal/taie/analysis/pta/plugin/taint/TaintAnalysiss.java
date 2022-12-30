/*
 * Tai-e: A Static Analysis Framework for Java
 *
 * Copyright (C) 2022 Tian Tan <tiantan@nju.edu.cn>
 * Copyright (C) 2022 Yue Li <yueli@nju.edu.cn>
 *
 * This file is part of Tai-e.
 *
 * Tai-e is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation, either version 3
 * of the License, or (at your option) any later version.
 *
 * Tai-e is distributed in the hope that it will be useful,but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
 * or FITNESS FOR A PARTICULAR PURPOSE. See the GNU Lesser General
 * Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with Tai-e. If not, see <https://www.gnu.org/licenses/>.
 */

package pascal.taie.analysis.pta.plugin.taint;

import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import pascal.taie.World;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.element.CSCallSite;
import pascal.taie.analysis.pta.core.cs.element.CSManager;
import pascal.taie.analysis.pta.core.cs.element.CSObj;
import pascal.taie.analysis.pta.core.cs.element.CSVar;
import pascal.taie.analysis.pta.cs.Solver;
import pascal.taie.analysis.pta.pts.PointsToSet;
import pascal.taie.ir.exp.InvokeExp;
import pascal.taie.ir.exp.InvokeInstanceExp;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.Type;
import pascal.taie.util.collection.Maps;
import pascal.taie.util.collection.MultiMap;

public class TaintAnalysiss {

    private static final Logger logger = LogManager.getLogger(TaintAnalysiss.class);

    private final TaintManager manager;

    private final TaintConfig config;

    private final Solver solver;

    private final CSManager csManager;

    private final Context emptyContext;

    private final Map<JMethod, Type> sources = Maps.newHybridMap();
    private final MultiMap<JMethod, Sink> sinks = Maps.newMultiMap();
    private final MultiMap<Sink, CSCallSite> sinkCalls = Maps.newMultiMap();
    private final MultiMap<JMethod, TaintTransfer> relevantTransfers = Maps.newMultiMap();
    private final MultiMap<CSVar, CSVar> transferEdges = Maps.newMultiMap();

    public TaintAnalysiss(Solver solver) {
        manager = new TaintManager();
        this.solver = solver;
        csManager = solver.getCSManager();
        emptyContext = solver.getContextSelector().getEmptyContext();

        String configPath = solver.getOptions().getString("taint-config");
        var hierarchy = World.get().getClassHierarchy();
        var typeSystem = World.get().getTypeSystem();
        config = TaintConfig.readConfig(configPath, hierarchy, typeSystem);

        for (var source : config.getSources()) {
            sources.put(source.method(), source.type());
        }
        for (var sink : config.getSinks()) {
            sinks.put(sink.method(), sink);
        }
        for (var taintTransfer : config.getTransfers()) {
            relevantTransfers.put(taintTransfer.method(), taintTransfer);
        }
    }

    public void checkSourceCalls(CSCallSite csCallSite) {
        JMethod method = csCallSite.getCallSite().getMethodRef().resolve();
        if (!sources.containsKey(method)) {
            return;
        }
        Context context = csCallSite.getContext();
        Invoke callSite = csCallSite.getCallSite();
        Type type = sources.get(method);
        Var callSiteReturnVar = callSite.getResult();
        CSVar csCallSiteReturnVar = csManager.getCSVar(context, callSiteReturnVar);
        var csObj = csManager.getCSObj(emptyContext, manager.makeTaint(callSite, type));
        solver.addWorkList(csCallSiteReturnVar, csObj);
    }

    public void checkSinkCalls(CSCallSite csCallSite) {
        JMethod jMethod = csCallSite.getCallSite().getMethodRef().resolve();
        if (sinks.containsKey(jMethod)) {
            for (Sink sink : sinks.get(jMethod)) {
                sinkCalls.put(sink, csCallSite);
            }
        }
    }

    public void checkEdges(CSCallSite csCallSite) {
        Invoke callSite = csCallSite.getCallSite();
        JMethod jMethod = callSite.getMethodRef().resolve();
        if (!relevantTransfers.containsKey(jMethod)) {
            return;
        }
        Set<TaintTransfer> taintTransfers = relevantTransfers.get(jMethod);
        for (TaintTransfer taintTransfer : taintTransfers) {
            CSVar fromVar = getTransferCSVar(csCallSite, taintTransfer.from());
            CSVar toVar = getTransferCSVar(csCallSite, taintTransfer.to());
            if (transferEdges.put(fromVar, toVar)) {
                PointsToSet fromPTS = fromVar.getPointsToSet();
                transferNode(fromPTS, toVar);
            }
        }
    }

    public void transferNode(PointsToSet from, CSVar to) {
        for (CSObj csObj : from.getObjects()) {
            var obj = csObj.getObject();
            if (manager.isTaint(obj)) {
                Invoke invoke = manager.getSourceCall(obj);
                var transferredTaint = manager.makeTaint(invoke, to.getType());
                CSObj taintCSObj = csManager.getCSObj(emptyContext, transferredTaint);
                solver.addWorkList(to, taintCSObj);
            }
        }
    }

    public void propagate(CSVar from, PointsToSet pts) {
        for (CSVar to : transferEdges.get(from)) {
            transferNode(pts, to);
        }
    }

    // DONE
    public void onFinish() {
        Set<TaintFlow> taintFlows = collectTaintFlows();
        solver.getResult().storeResult(getClass().getName(), taintFlows);
    }

    private CSVar getTransferCSVar(CSCallSite csCallSite, int index) {
        Invoke callSite = csCallSite.getCallSite();
        Context context = csCallSite.getContext();
        InvokeExp invokeExp = callSite.getInvokeExp();
        switch (index) {
            case TaintTransfer.RESULT:
                return csManager.getCSVar(context, callSite.getResult());
            case TaintTransfer.BASE:
                var invokeInstanceExp = (InvokeInstanceExp) invokeExp;
                return csManager.getCSVar(context, invokeInstanceExp.getBase());
            default:
                return csManager.getCSVar(context, invokeExp.getArg(index));
        }
    }

    private Set<TaintFlow> collectTaintFlows() {
        Set<TaintFlow> taintFlows = new TreeSet<>();
        PointerAnalysisResult result = solver.getResult();
        // DONE
        // You could query pointer analysis results you need via variable result.
        sinks.forEach((method, sink) -> {
            int sinkIndex = sink.index();
            for (var csCallSite : sinkCalls.get(sink)) {
                Context context = csCallSite.getContext();
                Invoke callSite = csCallSite.getCallSite();
                Var arg = callSite.getInvokeExp().getArg(sinkIndex);
                for (var csObj : result.getPointsToSet(csManager.getCSVar(context, arg))) {
                    var obj = csObj.getObject();
                    if (manager.isTaint(obj)) {
                        taintFlows.add(new TaintFlow(manager.getSourceCall(obj), callSite, sinkIndex));
                    }
                }
            }
        });
        return taintFlows;
    }
}
