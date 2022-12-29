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

package pascal.taie.analysis.dataflow.inter;

import java.util.List;
import java.util.Map;
import java.util.Set;

import pascal.taie.World;
import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
import pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation;
import pascal.taie.analysis.dataflow.analysis.constprop.Value;
import pascal.taie.analysis.graph.cfg.CFGBuilder;
import pascal.taie.analysis.graph.icfg.CallEdge;
import pascal.taie.analysis.graph.icfg.CallToReturnEdge;
import pascal.taie.analysis.graph.icfg.NormalEdge;
import pascal.taie.analysis.graph.icfg.ReturnEdge;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.InstanceFieldAccess;
import pascal.taie.ir.exp.InvokeExp;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.ir.stmt.LoadArray;
import pascal.taie.ir.stmt.LoadField;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.ir.stmt.StoreArray;
import pascal.taie.ir.stmt.StoreField;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;
import pascal.taie.util.collection.HybridArrayHashMap;
import pascal.taie.util.collection.HybridArrayHashSet;

/**
 * Implementation of interprocedural constant propagation for int values.
 */
public class InterConstantPropagation extends
        AbstractInterDataflowAnalysis<JMethod, Stmt, CPFact> {

    public static final String ID = "inter-constprop";

    private final ConstantPropagation cp;
    private Map<JField, Set<StoreField>> storeStaticFields;
    private Map<JField, Set<LoadField>> loadStaticFields;
    private Map<Var, Set<StoreField>> storeInstanceFields;
    private Map<Var, Set<LoadField>> loadInstanceFields;
    private Map<Var, Set<StoreArray>> storeArrays;
    private Map<Var, Set<LoadArray>> loadArrays;

    public InterConstantPropagation(AnalysisConfig config) {
        super(config);
        cp = new ConstantPropagation(new AnalysisConfig(ConstantPropagation.ID));
    }

    @Override
    protected void initialize() {
        String ptaId = getOptions().getString("pta");
        PointerAnalysisResult pta = World.get().getResult(ptaId);
        // You can do initialization work here
        storeStaticFields = new HybridArrayHashMap<>();
        loadStaticFields = new HybridArrayHashMap<>();
        storeInstanceFields = new HybridArrayHashMap<>();
        loadInstanceFields = new HybridArrayHashMap<>();
        storeArrays = new HybridArrayHashMap<>();
        loadArrays = new HybridArrayHashMap<>();

        pta.getCallGraph().reachableMethods().forEach(jMethod -> {
            IR ir = jMethod.getIR();
            for (Stmt stmt : ir.getStmts()) {
                if (stmt instanceof StoreField storeField && storeField.isStatic()) {
                    var key = storeField.getFieldRef().resolve();
                    var storeFieldSet = storeStaticFields.computeIfAbsent(key, x -> new HybridArrayHashSet<>());
                    storeFieldSet.add(storeField);
                } else if (stmt instanceof LoadField loadField && loadField.isStatic()) {
                    var key = loadField.getFieldRef().resolve();
                    var loadFieldSet = loadStaticFields.computeIfAbsent(key, x -> new HybridArrayHashSet<>());
                    loadFieldSet.add(loadField);
                }
            }
        });

        for (Var base : pta.getVars()) {
            for (Var var : pta.getVars()) {
                if (existsIntersection(pta.getPointsToSet(base), pta.getPointsToSet(var))) {
                    var storeFieldSet = storeInstanceFields.computeIfAbsent(base, x -> new HybridArrayHashSet<>());
                    storeFieldSet.addAll(var.getStoreFields());
                    var loadFieldSet = loadInstanceFields.computeIfAbsent(base, x -> new HybridArrayHashSet<>());
                    loadFieldSet.addAll(var.getLoadFields());
                    var storeArraySet = storeArrays.computeIfAbsent(base, x -> new HybridArrayHashSet<>());
                    storeArraySet.addAll(var.getStoreArrays());
                    var loadArraySet = loadArrays.computeIfAbsent(base, x -> new HybridArrayHashSet<>());
                    loadArraySet.addAll(var.getLoadArrays());
                }
            }
        }
    }

    @Override
    public boolean isForward() {
        return cp.isForward();
    }

    @Override
    public CPFact newBoundaryFact(Stmt boundary) {
        IR ir = icfg.getContainingMethodOf(boundary).getIR();
        return cp.newBoundaryFact(ir.getResult(CFGBuilder.ID));
    }

    @Override
    public CPFact newInitialFact() {
        return cp.newInitialFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        cp.meetInto(fact, target);
    }

    @Override
    protected boolean transferCallNode(Stmt stmt, CPFact in, CPFact out) {
        // DONE
        return out.copyFrom(in);
    }

    @Override
    protected boolean transferNonCallNode(Stmt stmt, CPFact in, CPFact out) {
        // DONE
        if (stmt instanceof StoreField storeField) {
            return transferStoreFieldNode(storeField, in, out);
        }
        if (stmt instanceof LoadField loadField) {
            return transferLoadFieldNode(loadField, in, out);
        }
        if (stmt instanceof StoreArray storeArray) {
            return transferStoreArrayNode(storeArray, in, out);
        }
        if (stmt instanceof LoadArray loadArray) {
            return transferLoadArrayNode(loadArray, in, out);
        }
        return cp.transferNode(stmt, in, out);
    }

    protected boolean transferStoreFieldNode(StoreField storeField, CPFact in, CPFact out) {
        boolean isUpdated = out.copyFrom(in);
        Var x = storeField.getRValue();
        if (isUpdated && ConstantPropagation.canHoldInt(x)) {
            JField jField = storeField.getFieldRef().resolve();
            if (storeField.isStatic()) {
                Set<LoadField> loadStaticSet = loadStaticFields.get(jField);
                if (loadStaticSet != null) {
                    solver.workListAdd(loadStaticSet);
                }
            } else {
                var instanceFieldAccess = (InstanceFieldAccess) storeField.getFieldAccess();
                Var base = instanceFieldAccess.getBase();
                Set<LoadField> loadInstanceSet = loadInstanceFields.get(base);
                if (loadInstanceSet != null) {
                    for (LoadField loadField : loadInstanceSet) {
                        var loadJField = loadField.getFieldRef().resolve();
                        if (loadJField.equals(jField)) {
                            solver.workListAdd(loadField);
                        }
                    }
                }
            }
        }
        return isUpdated;
    }

    protected boolean transferLoadFieldNode(LoadField loadField, CPFact in, CPFact out) {
        Var x = loadField.getLValue();
        if (!ConstantPropagation.canHoldInt(x)) {
            return out.copyFrom(in);
        }
        CPFact inCopy = in.copy();
        JField jField = loadField.getFieldRef().resolve();
        if (loadField.isStatic()) { // static x = T.f
            Set<StoreField> storeStaticSet = storeStaticFields.get(jField);
            if (storeStaticSet != null) {
                Value metValue = null;
                for (StoreField storeField : storeStaticSet) {
                    CPFact outFact = solver.getOutFact(storeField);
                    Value loadedValue = outFact.get(storeField.getRValue());
                    if (metValue == null) {
                        metValue = loadedValue;
                    } else {
                        metValue = cp.meetValue(metValue, loadedValue);
                    }
                }
                if (metValue != null) {
                    inCopy.update(x, metValue);
                }
            }
        } else { // instance x = o.f
            InstanceFieldAccess fieldAccess = (InstanceFieldAccess) loadField.getFieldAccess();
            Var base = fieldAccess.getBase();
            Set<StoreField> storeInstanceSet = storeInstanceFields.get(base);
            if (storeInstanceSet != null) {
                Value metValue = null;
                for (StoreField storeField : storeInstanceSet) {
                    if (jField.equals(storeField.getFieldRef().resolve())) {
                        CPFact outFact = solver.getOutFact(storeField);
                        Value loadedValue = outFact.get(storeField.getRValue());
                        if (metValue == null) {
                            metValue = loadedValue;
                        } else {
                            metValue = cp.meetValue(metValue, loadedValue);
                        }
                    }
                }
                if (metValue != null) {
                    inCopy.update(x, metValue);
                }
            }
        }
        return out.copyFrom(inCopy);
    }

    protected boolean transferStoreArrayNode(StoreArray storeArray, CPFact in, CPFact out) {
        boolean isUpdated = out.copyFrom(in);
        Var x = storeArray.getRValue();
        if (isUpdated && ConstantPropagation.canHoldInt(x)) {
            Var base = storeArray.getArrayAccess().getBase();
            Set<LoadArray> loadArraySet = loadArrays.get(base);
            if (loadArraySet != null) {
                for (LoadArray loadArray : loadArraySet) {
                    solver.workListAdd(loadArray);
                }
            }
        }
        return isUpdated;
    }

    protected boolean transferLoadArrayNode(LoadArray loadArray, CPFact in, CPFact out) {
        Var x = loadArray.getLValue();
        if (!ConstantPropagation.canHoldInt(x)) {
            return out.copyFrom(in);
        }
        CPFact inCopy = in.copy();

        Var indexVar = loadArray.getArrayAccess().getIndex();
        Var base = loadArray.getArrayAccess().getBase();
        Set<StoreArray> storeArraySet = storeArrays.get(base);
        if (storeArraySet != null) {
            Value metValue = null;
            for (StoreArray storeArray : storeArraySet) {
                Value value1 = in.get(indexVar);
                Value value2 = solver.getOutFact(storeArray).get(storeArray.getArrayAccess().getIndex());
                if (isSameIndex(value1, value2)) {
                    Value loadedValue = solver.getOutFact(storeArray).get(storeArray.getRValue());
                    if (metValue == null) {
                        metValue = loadedValue;
                    } else {
                        metValue = cp.meetValue(metValue, loadedValue);
                    }
                }
            }
            if (metValue != null) {
                inCopy.update(x, metValue);
            }
        }
        return out.copyFrom(inCopy);
    }

    @Override
    protected CPFact transferNormalEdge(NormalEdge<Stmt> edge, CPFact out) {
        // DONE
        return out.copy();
    }

    @Override
    protected CPFact transferCallToReturnEdge(CallToReturnEdge<Stmt> edge, CPFact out) {
        // DONE
        Stmt callSite = edge.getSource();
        var invoke = (Invoke) callSite;
        Var var = invoke.getResult();
        if (var != null) {
            CPFact fact = out.copy();
            fact.remove(var);
            return fact;
        } else {
            return out.copy();
        }
    }

    @Override
    protected CPFact transferCallEdge(CallEdge<Stmt> edge, CPFact callSiteOut) {
        // DONE
        CPFact calleeInFact = new CPFact();
        JMethod callee = edge.getCallee();
        InvokeExp invokeExp = ((Invoke) edge.getSource()).getInvokeExp();
        List<Var> argList = invokeExp.getArgs();
        List<Var> paramList = callee.getIR().getParams();
        for (int i = 0; i < argList.size(); i++) {
            Var arg = argList.get(i);
            Var param = paramList.get(i);
            if (ConstantPropagation.canHoldInt(arg)) {
                calleeInFact.update(param, callSiteOut.get(arg));
            }
        }
        return calleeInFact;
    }

    @Override
    protected CPFact transferReturnEdge(ReturnEdge<Stmt> edge, CPFact returnOut) {
        // DONE
        CPFact fact = new CPFact();
        Stmt callSite = edge.getCallSite();
        Invoke invoke = ((Invoke) callSite);
        Var invokeResult = invoke.getResult();
        if (invokeResult != null) {
            for (Var returnVar : edge.getReturnVars()) {
                Value value = returnOut.get(returnVar);
                Value metValue = cp.meetValue(fact.get(invokeResult), value);
                fact.update(invokeResult, metValue);
            }
        }
        return fact;
    }

    private boolean isSameIndex(Value value1, Value value2) {
        if (value1.isUndef() || value2.isUndef()) {
            return false;
        }
        if (value1.isConstant() && value2.isConstant()) {
            return value1.getConstant() == value2.getConstant();
        }
        return true;
    }

    private boolean existsIntersection(Set<Obj> set1, Set<Obj> set2) {
        if (!set1.isEmpty() && !set2.isEmpty()) {
            for (Obj obj : set1) {
                if (set2.contains(obj)) {
                    return true;
                }
            }
        }
        return false;
    }
}
