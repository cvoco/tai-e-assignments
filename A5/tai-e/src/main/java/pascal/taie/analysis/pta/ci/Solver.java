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

package pascal.taie.analysis.pta.ci;

import java.util.LinkedList;
import java.util.List;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import pascal.taie.World;
import pascal.taie.analysis.graph.callgraph.CallGraphs;
import pascal.taie.analysis.graph.callgraph.CallKind;
import pascal.taie.analysis.graph.callgraph.DefaultCallGraph;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.pta.core.heap.HeapModel;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.Copy;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.ir.stmt.LoadField;
import pascal.taie.ir.stmt.New;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.ir.stmt.StmtVisitor;
import pascal.taie.ir.stmt.StoreField;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.Type;

class Solver {

    private static final Logger logger = LogManager.getLogger(Solver.class);

    private final HeapModel heapModel;

    private DefaultCallGraph callGraph;

    private PointerFlowGraph pointerFlowGraph;

    private WorkList workList;

    private StmtProcessor stmtProcessor;

    private ClassHierarchy hierarchy;

    Solver(HeapModel heapModel) {
        this.heapModel = heapModel;
    }

    /**
     * Runs pointer analysis algorithm.
     */
    void solve() {
        initialize();
        analyze();
    }

    /**
     * Initializes pointer analysis.
     */
    private void initialize() {
        workList = new WorkList();
        pointerFlowGraph = new PointerFlowGraph();
        callGraph = new DefaultCallGraph();
        stmtProcessor = new StmtProcessor();
        hierarchy = World.get().getClassHierarchy();
        // initialize main method
        JMethod main = World.get().getMainMethod();
        callGraph.addEntryMethod(main);
        addReachable(main);
    }

    /**
     * Processes new reachable method.
     */
    private void addReachable(JMethod method) {
        if (callGraph.addReachableMethod(method)) {
            for (Stmt stmt : method.getIR().getStmts()) {
                stmt.accept(stmtProcessor);
            }
        }
    }

    /**
     * Processes statements in new reachable methods.
     */
    private class StmtProcessor implements StmtVisitor<Void> {
        List<Stmt> stmtSet = new LinkedList<>();

        public Void visit(New allocSite) {
            // x = new C()
            Var var = allocSite.getLValue();
            workList.addEntry(pointerFlowGraph.getVarPtr(var), new PointsToSet(heapModel.getObj(allocSite)));
            visitDefault(allocSite);
            return null;
        }

        public Void visit(Copy stmt) {
            // x = y
            Var x = stmt.getLValue();
            Var y = stmt.getRValue();
            addPFGEdge(pointerFlowGraph.getVarPtr(y), pointerFlowGraph.getVarPtr(x));
            visitDefault(stmt);
            return null;
        }

        public Void visit(StoreField storeField) {
            // store static field x.f = y
            JField jField = storeField.getFieldRef().resolve();
            if (jField.isStatic()) {
                Var y = storeField.getRValue();
                addPFGEdge(pointerFlowGraph.getVarPtr(y), pointerFlowGraph.getStaticField(jField));
            }
            visitDefault(storeField);
            return null;
        }

        public Void visit(LoadField loadField) {
            // load static field y = x.f
            JField jField = loadField.getFieldRef().resolve();
            if (jField.isStatic()) {
                Var x = loadField.getLValue();
                addPFGEdge(pointerFlowGraph.getStaticField(jField), pointerFlowGraph.getVarPtr(x));
            }
            visitDefault(loadField);
            return null;
        }

        public Void visit(Invoke invoke) {
            if (invoke.isStatic()) {
                Var callSiteRetVar = invoke.getResult();
                JMethod callee = resolveCallee(null, invoke);
                if (callGraph.addEdge(new Edge<>(CallKind.STATIC, invoke, callee))) {
                    addReachable(callee);
                    List<Var> argList = invoke.getInvokeExp().getArgs();
                    IR ir = callee.getIR();
                    List<Var> paramList = ir.getParams();
                    assert argList.size() == paramList.size();
                    for (int i = 0; i < argList.size(); i++) {
                        var source = pointerFlowGraph.getVarPtr(argList.get(i));
                        var target = pointerFlowGraph.getVarPtr(paramList.get(i));
                        addPFGEdge(source, target);
                    }
                    if (callSiteRetVar != null) {
                        // not return void
                        VarPtr callSiteRetVarPtr = pointerFlowGraph.getVarPtr(callSiteRetVar);
                        for (Var returnVar : ir.getReturnVars()) {
                            addPFGEdge(pointerFlowGraph.getVarPtr(returnVar), callSiteRetVarPtr);
                        }
                    }
                }
            }
            visitDefault(invoke);
            return null;
        }

        public Void visitDefault(Stmt stmt) {
            stmtSet.add(stmt);
            return null;
        }
    }

    /**
     * Adds an edge "source -> target" to the PFG.
     */
    private void addPFGEdge(Pointer source, Pointer target) {
        if (pointerFlowGraph.addEdge(source, target)) {
            PointsToSet pt = source.getPointsToSet();
            if (!pt.isEmpty()) {
                workList.addEntry(target, pt);
            }
        }
    }

    /**
     * Processes work-list entries until the work-list is empty.
     */
    private void analyze() {
        while (!workList.isEmpty()) {
            WorkList.Entry entry = workList.pollEntry();
            Pointer ptr = entry.pointer();
            PointsToSet pts = entry.pointsToSet();
            PointsToSet delta = propagate(ptr, pts);
            if (ptr instanceof VarPtr varPtr) {
                Var x = varPtr.getVar();
                delta.forEach(obj -> {
                    for (var storeField : x.getStoreFields()) {
                        if (!storeField.isStatic()) { // x.f = y
                            var source = pointerFlowGraph.getVarPtr(storeField.getRValue());
                            var field = storeField.getFieldRef().resolve();
                            var target = pointerFlowGraph.getInstanceField(obj, field);
                            addPFGEdge(source, target);
                        }
                    }
                    for (var loadField : x.getLoadFields()) {
                        if (!loadField.isStatic()) { // y = x.f
                            var field = loadField.getFieldRef().resolve();
                            var source = pointerFlowGraph.getInstanceField(obj, field);
                            var target = pointerFlowGraph.getVarPtr(loadField.getLValue());
                            addPFGEdge(source, target);
                        }
                    }
                    for (var storeArray : x.getStoreArrays()) { // x[] = y
                        var source = pointerFlowGraph.getVarPtr(storeArray.getRValue());
                        var target = pointerFlowGraph.getArrayIndex(obj);
                        addPFGEdge(source, target);
                    }
                    for (var loadArray : x.getLoadArrays()) { // y = x[]
                        var source = pointerFlowGraph.getArrayIndex(obj);
                        var target = pointerFlowGraph.getVarPtr(loadArray.getLValue());
                        addPFGEdge(source, target);
                    }
                    // process method invocation
                    processCall(varPtr.getVar(), obj);
                });
            }
        }
    }

    /**
     * Propagates pointsToSet to pt(pointer) and its PFG successors,
     * returns the difference set of pointsToSet and pt(pointer).
     */
    private PointsToSet propagate(Pointer pointer, PointsToSet pointsToSet) {
        PointsToSet delta = new PointsToSet();
        if (!pointsToSet.isEmpty()) {
            PointsToSet pt = pointer.getPointsToSet();
            pointsToSet.objects().filter(obj -> !pt.contains(obj)).forEach(delta::addObject);
            delta.objects().forEach(pt::addObject);
            pointerFlowGraph.getSuccsOf(pointer).forEach(sucPtr -> workList.addEntry(sucPtr, delta));
        }
        return delta;
        // return null;
    }

    /**
     * Processes instance calls when points-to set of the receiver variable changes.
     *
     * @param var  the variable that holds receiver objects
     * @param recv a new discovered object pointed by the variable.
     */
    private void processCall(Var var, Obj recv) {
        for (Invoke invoke : var.getInvokes()) {
            if (!invoke.isStatic()) {
                CallKind callKind = CallGraphs.getCallKind(invoke);
                JMethod method = resolveCallee(recv, invoke);
                IR ir = method.getIR();
                // m_this -> {o_i}
                workList.addEntry(pointerFlowGraph.getVarPtr(ir.getThis()), new PointsToSet(recv));
                if (callGraph.addEdge(new Edge<>(callKind, invoke, method))) {
                    addReachable(method);
                    List<Var> paramList = ir.getParams();
                    List<Var> argList = invoke.getInvokeExp().getArgs();
                    assert paramList.size() == argList.size();
                    for (int i = 0; i < argList.size(); i++) {
                        var source = pointerFlowGraph.getVarPtr(argList.get(i));
                        var target = pointerFlowGraph.getVarPtr(paramList.get(i));
                        addPFGEdge(source, target);
                    }
                    Var callSiteRetVar = invoke.getResult();
                    if (callSiteRetVar != null) { // not return void
                        VarPtr callSiteRetVarPtr = pointerFlowGraph.getVarPtr(callSiteRetVar);
                        // may have multiple return vars
                        for (Var returnVar : ir.getReturnVars()) {
                            addPFGEdge(pointerFlowGraph.getVarPtr(returnVar), callSiteRetVarPtr);
                        }
                    }
                }
            }
        }
    }

    /**
     * Resolves the callee of a call site with the receiver object.
     *
     * @param recv     the receiver object of the method call. If the callSite
     *                 is static, this parameter is ignored (i.e., can be null).
     * @param callSite the call site to be resolved.
     * @return the resolved callee.
     */
    private JMethod resolveCallee(Obj recv, Invoke callSite) {
        Type type = recv != null ? recv.getType() : null;
        return CallGraphs.resolveCallee(type, callSite);
    }

    CIPTAResult getResult() {
        return new CIPTAResult(pointerFlowGraph, callGraph);
    }
}
