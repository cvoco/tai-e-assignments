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

package pascal.taie.analysis.graph.callgraph;

import java.util.Deque;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.Set;
import java.util.Stack;

import pascal.taie.World;
import pascal.taie.ir.proginfo.MethodRef;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JClass;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.classes.Subsignature;

/**
 * Implementation of the CHA algorithm.
 */
class CHABuilder implements CGBuilder<Invoke, JMethod> {

    private ClassHierarchy hierarchy;

    @Override
    public CallGraph<Invoke, JMethod> build() {
        hierarchy = World.get().getClassHierarchy();
        return buildCallGraph(World.get().getMainMethod());
    }

    private CallGraph<Invoke, JMethod> buildCallGraph(JMethod entry) {
        var graph = new DefaultCallGraph();
        graph.addEntryMethod(entry);
        graph.addReachableMethod(entry);
        Deque<JMethod> workList = new LinkedList<>();
        workList.addLast(entry);
        while (!workList.isEmpty()) {
            JMethod jmethod = workList.removeFirst();
            graph.callSitesIn(jmethod).forEach(callSite -> {
                CallKind callKind = CallGraphs.getCallKind(callSite);
                Set<JMethod> callees = resolve(callSite);
                for (var resolvedMethod : callees) {
                    var edge = new Edge<>(callKind, callSite, resolvedMethod);
                    graph.addEdge(edge);
                    if (graph.addReachableMethod(resolvedMethod)) {
                        workList.add(resolvedMethod);
                    }
                }
            });
        }
        return graph;
    }

    /**
     * Resolves call targets (callees) of a call site via CHA.
     */
    private Set<JMethod> resolve(Invoke callSite) {
        Set<JMethod> callees = new HashSet<>();
        MethodRef methodRef = callSite.getMethodRef();
        JClass declaringClass = methodRef.getDeclaringClass();
        Subsignature subsignature = methodRef.getSubsignature();

        if (callSite.isStatic() || callSite.isSpecial()) {
            JMethod resolvedMethod = dispatch(declaringClass, subsignature);
            if (resolvedMethod != null && !resolvedMethod.isAbstract()) {
                callees.add(resolvedMethod);
            }
        } else if (callSite.isVirtual() || callSite.isInterface()) {
            Stack<JClass> classStack = new Stack<>();
            Set<JClass> visitedClasses = new HashSet<>();
            if (callSite.isInterface()) {
                Set<JClass> visitedInterfaces = new HashSet<>();
                Stack<JClass> interfaceStack = new Stack<>();
                visitedInterfaces.add(declaringClass);
                interfaceStack.push(declaringClass);
                while (!interfaceStack.isEmpty()) {
                    JClass jInterface = interfaceStack.pop();
                    var subInterfaces = hierarchy.getDirectSubinterfacesOf(jInterface);
                    var subInterfaceImpls = hierarchy.getDirectImplementorsOf(jInterface);
                    for (var subInterface : subInterfaces) {
                        if (visitedInterfaces.add(subInterface)) {
                            interfaceStack.push(subInterface);
                        }
                    }
                    for (var subInterfaceImpl : subInterfaceImpls) {
                        if (visitedClasses.add(subInterfaceImpl)) {
                            classStack.push(subInterfaceImpl);
                        }
                    }
                }
            } else {
                classStack.push(declaringClass);
            }
            while (!classStack.isEmpty()) {
                JClass jClass = classStack.pop();
                JMethod resolvedMethod = dispatch(jClass, subsignature);
                if (resolvedMethod != null && !resolvedMethod.isAbstract()) {
                    callees.add(resolvedMethod);
                }
                var subClasses = hierarchy.getDirectSubclassesOf(jClass);
                for (JClass subClass : subClasses) {
                    if (visitedClasses.add(subClass)) {
                        classStack.push(subClass);
                    }
                }
            }
        }
        return callees;
    }

    /**
     * Looks up the target method based on given class and method subsignature.
     *
     * @return the dispatched target method, or null if no satisfying method
     *         can be found.
     */
    private JMethod dispatch(JClass jclass, Subsignature subsignature) {
        JMethod targetMethod = jclass.getDeclaredMethod(subsignature);
        if (targetMethod != null) {
            return targetMethod;
        }
        JClass superClass = jclass.getSuperClass();
        if (superClass != null) {
            return dispatch(superClass, subsignature);
        }
        return null;
    }
}
