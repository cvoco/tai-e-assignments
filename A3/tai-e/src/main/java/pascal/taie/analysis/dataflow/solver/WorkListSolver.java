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


package pascal.taie.analysis.dataflow.solver;

import java.util.LinkedList;
import java.util.Queue;
import java.util.Stack;

import pascal.taie.analysis.dataflow.analysis.DataflowAnalysis;
import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.graph.cfg.CFG;

class WorkListSolver<Node, Fact> extends Solver<Node, Fact> {

    WorkListSolver(DataflowAnalysis<Node, Fact> analysis) {
        super(analysis);
    }

    @Override
    protected void doSolveForward(CFG<Node> cfg, DataflowResult<Node, Fact> result) {
        Queue<Node> queue = new LinkedList<>();
        queue.addAll(cfg.getNodes());
        while (!queue.isEmpty()) {
            var node = queue.poll();
            Fact inFact = result.getInFact(node);
            for (Node outNode : cfg.getPredsOf(node)) {
                Fact outFact = result.getOutFact(outNode);
                analysis.meetInto(outFact, inFact);
            }
            Fact outFact = result.getOutFact(node);
            boolean isChanged = analysis.transferNode(node, inFact, outFact);
            if (isChanged) {
                queue.addAll(cfg.getSuccsOf(node));
            }
        }
    }

    @Override
    protected void doSolveBackward(CFG<Node> cfg, DataflowResult<Node, Fact> result) {
        Stack<Node> stack = new Stack<>();
        stack.addAll(cfg.getNodes());
        while (!stack.isEmpty()) {
            var node = stack.pop();
            Fact outFact = result.getOutFact(node);
            for (Node outNode : cfg.getSuccsOf(node)) {
                Fact inFact = result.getInFact(outNode);
                analysis.meetInto(inFact, outFact);
            }
            Fact inFact = result.getInFact(node);
            boolean isChanged = analysis.transferNode(node, inFact, outFact);
            if (isChanged) {
                stack.addAll(cfg.getSuccsOf(node));
            }
        }
    }
}
