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

package pascal.taie.analysis.dataflow.analysis.constprop;

import pascal.taie.analysis.dataflow.analysis.AbstractDataflowAnalysis;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.exp.ArithmeticExp;
import pascal.taie.ir.exp.BinaryExp;
import pascal.taie.ir.exp.BitwiseExp;
import pascal.taie.ir.exp.ConditionExp;
import pascal.taie.ir.exp.Exp;
import pascal.taie.ir.exp.IntLiteral;
import pascal.taie.ir.exp.ShiftExp;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.DefinitionStmt;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.type.PrimitiveType;
import pascal.taie.language.type.Type;

public class ConstantPropagation extends
        AbstractDataflowAnalysis<Stmt, CPFact> {

    public static final String ID = "constprop";

    public ConstantPropagation(AnalysisConfig config) {
        super(config);
    }

    @Override
    public boolean isForward() {
        return true;
    }

    @Override
    public CPFact newBoundaryFact(CFG<Stmt> cfg) {
        CPFact fact = new CPFact();
        for (Var var : cfg.getIR().getVars()) {
            fact.update(var, Value.getNAC());
        }
        return fact;
    }

    @Override
    public CPFact newInitialFact() {
        return new CPFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        fact.entries().forEach((entry) -> {
            Var key = entry.getKey();
            Value factValue = entry.getValue();
            Value targetValue = target.get(key);
            // it will be OK even if target is undef
            Value value = meetValue(factValue, targetValue);
            target.update(key, value);
        });
    }

    /**
     * Meets two Values.
     */
    public Value meetValue(Value v1, Value v2) {
        if (v1.isNAC() || v2.isNAC()) {
            return Value.getNAC();
        }
        if (v1.isUndef()) {
            return v2;
        }
        if (v2.isUndef()) {
            return v1;
        }
        if (v1.isConstant() && v2.isConstant()) {
            if (v1.getConstant() != v2.getConstant()) {
                return Value.getNAC();
            }
            return v1;
        }
        return null; // unreachable
    }

    @Override
    public boolean transferNode(Stmt stmt, CPFact in, CPFact out) {
        CPFact oldOut = out.copy();
        if (stmt instanceof DefinitionStmt<?, ?> definitionStmt) {
            var def = (Var) definitionStmt.getLValue();
            var exp = (Exp) definitionStmt.getRValue();
            for (var entry : in.entries().toList()) {
                Var key = entry.getKey();
                if (!key.equals(def)) {
                    Value value = entry.getValue();
                    if (!value.isNAC()) {
                        out.update(key, value);
                    }
                }
            }
            var var = (Var) definitionStmt.getLValue();
            Value value = evaluate(exp, in);
            if (value != null) {
                out.update(var, value);
            }
        }
        return !oldOut.equals(out);
    }

    /**
     * @return true if the given variable can hold integer value, otherwise false.
     */
    public static boolean canHoldInt(Var var) {
        Type type = var.getType();
        if (type instanceof PrimitiveType) {
            switch ((PrimitiveType) type) {
                case BYTE:
                case SHORT:
                case INT:
                case CHAR:
                case BOOLEAN:
                    return true;
            }
        }
        return false;
    }

    /**
     * Evaluates the {@link Value} of given expression.
     *
     * @param exp the expression to be evaluated
     * @param in  IN fact of the statement
     * @return the resulting {@link Value}
     */
    public static Value evaluate(Exp exp, CPFact in) {
        if (exp instanceof Var var) {
            return in.get(var);
        }
        if (exp instanceof IntLiteral intLiteral) {
            return Value.makeConstant(intLiteral.getValue());
        }
        if (exp instanceof BinaryExp binaryExp) {
            Value lValue = in.get(binaryExp.getOperand1());
            Value rValue = in.get(binaryExp.getOperand2());
            if (lValue.isConstant() && rValue.isConstant()) {
                int lConst = lValue.getConstant();
                int rConst = rValue.getConstant();
                int oConst = evaluateBinaryExp(binaryExp, lConst, rConst);
                return Value.makeConstant(oConst);
            }
            if (lValue.isNAC() || rValue.isNAC()) {
                return Value.getNAC();
            }
            return Value.getUndef();
        }
        return null;
    }

    private static int evaluateBinaryExp(BinaryExp binaryExp, int lhs, int rhs) {
        if (binaryExp instanceof ArithmeticExp arithmeticExp) {
            switch (arithmeticExp.getOperator()) {
                case ADD:
                    return lhs + rhs;
                case DIV:
                    return lhs / rhs;
                case MUL:
                    return lhs * rhs;
                case REM:
                    return lhs % rhs;
                case SUB:
                    return lhs - rhs;
            }
        }
        if (binaryExp instanceof ConditionExp conditionExp) {
            switch (conditionExp.getOperator()) {
                case EQ:
                    return lhs == rhs ? 1 : 0;
                case GE:
                    return lhs >= rhs ? 1 : 0;
                case GT:
                    return lhs > rhs ? 1 : 0;
                case LE:
                    return lhs <= rhs ? 1 : 0;
                case LT:
                    return lhs < rhs ? 1 : 0;
                case NE:
                    return lhs != rhs ? 1 : 0;
            }
        }
        if (binaryExp instanceof ShiftExp shiftExp) {
            switch (shiftExp.getOperator()) {
                case SHL:
                    return lhs << rhs;
                case SHR:
                    return lhs >> rhs;
                case USHR:
                    return lhs >>> rhs;
            }
        }
        if (binaryExp instanceof BitwiseExp bitwiseExp) {
            switch (bitwiseExp.getOperator()) {
                case AND:
                    return lhs & rhs;
                case OR:
                    return lhs | rhs;
                case XOR:
                    return lhs ^ rhs;
                default:
                    break;
            }
        }
        return Integer.MIN_VALUE; // unreachable
    }
}
