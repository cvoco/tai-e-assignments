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
        for (Var var : cfg.getIR().getParams()) {
            if (canHoldInt(var)) {
                fact.update(var, Value.getNAC());
            }
        }
        return fact;
    }

    @Override
    public CPFact newInitialFact() {
        return new CPFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        fact.forEach((key, factValue) -> {
            if (canHoldInt(key)) {
                Value targetValue = target.get(key);
                // it will be OK even if target is undef
                Value value = meetValue(factValue, targetValue);
                assert value != null;
                target.update(key, value);
            }
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
        boolean isChanged = false;
        if (stmt instanceof DefinitionStmt<?, ?> definitionStmt) { // x = y
            var x = definitionStmt.getLValue();
            // IN[s] – {(x, _)}
            for (var key : in.keySet()) {
                if (!key.equals(x)) {
                    var value = in.get(key);
                    isChanged |= out.update(key, value);
                }
            }
            if (x instanceof Var var && canHoldInt(var)) {
                var exp = (Exp) definitionStmt.getRValue();
                // gen = {(x, eval(y))}
                Value value = evaluate(exp, in);
                isChanged |= out.update(var, value);
            }
        } else {
            isChanged |= out.copyFrom(in);
        }
        return isChanged;
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
        if (exp instanceof IntLiteral intLiteral) { // x = c
            return Value.makeConstant(intLiteral.getValue());
        }
        if (exp instanceof Var var) { // x = y
            return in.get(var);
        }
        if (exp instanceof BinaryExp binaryExp) { // x = y op z
            Value y = in.get(binaryExp.getOperand1());
            Value z = in.get(binaryExp.getOperand2());
            if (y.isConstant() && z.isConstant()) { // both constants
                int yConst = y.getConstant();
                int zConst = z.getConstant();
                var op = binaryExp.getOperator();
                // div/rem 0
                if (op == ArithmeticExp.Op.DIV || op == ArithmeticExp.Op.REM) {
                    if (zConst == 0) {
                        return Value.getNAC();
                    }
                }
                int value = evaluateOp(op, yConst, zConst);
                return Value.makeConstant(value); // val(y) op val(z)
            }
            if (y.isNAC() || z.isNAC()) { // any NAC
                return Value.getNAC(); // NAC
            }
            // otherwise
            return Value.getUndef(); // UNDEF
        }
        return Value.getNAC(); // other unsolvable situations
    }

    private static int evaluateOp(BinaryExp.Op op, int y, int z) {
        if (op instanceof ArithmeticExp.Op arithmeticOp) {
            switch (arithmeticOp) {
                case ADD:
                    return y + z;
                case DIV:
                    return y / z;
                case MUL:
                    return y * z;
                case REM:
                    return y % z;
                case SUB:
                    return y - z;
            }
        }
        if (op instanceof ConditionExp.Op conditionOp) {
            switch (conditionOp) {
                case EQ:
                    return y == z ? 1 : 0;
                case GE:
                    return y >= z ? 1 : 0;
                case GT:
                    return y > z ? 1 : 0;
                case LE:
                    return y <= z ? 1 : 0;
                case LT:
                    return y < z ? 1 : 0;
                case NE:
                    return y != z ? 1 : 0;
            }
        }
        if (op instanceof ShiftExp.Op shiftOp) {
            switch (shiftOp) {
                case SHL:
                    return y << z;
                case SHR:
                    return y >> z;
                case USHR:
                    return y >>> z;
            }
        }
        if (op instanceof BitwiseExp.Op bitwiseOp) {
            switch (bitwiseOp) {
                case AND:
                    return y & z;
                case OR:
                    return y | z;
                case XOR:
                    return y ^ z;
            }
        }
        return Integer.MIN_VALUE; // unreachable
    }
}
