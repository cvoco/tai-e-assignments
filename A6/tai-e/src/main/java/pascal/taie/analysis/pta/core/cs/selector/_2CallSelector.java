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

package pascal.taie.analysis.pta.core.cs.selector;

import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.context.ListContext;
import pascal.taie.analysis.pta.core.cs.element.CSCallSite;
import pascal.taie.analysis.pta.core.cs.element.CSMethod;
import pascal.taie.analysis.pta.core.cs.element.CSObj;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.language.classes.JMethod;

/**
 * Implementation of 2-call-site sensitivity.
 */
public class _2CallSelector implements ContextSelector {

    @Override
    public Context getEmptyContext() {
        return ListContext.make();
    }

    @Override
    public Context selectContext(CSCallSite callSite, JMethod callee) {
        // DONE
        return selectContext(callSite, null, callee);
    }

    @Override
    public Context selectContext(CSCallSite callSite, CSObj recv, JMethod callee) {
        // DONE
        Context callSiteContext = callSite.getContext();
        int callSiteContextLength = callSiteContext.getLength();
        Invoke invoke = callSite.getCallSite();
        if (callSiteContextLength == 0) {
            return ListContext.make(invoke);
        }
        var element = callSiteContext.getElementAt(callSiteContextLength - 1);
        return ListContext.make(element, invoke);
    }

    @Override
    public Context selectHeapContext(CSMethod method, Obj obj) {
        // DONE
        Context methodInContext = method.getContext();
        int methodInContextLength = methodInContext.getLength();
        if (methodInContextLength == 0) {
            return ListContext.make();
        }
        var element = methodInContext.getElementAt(methodInContextLength - 1);
        return ListContext.make(element);
    }
}
