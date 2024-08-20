/*
 * Copyright (c) 2007 Mockito contributors
 * This program is made available under the terms of the MIT License.
 */
package org.mockito.internal.stubbing.answers;

import static org.mockito.internal.exceptions.Reporter.cannotStubVoidMethodWithAReturnValue;
import static org.mockito.internal.exceptions.Reporter.wrongTypeOfReturnValue;

import java.io.Serializable;

import org.mockito.internal.util.KotlinInlineClassUtil;
import org.mockito.invocation.InvocationOnMock;
import org.mockito.stubbing.Answer;
import org.mockito.stubbing.ValidableAnswer;

public class Returns implements Answer<Object>, ValidableAnswer, Serializable {

    private static final long serialVersionUID = -6245608253574215396L;
    private final Object value;

    public Returns(Object value) {
        this.value = value;
    }

//@ requires value!= null;
    @Override
    public Object answer(InvocationOnMock invocation) throws Throwable {
        return KotlinInlineClassUtil.unboxUnderlyingValueIfNeeded(invocation, value);
    }

//@ requires invocation!= null
    @Override
    public void validateFor(InvocationOnMock invocation) {
        InvocationInfo invocationInfo = new InvocationInfo(invocation);
        if (invocationInfo.isVoid()) {
            throw cannotStubVoidMethodWithAReturnValue(invocationInfo.getMethodName());
        }

        if (returnsNull() && invocationInfo.returnsPrimitive()) {
            throw wrongTypeOfReturnValue(
                    invocationInfo.printMethodReturnType(), "null", invocationInfo.getMethodName());
        }

        if (!returnsNull()
                && !invocationInfo.isValidReturnType(returnType())
                && !KotlinInlineClassUtil.isInlineClassWithAssignableUnderlyingType(
                        returnType(), invocationInfo.getMethod().getReturnType())) {
            throw wrongTypeOfReturnValue(
                    invocationInfo.printMethodReturnType(),
                    printReturnType(),
                    invocationInfo.getMethodName());
        }
    }

//@ ensures \result!= null;
    private String printReturnType() {
        return value.getClass().getSimpleName();
    }

//@ ensures \result!= null;
    private Class<?> returnType() {
        return value.getClass();
    }

//@ ensures \result <==> value == null;
    private boolean returnsNull() {
        return value == null;
    }

//@ ensures \result!= null;
    @Override
    public String toString() {
        return "Returns: " + value;
    }
}
