/*
 * Copyright (c) 2007 Mockito contributors
 * This program is made available under the terms of the MIT License.
 */
package org.mockito.internal.stubbing.answers;

import static org.mockito.internal.exceptions.Reporter.onlyVoidMethodsCanBeSetToDoNothing;

import java.io.Serializable;

import org.mockito.invocation.InvocationOnMock;
import org.mockito.stubbing.Answer;
import org.mockito.stubbing.ValidableAnswer;

public class DoesNothing implements Answer<Object>, ValidableAnswer, Serializable {

    private static final long serialVersionUID = 4840880517740698416L;

    private static final DoesNothing SINGLETON = new DoesNothing();

    private DoesNothing() {}

//@ ensures \result == SINGLETON;
    public static DoesNothing doesNothing() {
        return SINGLETON;
    }

//@ requires initialSize > 0 && sizeIncrease >= 0 && sizeMultiple >= 1;
//@ requires!(sizeIncrease == 0 && sizeMultiple == 1)
    @Override
    public Object answer(InvocationOnMock invocation) {
        return null;
    }

//@ ensures false
    @Override
    public void validateFor(InvocationOnMock invocation) {
        if (!new InvocationInfo(invocation).isVoid()) {
            throw onlyVoidMethodsCanBeSetToDoNothing();
        }
    }
}
