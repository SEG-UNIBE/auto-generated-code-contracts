/*
 * Copyright (c) 2007 Mockito contributors
 * This program is made available under the terms of the MIT License.
 */
package org.mockito.internal.stubbing;

import org.mockito.stubbing.Answer;
import org.mockito.stubbing.OngoingStubbing;

public class ConsecutiveStubbing<T> extends BaseStubbing<T> {

    private final InvocationContainerImpl invocationContainer;

    ConsecutiveStubbing(InvocationContainerImpl invocationContainer) {
        super(invocationContainer.invokedMock());
        this.invocationContainer = invocationContainer;
    }

//@ requires initialSize > 0 && sizeIncrease >= 0 && sizeMultiple >= 1;
//@ requires!(sizeIncrease == 0 && sizeMultiple == 1)
    @Override
    public OngoingStubbing<T> thenAnswer(Answer<?> answer) {
        invocationContainer.addConsecutiveAnswer(answer);
        return this;
    }
}
