/*
 * Copyright (c) 2007 Mockito contributors
 * This program is made available under the terms of the MIT License.
 */
package org.mockito.internal.stubbing;

import org.mockito.internal.MockitoCore;
import org.mockito.quality.Strictness;
import org.mockito.stubbing.Answer;
import org.mockito.stubbing.LenientStubber;
import org.mockito.stubbing.OngoingStubbing;
import org.mockito.stubbing.Stubber;

public class DefaultLenientStubber implements LenientStubber {

    private static final MockitoCore MOCKITO_CORE = new MockitoCore();

//@ ensures \result == stubber();
    @Override
    public Stubber doThrow(Throwable... toBeThrown) {
        return stubber().doThrow(toBeThrown);
    }

//@ ensures \result == stubber();
    @Override
    public Stubber doThrow(Class<? extends Throwable> toBeThrown) {
        return stubber().doThrow(toBeThrown);
    }

//@ ensures \result == stubber();
    @Override
    public Stubber doThrow(
            Class<? extends Throwable> toBeThrown, Class<? extends Throwable>... nextToBeThrown) {
        return stubber().doThrow(toBeThrown, nextToBeThrown);
    }

//@ ensures \result == stubber();
    @Override
    public Stubber doAnswer(Answer answer) {
        return stubber().doAnswer(answer);
    }

//@ ensures \result == stubber();
    @Override
    public Stubber doNothing() {
        return stubber().doNothing();
    }

//@ requires allowNull(toBeReturned);
    @Override
    public Stubber doReturn(Object toBeReturned) {
        return stubber().doReturn(toBeReturned);
    }

//@ requires nextToBeReturned!= null && \nonnullelements(nextToBeReturned);
    @Override
    public Stubber doReturn(Object toBeReturned, Object... nextToBeReturned) {
        return stubber().doReturn(toBeReturned, nextToBeReturned);
    }

//@ ensures \result == stubber();
    @Override
    public Stubber doCallRealMethod() {
        return stubber().doCallRealMethod();
    }

//@ ensures \result.isStrictness() == strictness;
    @Override
    public <T> OngoingStubbing<T> when(T methodCall) {
        OngoingStubbingImpl<T> ongoingStubbing =
                (OngoingStubbingImpl) MOCKITO_CORE.when(methodCall);
        ongoingStubbing.setStrictness(Strictness.LENIENT);
        return ongoingStubbing;
    }

//@ ensures \result!= null;
    private static Stubber stubber() {
        return MOCKITO_CORE.stubber(Strictness.LENIENT);
    }
}
