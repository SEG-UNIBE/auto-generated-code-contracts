/*
 * Copyright (c) 2016 Mockito contributors
 * This program is made available under the terms of the MIT License.
 */
package org.mockito.internal.stubbing;

import java.util.Comparator;

import org.mockito.internal.invocation.InvocationComparator;
import org.mockito.stubbing.Stubbing;

/**
 * Compares stubbings based on {@link InvocationComparator}
 */
public class StubbingComparator implements Comparator<Stubbing> {

    private final InvocationComparator invocationComparator = new InvocationComparator();

//@ requires o1!= null && o2!= null;
//@ requires (o1.invocation == null || o2.invocation == null) && \invariant_for(o1) && \invariant_for(o2);
//@ ensures \result == invocationComparator.compare(o1.getInvocation(), o2.getInvocation());
    @Override
    public int compare(Stubbing o1, Stubbing o2) {
        return invocationComparator.compare(o1.getInvocation(), o2.getInvocation());
    }
}
