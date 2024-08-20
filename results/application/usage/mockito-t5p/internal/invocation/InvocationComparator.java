/*
 * Copyright (c) 2016 Mockito contributors
 * This program is made available under the terms of the MIT License.
 */
package org.mockito.internal.invocation;

import java.util.Comparator;

import org.mockito.invocation.Invocation;

/**
 * Compares invocations based on the sequence number
 */
public class InvocationComparator implements Comparator<Invocation> {
//@ requires 0 <= o1.getSequenceNumber() && o1.getSequenceNumber() <= numInstances();
//@ requires 0 <= o2.getSequenceNumber() && o2.getSequenceNumber() <= numInstances();
    @Override
    public int compare(Invocation o1, Invocation o2) {
        return Integer.compare(o1.getSequenceNumber(), o2.getSequenceNumber());
    }
}
