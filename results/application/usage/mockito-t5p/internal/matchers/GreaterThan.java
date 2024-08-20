/*
 * Copyright (c) 2007 Mockito contributors
 * This program is made available under the terms of the MIT License.
 */
package org.mockito.internal.matchers;

import java.io.Serializable;

public class GreaterThan<T extends Comparable<T>> extends CompareTo<T> implements Serializable {

    public GreaterThan(T value) {
        super(value);
    }

//@ requires l <= ((long)u)+1;
//@ ensures l <= ((long)u)+1;
    @Override
    protected String getName() {
        return "gt";
    }

//@ ensures \result > 0;
    @Override
    protected boolean matchResult(int result) {
        return result > 0;
    }
}
