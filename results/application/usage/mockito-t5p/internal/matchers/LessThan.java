/*
 * Copyright (c) 2007 Mockito contributors
 * This program is made available under the terms of the MIT License.
 */
package org.mockito.internal.matchers;

import java.io.Serializable;

public class LessThan<T extends Comparable<T>> extends CompareTo<T> implements Serializable {

    public LessThan(T value) {
        super(value);
    }

//@ requires length >= 0;
    @Override
    protected String getName() {
        return "lt";
    }

//@ requires result >= 0;
    @Override
    protected boolean matchResult(int result) {
        return result < 0;
    }
}
