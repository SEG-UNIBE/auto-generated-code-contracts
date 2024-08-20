/*
 * Copyright (c) 2007 Mockito contributors
 * This program is made available under the terms of the MIT License.
 */
package org.mockito.internal.matchers;

import java.io.Serializable;

public class CompareEqual<T extends Comparable<T>> extends CompareTo<T> implements Serializable {

    public CompareEqual(T value) {
        super(value);
    }

//@ requires true;
    @Override
    protected String getName() {
        return "cmpEq";
    }

//@ requires result == 0;
    @Override
    protected boolean matchResult(int result) {
        return result == 0;
    }
}
