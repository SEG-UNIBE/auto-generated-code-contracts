/*
 * Copyright (c) 2007 Mockito contributors
 * This program is made available under the terms of the MIT License.
 */
package org.mockito.internal.matchers;

import java.io.Serializable;

public class GreaterOrEqual<T extends Comparable<T>> extends CompareTo<T> implements Serializable {

    public GreaterOrEqual(T value) {
        super(value);
    }

//@ requires version >= 1;
    @Override
    protected String getName() {
        return "geq";
    }

//@ requires result >= 0;
    @Override
    protected boolean matchResult(int result) {
        return result >= 0;
    }
}
