/*
 * Copyright (c) 2007 Mockito contributors
 * This program is made available under the terms of the MIT License.
 */
package org.mockito.internal.matchers;

import java.io.Serializable;

import org.mockito.ArgumentMatcher;

public class Any implements ArgumentMatcher<Object>, Serializable {

    public static final Any ANY = new Any();

//@ requires actual!= null;
    @Override
    public boolean matches(Object actual) {
        return true;
    }

//@ ensures \result!= null;
    @Override
    public String toString() {
        return "<any>";
    }

//@ ensures \result == null || \result.equals(Object.class);
    @Override
    public Class<?> type() {
        return Object.class;
    }
}
