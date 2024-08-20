/*
 * Copyright (c) 2007 Mockito contributors
 * This program is made available under the terms of the MIT License.
 */
package org.mockito.internal.matchers;

import java.io.Serializable;

import org.mockito.ArgumentMatcher;

public class Contains implements ArgumentMatcher<String>, Serializable {

    private final String substring;

    public Contains(String substring) {
        this.substring = substring;
    }

//@ requires length > 0;
    @Override
    public boolean matches(String actual) {
        return actual != null && actual.contains(substring);
    }

//@ requires substring!= null;
    @Override
    public String toString() {
        return "contains(\"" + substring + "\")";
    }
}
