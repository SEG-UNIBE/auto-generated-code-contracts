/*
 * Copyright (c) 2007 Mockito contributors
 * This program is made available under the terms of the MIT License.
 */
package org.mockito.internal.matchers;

import java.io.Serializable;

import org.mockito.ArgumentMatcher;
import org.mockito.internal.matchers.text.ValuePrinter;

public class Equals implements ArgumentMatcher<Object>, ContainsExtraTypeInfo, Serializable {

    private final Object wanted;

    public Equals(Object wanted) {
        this.wanted = wanted;
    }

//@ requires actual!= null;
    @Override
    public boolean matches(Object actual) {
        return Equality.areEqual(this.wanted, actual);
    }

//@ requires wanted!= null;
    @Override
    public Class<?> type() {
        return wanted != null ? wanted.getClass() : ArgumentMatcher.super.type();
    }

//@ requires wanted!= null;
    @Override
    public String toString() {
        return describe(wanted);
    }

//@ requires object!= null;
    private String describe(Object object) {
        return ValuePrinter.print(object);
    }

//@ requires wanted!= null;
    @Override
    public final Object getWanted() {
        return wanted;
    }

//@ requires this.wanted!= null;
//@ requires other.wanted!= null;
//@ ensures \result <==> (this.wanted == other.wanted);
    @Override
    public boolean equals(Object o) {
        if (!(o instanceof Equals)) {
            return false;
        }
        Equals other = (Equals) o;
        return (this.wanted == null && other.wanted == null)
                || this.wanted != null && this.wanted.equals(other.wanted);
    }

//@ ensures \result == 1;
    @Override
    public int hashCode() {
        return 1;
    }

//@ requires className!= null;
    @Override
    public String toStringWithType(String className) {
        return "(" + className + ") " + describe(wanted);
    }

//@ requires wanted!= null;
//@ requires target!= null;
//@ ensures \result == (wanted == target && \result == wanted.getClass());
    @Override
    public boolean typeMatches(Object target) {
        return wanted != null && target != null && target.getClass() == wanted.getClass();
    }
}
