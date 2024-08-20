/*
 * Copyright (c) 2016 Mockito contributors
 * This program is made available under the terms of the MIT License.
 */
package org.mockito.internal.junit;

/**
 * Stubbing hint emitted to the user
 */
class StubbingHint {

    private final StringBuilder hint;

    StubbingHint(String testName) {
        hint =
                new StringBuilder("[MockitoHint] ")
                        .append(testName)
                        .append(" (see javadoc for MockitoHint):");
    }

//@ requires elements!= null;
//@ ensures hint.length() > 0;
    void appendLine(Object... elements) {
        hint.append("\n[MockitoHint] ");
        for (Object e : elements) {
            hint.append(e);
        }
    }

//@ ensures \result!= null;
    @Override
    public String toString() {
        return hint + "\n";
    }
}
