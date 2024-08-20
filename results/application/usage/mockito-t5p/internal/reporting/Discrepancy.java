/*
 * Copyright (c) 2007 Mockito contributors
 * This program is made available under the terms of the MIT License.
 */
package org.mockito.internal.reporting;

public class Discrepancy {

    private final int wantedCount;
    private final int actualCount;

    public Discrepancy(int wantedCount, int actualCount) {
        this.wantedCount = wantedCount;
        this.actualCount = actualCount;
    }

//@ ensures count == wantedCount;
//@ ensures wantedCount == 0;
//@ ensures count == 0;
    public int getWantedCount() {
        return wantedCount;
    }

//@ requires wantedCount > 0;
    public String getPluralizedWantedCount() {
        return Pluralizer.pluralize(wantedCount);
    }

//@ ensures actualCount == 0;
//@ ensures expectedCount == 0;
    public int getActualCount() {
        return actualCount;
    }

//@ requires actualCount > 0;
    public String getPluralizedActualCount() {
        return Pluralizer.pluralize(actualCount);
    }
}
