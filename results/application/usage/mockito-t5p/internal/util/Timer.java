/*
 * Copyright (c) 2016 Mockito contributors
 * This program is made available under the terms of the MIT License.
 */
package org.mockito.internal.util;

import static org.mockito.internal.exceptions.Reporter.cannotCreateTimerWithNegativeDurationTime;

public class Timer {

    private final long durationMillis;
    private long startTime = -1;

    public Timer(long durationMillis) {
        validateInput(durationMillis);
        this.durationMillis = durationMillis;
    }

    /**
     * Informs whether the timer is still counting down.
     */
//@ requires startTime!= -1;
//@ requires durationMillis > 0;
    public boolean isCounting() {
        assert startTime != -1;
        return System.currentTimeMillis() - startTime <= durationMillis;
    }

    /**
     * Starts the timer count down.
     */
//@ ensures startTime == 0;
    public void start() {
        startTime = System.currentTimeMillis();
    }

//@ requires durationMillis >= 0;
    private void validateInput(long durationMillis) {
        if (durationMillis < 0) {
            throw cannotCreateTimerWithNegativeDurationTime(durationMillis);
        }
    }

//@ ensures \result == durationMillis;
    public long duration() {
        return durationMillis;
    }
}
