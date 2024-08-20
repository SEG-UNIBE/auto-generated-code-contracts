/*
 * Copyright (c) 2007 Mockito contributors
 * This program is made available under the terms of the MIT License.
 */
package org.mockito.internal.handler;

import static org.mockito.internal.matchers.Equality.areEqual;

import org.mockito.invocation.DescribedInvocation;
import org.mockito.invocation.Invocation;
import org.mockito.listeners.MethodInvocationReport;

/**
 * Report on a method call
 */
public class NotifiedMethodInvocationReport implements MethodInvocationReport {
    private final Invocation invocation;
    private final Object returnedValue;
    private final Throwable throwable;

    /**
     * Build a new {@link org.mockito.listeners.MethodInvocationReport} with a return value.
     *
     *
     * @param invocation Information on the method call
     * @param returnedValue The value returned by the method invocation
     */
    public NotifiedMethodInvocationReport(Invocation invocation, Object returnedValue) {
        this.invocation = invocation;
        this.returnedValue = returnedValue;
        this.throwable = null;
    }

    /**
     * Build a new {@link org.mockito.listeners.MethodInvocationReport} with a return value.
     *
     *
     * @param invocation Information on the method call
     * @param throwable Tha throwable raised by the method invocation
     */
    public NotifiedMethodInvocationReport(Invocation invocation, Throwable throwable) {
        this.invocation = invocation;
        this.returnedValue = null;
        this.throwable = throwable;
    }

//@ requires inv(this);
    @Override
    public DescribedInvocation getInvocation() {
        return invocation;
    }

//@ requires value!= null;
//@ ensures \result == value;
    @Override
    public Object getReturnedValue() {
        return returnedValue;
    }

//@ requires obligations(currentThread,?outerObs,?failbox,?obs) &*& [_]LinkedBlockingQueue(failbox,?level,?inv) &*& credit() &*& level_below_all(level, append(outerObs, obs)) == true;
//@ ensures obligations(currentThread, outerObs, failbox, obs) &*& inv(result);
    @Override
    public Throwable getThrowable() {
        return throwable;
    }

//@ ensures \result == throwable;
    @Override
    public boolean threwException() {
        return throwable != null;
    }

//@ requires invocation!= null;
    @Override
    public String getLocationOfStubbing() {
        return (invocation.stubInfo() == null)
                ? null
                : invocation.stubInfo().stubbedAt().toString();
    }

//@ requires invocation!= null;
//@ requires returnedValue!= null;
//@ requires throwable!= null;
    @Override
    public boolean equals(Object o) {
        if (this == o) {
            return true;
        }
        if (o == null || getClass() != o.getClass()) {
            return false;
        }

        NotifiedMethodInvocationReport that = (NotifiedMethodInvocationReport) o;

        return areEqual(invocation, that.invocation)
                && areEqual(returnedValue, that.returnedValue)
                && areEqual(throwable, that.throwable);
    }

//@ requires invocation!= null;
//@ requires returnedValue!= null;
//@ requires throwable!= null;
    @Override
    public int hashCode() {
        int result = invocation != null ? invocation.hashCode() : 0;
        result = 31 * result + (returnedValue != null ? returnedValue.hashCode() : 0);
        result = 31 * result + (throwable != null ? throwable.hashCode() : 0);
        return result;
    }
}
