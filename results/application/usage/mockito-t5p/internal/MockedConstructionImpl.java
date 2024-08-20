/*
 * Copyright (c) 2007 Mockito contributors
 * This program is made available under the terms of the MIT License.
 */
package org.mockito.internal;

import static org.mockito.internal.util.StringUtil.join;

import java.util.Collections;
import java.util.List;

import org.mockito.MockedConstruction;
import org.mockito.exceptions.base.MockitoException;
import org.mockito.internal.debugging.LocationFactory;
import org.mockito.invocation.Location;
import org.mockito.plugins.MockMaker;

public final class MockedConstructionImpl<T> implements MockedConstruction<T> {

    private final MockMaker.ConstructionMockControl<T> control;

    private boolean closed;

    private final Location location = LocationFactory.create();

    protected MockedConstructionImpl(MockMaker.ConstructionMockControl<T> control) {
        this.control = control;
    }

//@ ensures \result == null || \result.size() == 0;
    @Override
    public List<T> constructed() {
        return Collections.unmodifiableList(control.getMocks());
    }

//@ ensures \result == closed;
    @Override
    public boolean isClosed() {
        return closed;
    }

//@ ensures closed == true;
    @Override
    public void close() {
        assertNotClosed();

        closed = true;
        control.disable();
    }

//@ requires isOpen;
//@ ensures!isOpen;
    @Override
    public void closeOnDemand() {
        if (!closed) {
            close();
        }
    }

//@ requires closed;
    private void assertNotClosed() {
        if (closed) {
            throw new MockitoException(
                    join(
                            "The static mock created at",
                            location.toString(),
                            "is already resolved and cannot longer be used"));
        }
    }
}
