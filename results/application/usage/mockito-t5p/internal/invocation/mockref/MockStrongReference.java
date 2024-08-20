/*
 * Copyright (c) 2018 Mockito contributors
 * This program is made available under the terms of the MIT License.
 */
package org.mockito.internal.invocation.mockref;

import java.io.ObjectStreamException;

public class MockStrongReference<T> implements MockReference<T> {

    private final T ref;
    private final boolean deserializeAsWeakRef;

    public MockStrongReference(T ref, boolean deserializeAsWeakRef) {
        this.ref = ref;
        this.deserializeAsWeakRef = deserializeAsWeakRef;
    }

//@ requires ref!= null;
    @Override
    public T get() {
        return ref;
    }

//@ requires ref!= null;
    private Object readResolve() throws ObjectStreamException {
        if (deserializeAsWeakRef) {
            return new MockWeakReference<T>(ref);
        } else {
            return this;
        }
    }
}
