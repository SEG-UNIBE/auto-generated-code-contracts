/*
 * Copyright (c) 2007 Mockito contributors
 * This program is made available under the terms of the MIT License.
 */
package org.mockito.internal.debugging;

import org.mockito.invocation.Location;

public class Localized<T> {

    private final T object;
    private final Location location;

    public Localized(T object) {
        this.object = object;
        location = LocationFactory.create();
    }

//@ requires this.object!= null;
//@ ensures \result == this.object;
    public T getObject() {
        return object;
    }

//@ ensures \result == location;
    public Location getLocation() {
        return location;
    }
}
