/*
 * Copyright (c) 2007 Mockito contributors
 * This program is made available under the terms of the MIT License.
 */
package org.mockito.internal.verification;

import java.io.Serializable;
import java.util.Collections;
import java.util.List;

import org.mockito.invocation.Invocation;

public class SingleRegisteredInvocation implements RegisteredInvocations, Serializable {

    private Invocation invocation;

//@ requires invocation!= null;
    @Override
    public void add(Invocation invocation) {
        this.invocation = invocation;
    }

//@ requires last()!= null;
    @Override
    public void removeLast() {
        invocation = null;
    }

//@ ensures \result == null || \result.size() == 0;
    @Override
    public List<Invocation> getAll() {
        return Collections.emptyList();
    }

//@ requires current_applet(this) &*& [1/2]valid();
//@ ensures current_applet(this) &*& [1/2]valid();
    @Override
    public void clear() {
        invocation = null;
    }

//@ ensures \result <==> invocation == null;
    @Override
    public boolean isEmpty() {
        return invocation == null;
    }
}
