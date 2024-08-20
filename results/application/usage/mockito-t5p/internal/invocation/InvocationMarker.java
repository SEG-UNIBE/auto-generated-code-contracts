/*
 * Copyright (c) 2007 Mockito contributors
 * This program is made available under the terms of the MIT License.
 */
package org.mockito.internal.invocation;

import java.util.List;

import org.mockito.internal.verification.api.InOrderContext;
import org.mockito.invocation.Invocation;
import org.mockito.invocation.MatchableInvocation;

public class InvocationMarker {

    private InvocationMarker() {}

//@ requires invocations!= null && wanted!= null;
//@ requires \nonnullelements(invocations);
    public static void markVerified(List<Invocation> invocations, MatchableInvocation wanted) {
        for (Invocation invocation : invocations) {
            markVerified(invocation, wanted);
        }
    }

//@ requires invocation!= null && wanted!= null;
    public static void markVerified(Invocation invocation, MatchableInvocation wanted) {
        invocation.markVerified();
        wanted.captureArgumentsFrom(invocation);
    }

//@ requires chunk!= null && wanted!= null;
//@ requires context!= null;
    public static void markVerifiedInOrder(
            List<Invocation> chunk, MatchableInvocation wanted, InOrderContext context) {
        markVerified(chunk, wanted);

        for (Invocation i : chunk) {
            context.markVerified(i);
        }
    }
}
