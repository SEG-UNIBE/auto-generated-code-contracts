/*
 * Copyright (c) 2007 Mockito contributors
 * This program is made available under the terms of the MIT License.
 */
package org.mockito.internal.verification;

import org.mockito.verification.VerificationMode;

public final class VerificationModeFactory {

//@ ensures \result == atLeast(1);
    public static VerificationMode atLeastOnce() {
        return atLeast(1);
    }

//@ requires minNumberOfInvocations >= 0;
    public static VerificationMode atLeast(int minNumberOfInvocations) {
        return new AtLeast(minNumberOfInvocations);
    }

//@ ensures \result!= null;
    public static VerificationMode only() {
        return new Only(); // TODO make exception message nicer
    }

//@ requires wantedNumberOfInvocations >= 0;
    public static Times times(int wantedNumberOfInvocations) {
        return new Times(wantedNumberOfInvocations);
    }

//@ requires wantedNumberOfInvocations >= 0;
    public static Calls calls(int wantedNumberOfInvocations) {
        return new Calls(wantedNumberOfInvocations);
    }

//@ ensures \result!= null;
    public static NoMoreInteractions noMoreInteractions() {
        return new NoMoreInteractions();
    }

//@ ensures \result!= null;
    public static NoInteractions noInteractions() {
        return new NoInteractions();
    }

//@ ensures \result == atMost(1);
    public static VerificationMode atMostOnce() {
        return atMost(1);
    }

//@ requires maxNumberOfInvocations >= 0;
    public static VerificationMode atMost(int maxNumberOfInvocations) {
        return new AtMost(maxNumberOfInvocations);
    }

    /**
     * Verification mode will prepend the specified failure message if verification fails with the given implementation.
     * @param mode Implementation used for verification
     * @param description The custom failure message
     * @return VerificationMode
     * @since 2.1.0
     */
//@ ensures \result!= null;
//@ ensures \result.description().equals(description);
    public static VerificationMode description(VerificationMode mode, String description) {
        return new Description(mode, description);
    }

    private VerificationModeFactory() {}
}
