/*
 * Copyright (c) 2016 Mockito contributors
 * This program is made available under the terms of the MIT License.
 */
package org.mockito.internal.verification;

import org.mockito.internal.verification.api.VerificationData;
import org.mockito.verification.VerificationMode;

public abstract class VerificationWrapper<WrapperT extends VerificationMode>
        implements VerificationMode {

    protected final WrapperT wrappedVerification;

    public VerificationWrapper(WrapperT wrappedVerification) {
        this.wrappedVerification = wrappedVerification;
    }

//@ requires data!= null
    @Override
    public void verify(VerificationData data) {
        wrappedVerification.verify(data);
    }

    protected abstract VerificationMode copySelfWithNewVerificationMode(
            VerificationMode verificationMode);

//@ requires wantedNumberOfInvocations >= 0;
    public VerificationMode times(int wantedNumberOfInvocations) {
        return copySelfWithNewVerificationMode(
                VerificationModeFactory.times(wantedNumberOfInvocations));
    }

//@ ensures \result!= null;
    public VerificationMode never() {
        return copySelfWithNewVerificationMode(VerificationModeFactory.atMost(0));
    }

//@ ensures \result == copySelfWithNewVerificationMode(VerificationModeFactory.atLeastOnce());
    public VerificationMode atLeastOnce() {
        return copySelfWithNewVerificationMode(VerificationModeFactory.atLeastOnce());
    }

//@ requires numInvocations >= 0;
    public VerificationMode atLeast(int minNumberOfInvocations) {
        return copySelfWithNewVerificationMode(
                VerificationModeFactory.atLeast(minNumberOfInvocations));
    }

//@ ensures \result == copySelfWithNewVerificationMode(VerificationModeFactory.atMostOnce());
    public VerificationMode atMostOnce() {
        return copySelfWithNewVerificationMode(VerificationModeFactory.atMostOnce());
    }

//@ requires maxNumberOfInvocations >= 0;
    public VerificationMode atMost(int maxNumberOfInvocations) {
        return copySelfWithNewVerificationMode(
                VerificationModeFactory.atMost(maxNumberOfInvocations));
    }

//@ ensures \result == copySelfWithNewVerificationMode(VerificationModeFactory.only());
    public VerificationMode only() {
        return copySelfWithNewVerificationMode(VerificationModeFactory.only());
    }
}
