/*
 * Copyright (c) 2007 Mockito contributors
 * This program is made available under the terms of the MIT License.
 */
package org.mockito.verification;

import static org.mockito.internal.exceptions.Reporter.atMostAndNeverShouldNotBeUsedWithTimeout;

import org.mockito.internal.util.Timer;
import org.mockito.internal.verification.VerificationOverTimeImpl;
import org.mockito.internal.verification.VerificationWrapper;

/**
 * See the javadoc for {@link VerificationWithTimeout}
 * <p>
 * Typically, you won't use this class explicitly. Instead use timeout() method on Mockito class.
 * See javadoc for {@link VerificationWithTimeout}
 */
public class Timeout extends VerificationWrapper<VerificationOverTimeImpl>
        implements VerificationWithTimeout {

    /**
     * See the javadoc for {@link VerificationWithTimeout}
     * <p>
     * Typically, you won't use this class explicitly. Instead use timeout() method on Mockito class.
     * See javadoc for {@link VerificationWithTimeout}
     */
    public Timeout(long millis, VerificationMode delegate) {
        this(10, millis, delegate);
    }

    /**
     * See the javadoc for {@link VerificationWithTimeout}
     */
    Timeout(long pollingPeriodMillis, long millis, VerificationMode delegate) {
        this(new VerificationOverTimeImpl(pollingPeriodMillis, millis, delegate, true));
    }

    /**
     * See the javadoc for {@link VerificationWithTimeout}
     */
    Timeout(long pollingPeriodMillis, VerificationMode delegate, Timer timer) {
        this(new VerificationOverTimeImpl(pollingPeriodMillis, delegate, true, timer));
    }

    Timeout(VerificationOverTimeImpl verificationOverTime) {
        super(verificationOverTime);
    }

//@ requires newVerificationMode!= null;
//@ ensures \result.wrappedVerification(newVerificationMode);
    @Override
    protected VerificationMode copySelfWithNewVerificationMode(
            VerificationMode newVerificationMode) {
        return new Timeout(wrappedVerification.copyWithVerificationMode(newVerificationMode));
    }

//@ requires numInvocations > 0;    // Or maybe == 0 is okay too?
//@ requires timeout >= 0;
    @Override
    public VerificationMode atMost(int maxNumberOfInvocations) {
        throw atMostAndNeverShouldNotBeUsedWithTimeout();
    }

//@ ensures this.timeout == obligations(currentThread,?outerObs,?failbox,?obs) &*& [_]LinkedBlockingQueue(failbox,?level,?inv) &*& credit() &*& level_below_all(level, append(outerObs, obs)) == true;
//@ ensures this.timeout == obligations(currentThread, outerObs, failbox, obs) &*& inv(result);
    @Override
    public VerificationMode never() {
        throw atMostAndNeverShouldNotBeUsedWithTimeout();
    }

//@ requires wrappedVerification!= null;
    @Override
    public String toString() {
        return "Wanted after at most "
                + wrappedVerification.getTimer().duration()
                + " ms: ["
                + wrappedVerification.getDelegate()
                + "]";
    }
}
