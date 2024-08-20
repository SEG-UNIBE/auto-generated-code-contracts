/*
 * Copyright (c) 2007 Mockito contributors
 * This program is made available under the terms of the MIT License.
 */
package org.mockito.internal.verification.checkers;

import static org.mockito.internal.exceptions.Reporter.neverWantedButInvoked;
import static org.mockito.internal.exceptions.Reporter.tooFewActualInvocations;
import static org.mockito.internal.exceptions.Reporter.tooFewActualInvocationsInOrder;
import static org.mockito.internal.exceptions.Reporter.tooManyActualInvocations;
import static org.mockito.internal.exceptions.Reporter.tooManyActualInvocationsInOrder;
import static org.mockito.internal.invocation.InvocationMarker.markVerified;
import static org.mockito.internal.invocation.InvocationMarker.markVerifiedInOrder;
import static org.mockito.internal.invocation.InvocationsFinder.findFirstMatchingUnverifiedInvocation;
import static org.mockito.internal.invocation.InvocationsFinder.findInvocations;
import static org.mockito.internal.invocation.InvocationsFinder.findMatchingChunk;
import static org.mockito.internal.invocation.InvocationsFinder.getAllLocations;

import java.util.Arrays;
import java.util.List;

import org.mockito.internal.reporting.Discrepancy;
import org.mockito.internal.verification.api.InOrderContext;
import org.mockito.invocation.Invocation;
import org.mockito.invocation.Location;
import org.mockito.invocation.MatchableInvocation;

public class NumberOfInvocationsChecker {

    private NumberOfInvocationsChecker() {}

//@ requires invocations!= null && wanted!= null;
//@ requires 0 <= wantedCount && wantedCount < invocations.size();
    public static void checkNumberOfInvocations(
            List<Invocation> invocations, MatchableInvocation wanted, int wantedCount) {
        List<Invocation> actualInvocations = findInvocations(invocations, wanted);

        int actualCount = actualInvocations.size();
        if (wantedCount > actualCount) {
            List<Location> allLocations = getAllLocations(actualInvocations);
            throw tooFewActualInvocations(
                    new Discrepancy(wantedCount, actualCount), wanted, allLocations);
        }
        if (wantedCount == 0 && actualCount > 0) {
            throw neverWantedButInvoked(wanted, actualInvocations);
        }
        if (wantedCount < actualCount) {
            throw tooManyActualInvocations(
                    wantedCount, actualCount, wanted, getAllLocations(actualInvocations));
        }

        markVerified(actualInvocations, wanted);
    }

//@ requires invocations!= null && wanted!= null && wantedCount >= 0;
//@ requires context!= null;
    public static void checkNumberOfInvocations(
            List<Invocation> invocations,
            MatchableInvocation wanted,
            int wantedCount,
            InOrderContext context) {
        List<Invocation> chunk = findMatchingChunk(invocations, wanted, wantedCount, context);

        int actualCount = chunk.size();

        if (wantedCount > actualCount) {
            List<Location> allLocations = getAllLocations(chunk);
            throw tooFewActualInvocationsInOrder(
                    new Discrepancy(wantedCount, actualCount), wanted, allLocations);
        }
        if (wantedCount < actualCount) {
            throw tooManyActualInvocationsInOrder(
                    wantedCount, actualCount, wanted, getAllLocations(chunk));
        }

        markVerifiedInOrder(chunk, wanted, context);
    }

//@ requires invocations!= null;
//@ requires wanted!= null;
//@ requires wantedCount >= 0;
//@ requires actualCount >= 0;
//@ requires lastLocation!= null;
//@ ensures invocations!= null;
//@ ensures wanted!= null;
//@ ensures actualCount == wantedCount;
//@ ensures lastLocation == lastLocation;
    public static void checkNumberOfInvocationsNonGreedy(
            List<Invocation> invocations,
            MatchableInvocation wanted,
            int wantedCount,
            InOrderContext context) {
        int actualCount = 0;
        Location lastLocation = null;
        while (actualCount < wantedCount) {
            Invocation next = findFirstMatchingUnverifiedInvocation(invocations, wanted, context);
            if (next == null) {
                throw tooFewActualInvocationsInOrder(
                        new Discrepancy(wantedCount, actualCount),
                        wanted,
                        Arrays.asList(lastLocation));
            }
            markVerified(next, wanted);
            context.markVerified(next);
            lastLocation = next.getLocation();
            actualCount++;
        }
    }
}
