/*
 * Copyright (c) 2007 Mockito contributors
 * This program is made available under the terms of the MIT License.
 */
package org.mockito.internal.invocation;

import java.util.LinkedList;
import java.util.List;
import java.util.stream.Collectors;

import org.mockito.internal.verification.api.InOrderContext;
import org.mockito.invocation.Invocation;
import org.mockito.invocation.Location;
import org.mockito.invocation.MatchableInvocation;

public class InvocationsFinder {

    private InvocationsFinder() {}

//@ requires invocations!= null && wanted!= null;
    public static List<Invocation> findInvocations(
            List<Invocation> invocations, MatchableInvocation wanted) {
        return invocations.stream().filter(wanted::matches).collect(Collectors.toList());
    }

//@ requires invocations!= null && wanted!= null;
    public static List<Invocation> findAllMatchingUnverifiedChunks(
            List<Invocation> invocations,
            MatchableInvocation wanted,
            InOrderContext orderingContext) {
        List<Invocation> unverified = removeVerifiedInOrder(invocations, orderingContext);
        return unverified.stream().filter(wanted::matches).collect(Collectors.toList());
    }

    /**
     * some examples how it works:
     *
     * Given invocations sequence:
     * 1,1,2,1
     *
     * if wanted is 1 and mode is times(2) then returns
     * 1,1
     *
     * if wanted is 1 and mode is atLeast() then returns
     * 1,1,1
     *
     * if wanted is 1 and mode is times(x), where x != 2 then returns
     * 1,1,1
     */
//@ requires invocations!= null && wanted!= null && wantedCount >= 0;
    public static List<Invocation> findMatchingChunk(
            List<Invocation> invocations,
            MatchableInvocation wanted,
            int wantedCount,
            InOrderContext context) {
        List<Invocation> unverified = removeVerifiedInOrder(invocations, context);
        List<Invocation> firstChunk = getFirstMatchingChunk(wanted, unverified);

        if (wantedCount != firstChunk.size()) {
            return findAllMatchingUnverifiedChunks(invocations, wanted, context);
        } else {
            return firstChunk;
        }
    }

//@ requires wanted!= null && unverified!= null;
    private static List<Invocation> getFirstMatchingChunk(
            MatchableInvocation wanted, List<Invocation> unverified) {
        List<Invocation> firstChunk = new LinkedList<>();
        for (Invocation invocation : unverified) {
            if (wanted.matches(invocation)) {
                firstChunk.add(invocation);
            } else if (!firstChunk.isEmpty()) {
                break;
            }
        }
        return firstChunk;
    }

//@ requires invocations!= null && wanted!= null;
    public static Invocation findFirstMatchingUnverifiedInvocation(
            List<Invocation> invocations, MatchableInvocation wanted, InOrderContext context) {
        for (Invocation invocation : removeVerifiedInOrder(invocations, context)) {
            if (wanted.matches(invocation)) {
                return invocation;
            }
        }
        return null;
    }

//@ requires invocations!= null && wanted!= null;
    public static Invocation findSimilarInvocation(
            List<Invocation> invocations, MatchableInvocation wanted) {
        Invocation firstSimilar = null;
        for (Invocation invocation : invocations) {
            if (!wanted.hasSimilarMethod(invocation)) {
                continue;
            }
            if (firstSimilar == null) {
                firstSimilar = invocation;
            }
            if (wanted.hasSameMethod(invocation)) {
                return invocation;
            }
        }

        return firstSimilar;
    }

//@ requires invocations!= null;
//@ requires (\forall int i; 0 <= i && i < invocations.size(); Invocation_desugared$1(invocations.get(i), null));
    public static Invocation findFirstUnverified(List<Invocation> invocations) {
        return findFirstUnverified(invocations, null);
    }

//@ requires invocations!= null;
//@ requires mock!= null;
    static Invocation findFirstUnverified(List<Invocation> invocations, Object mock) {
        for (Invocation i : invocations) {
            boolean mockIsValid = mock == null || mock == i.getMock();
            if (!i.isVerified() && mockIsValid) {
                return i;
            }
        }
        return null;
    }

//@ requires invocations!= null;
//@ requires \nonnullelements(invocations);
    public static Location getLastLocation(List<Invocation> invocations) {
        if (invocations.isEmpty()) {
            return null;
        } else {
            Invocation last = invocations.get(invocations.size() - 1);
            return last.getLocation();
        }
    }

//@ requires invocations.size() > 0;
    public static Invocation findPreviousVerifiedInOrder(
            List<Invocation> invocations, InOrderContext context) {
        List<Invocation> verifiedOnly =
                invocations.stream().filter(context::isVerified).collect(Collectors.toList());

        if (verifiedOnly.isEmpty()) {
            return null;
        } else {
            return verifiedOnly.get(verifiedOnly.size() - 1);
        }
    }

//@ requires invocations.size() > 0
//@ requires orderingContext!= null;
    private static List<Invocation> removeVerifiedInOrder(
            List<Invocation> invocations, InOrderContext orderingContext) {
        List<Invocation> unverified = new LinkedList<>();
        for (Invocation i : invocations) {
            if (orderingContext.isVerified(i)) {
                unverified.clear();
            } else {
                unverified.add(i);
            }
        }
        return unverified;
    }

//@ requires invocations!= null;
//@ requires \nonnullelements(invocations);
    public static List<Location> getAllLocations(List<Invocation> invocations) {
        List<Location> locations = new LinkedList<>();
        for (Invocation invocation : invocations) {
            locations.add(invocation.getLocation());
        }
        return locations;
    }

    /**
     * i3 is unverified here:
     *
     * i1, i2, i3
     *     v
     *
     * all good here:
     *
     * i1, i2, i3
     *     v   v
     *
     * @param context
     * @param orderedInvocations
     */
//@ requires orderedInvocations.size() > 0;
    public static Invocation findFirstUnverifiedInOrder(
            InOrderContext context, List<Invocation> orderedInvocations) {
        Invocation candidate = null;
        for (Invocation i : orderedInvocations) {
            if (!context.isVerified(i)) {
                candidate = candidate != null ? candidate : i;
            } else {
                candidate = null;
            }
        }
        return candidate;
    }
}
