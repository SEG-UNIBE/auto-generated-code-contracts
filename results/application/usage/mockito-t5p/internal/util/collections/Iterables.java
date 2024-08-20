/*
 * Copyright (c) 2016 Mockito contributors
 * This program is made available under the terms of the MIT License.
 */
package org.mockito.internal.util.collections;

import java.util.ArrayList;
import java.util.Enumeration;
import java.util.Iterator;
import java.util.List;

/** Utilities for Iterables */
public final class Iterables {

    /**
     * Converts enumeration into iterable
     */
//@ requires in!= null;
//@ ensures \fresh(\result);
    public static <T> Iterable<T> toIterable(Enumeration<T> in) {
        List<T> out = new ArrayList<T>();
        while (in.hasMoreElements()) {
            out.add(in.nextElement());
        }
        return out;
    }

    /**
     * Returns first element of provided iterable or fails fast when iterable is empty.
     *
     * @param iterable non-empty iterable
     * @return first element of supplied iterable
     * @throws IllegalArgumentException when supplied iterable is empty
     */
//@ requires iterable.size() > 0;
    public static <T> T firstOf(Iterable<T> iterable) {
        Iterator<T> iterator = iterable.iterator();
        if (!iterator.hasNext()) {
            throw new IllegalArgumentException(
                    "Cannot provide 1st element from empty iterable: " + iterable);
        }
        return iterator.next();
    }

    private Iterables() {}
}