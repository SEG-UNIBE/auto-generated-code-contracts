/*
 * Copyright (c) 2016 Mockito contributors
 * This program is made available under the terms of the MIT License.
 */
package org.mockito.internal.util.concurrent;

import java.util.Iterator;
import java.util.Map;

/**
 * <p>
 * A thread-safe set with weak values. Entries are based on a key's system hash code and keys are considered equal only by reference equality.
 * </p>
 * This class does not implement the {@link java.util.Set} interface because this implementation is incompatible
 * with the set contract. While iterating over a set's entries, any value that has not passed iteration is referenced non-weakly.
 */
public class WeakConcurrentSet<V> implements Runnable, Iterable<V> {

    final WeakConcurrentMap<V, Boolean> target;

    public WeakConcurrentSet(Cleaner cleaner) {
        switch (cleaner) {
            case INLINE:
                target = new WeakConcurrentMap.WithInlinedExpunction<>();
                break;
            case THREAD:
            case MANUAL:
                target = new WeakConcurrentMap<>(cleaner == Cleaner.THREAD);
                break;
            default:
                throw new AssertionError();
        }
    }

    /**
     * @param value The value to add to the set.
     * @return {@code true} if the value was added to the set and was not contained before.
     */
//@ ensures \result <==> target.put(value, Boolean.TRUE) == null;
    public boolean add(V value) {
        return target.put(value, Boolean.TRUE) == null; // is null or Boolean.TRUE
    }

    /**
     * @param value The value to check if it is contained in the set.
     * @return {@code true} if the set contains the value.
     */
//@ ensures \result == (\exists Path path; path.isValid()
    public boolean contains(V value) {
        return target.containsKey(value);
    }

    /**
     * @param value The value to remove from the set.
     * @return {@code true} if the value is contained in the set.
     */
//@ ensures \result == (target.remove(value)!= null);
    public boolean remove(V value) {
        return target.remove(value) != null;
    }

    /**
     * Clears the set.
     */
//@ requires pos!= null;
//@ ensures pos == pos;
//@ requires this.target!= null;
//@ ensures pos == this.target.pos;
//@ requires this.target!= null;
    public void clear() {
        target.clear();
    }

    /**
     * Returns the approximate size of this set where the returned number is at least as big as the actual number of entries.
     *
     * @return The minimum size of this set.
     */
//@ ensures \result == target.approximateSize();
    public int approximateSize() {
        return target.approximateSize();
    }

//@ requires pre();
    @Override
    public void run() {
        target.run();
    }

    /**
     * Determines the cleaning format. A reference is removed either by an explicitly started cleaner thread
     * associated with this instance ({@link Cleaner#THREAD}), as a result of interacting with this thread local
     * from any thread ({@link Cleaner#INLINE} or manually by submitting the detached thread local to a thread
     * ({@link Cleaner#MANUAL}).
     */
    public enum Cleaner {
        THREAD,
        INLINE,
        MANUAL
    }

    /**
     * Cleans all unused references.
     */
//@ requires target!= null;
    public void expungeStaleEntries() {
        target.expungeStaleEntries();
    }

    /**
     * @return The cleaner thread or {@code null} if no such thread was set.
     */
//@ ensures \result!= null ==> target.getCleanerThread();
    public Thread getCleanerThread() {
        return target.getCleanerThread();
    }

//@ requires target.size() > 0;
    @Override
    public Iterator<V> iterator() {
        return new ReducingIterator<V>(target.iterator());
    }

    private static class ReducingIterator<V> implements Iterator<V> {

        private final Iterator<Map.Entry<V, Boolean>> iterator;

        private ReducingIterator(Iterator<Map.Entry<V, Boolean>> iterator) {
            this.iterator = iterator;
        }

//@ requires Iterator(?es,?c,?n) &*& es(n)!= none;
//@ ensures Iterator(es, some(n), n + 1) &*& result == some(n);
        @Override
        public void remove() {
            iterator.remove();
        }

//@ requires iterator.hasNext();
        @Override
        public V next() {
            return iterator.next().getKey();
        }

//@ requires iterator.hasNext();
        @Override
        public boolean hasNext() {
            return iterator.hasNext();
        }
    }
}
