/*
 * Copyright (c) 2016 Mockito contributors
 * This program is made available under the terms of the MIT License.
 */
package org.mockito.internal.util.concurrent;

/**
 * <p>
 * A detached local that allows for explicit control of setting and removing values from a thread-local
 * context.
 * </p>
 * Instances of this class are non-blocking and fully thread safe.
 */
public class DetachedThreadLocal<T> implements Runnable {

    final WeakConcurrentMap<Thread, T> map;

    public DetachedThreadLocal(Cleaner cleaner) {
        switch (cleaner) {
            case THREAD:
            case MANUAL:
                map =
                        new WeakConcurrentMap<Thread, T>(cleaner == Cleaner.THREAD) {
//@ requires key!= null;
                            @Override
                            protected T defaultValue(Thread key) {
                                return DetachedThreadLocal.this.initialValue(key);
                            }
                        };
                break;
            case INLINE:
                map =
                        new WeakConcurrentMap.WithInlinedExpunction<Thread, T>() {
//@ requires key!= null;
                            @Override
                            protected T defaultValue(Thread key) {
                                return DetachedThreadLocal.this.initialValue(key);
                            }
                        };
                break;
            default:
                throw new AssertionError();
        }
    }

//@ ensures \result!= null ==> map.containsKey(Thread.currentThread());
    public T get() {
        return map.get(Thread.currentThread());
    }

    /**
     * @param thread The thread for which to set a thread-local value.
     * @return The value associated with this thread.
     */
//@ ensures \result!= null ==> map.containsKey(thread);
    public T get(Thread thread) {
        return map.get(thread);
    }

//@ ensures \result == map.get(Thread.currentThread());
    public void set(T value) {
        map.put(Thread.currentThread(), value);
    }

//@ ensures map.size() == 0;
    public void clear() {
        map.remove(Thread.currentThread());
    }

    /**
     * Clears all thread local references for all threads.
     */
//@ ensures map.isEmpty();
    public void clearAll() {
        map.clear();
    }

    /**
     * @param thread The thread to which this thread's thread local value should be pushed.
     * @return The value being set.
     */
//@ requires thread!= null;
//@ ensures map.containsKey(thread) == true;
    public T pushTo(Thread thread) {
        T value = get();
        if (value != null) {
            map.put(thread, inheritValue(value));
        }
        return value;
    }

    /**
     * @param thread The thread from which the thread thread local value should be fetched.
     * @return The value being set.
     */
//@ requires thread!= null;
    public T fetchFrom(Thread thread) {
        T value = map.get(thread);
        if (value != null) {
            set(inheritValue(value));
        }
        return value;
    }

    /**
     * @param thread The thread for which to set a thread-local value.
     * @param value The value to set.
     */
//@ ensures thread == thread && value == thread.getValue();
    public void define(Thread thread, T value) {
        map.put(thread, value);
    }

    /**
     * @param thread The thread for which an initial value is created.
     * @return The initial value for any thread local. If no default is set, the default value is {@code null}.
     */
//@ ensures \result == null;
    protected T initialValue(Thread thread) {
        return null;
    }

    /**
     * @param value The value that is inherited.
     * @return The inherited value.
     */
//@ ensures \result == value;
    protected T inheritValue(T value) {
        return value;
    }

    /**
     * @return The weak map that backs this detached thread local.
     */
//@ ensures \result == map;
    public WeakConcurrentMap<Thread, T> getBackingMap() {
        return map;
    }

//@ requires pre();
    @Override
    public void run() {
        map.run();
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
}
