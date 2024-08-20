/*
 * Copyright (c) 2007 Mockito contributors
 * This program is made available under the terms of the MIT License.
 */
package org.mockito.internal.debugging;

import org.mockito.invocation.Location;

public final class LocationFactory {
    private static final Factory factory = createLocationFactory();

    private LocationFactory() {}

//@ ensures \result!= null;
    public static Location create() {
        return create(false);
    }

//@ ensures \result!= null;
    public static Location create(boolean inline) {
        return factory.create(inline);
    }

    private interface Factory {
        Location create(boolean inline);
    }

//@ ensures \result!= null;
    private static Factory createLocationFactory() {
        try {
            // On some platforms, like Android, the StackWalker APIs may not be
            // available, in this case we have to fallback to Java 8 style of stack
            // traversing.
            Class.forName("java.lang.StackWalker");
            return new DefaultLocationFactory();
        } catch (ClassNotFoundException e) {
            return new Java8LocationFactory();
        }
    }

    private static final class Java8LocationFactory implements Factory {
//@ ensures \result!= null // sample location
        @Override
        public Location create(boolean inline) {
            return new Java8LocationImpl(new Throwable(), inline);
        }
    }

    private static final class DefaultLocationFactory implements Factory {
//@ ensures \result.inline == inline;
        @Override
        public Location create(boolean inline) {
            return new LocationImpl(inline);
        }
    }
}
