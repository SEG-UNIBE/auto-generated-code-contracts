/*
 * Copyright (c) 2016 Mockito contributors
 * This program is made available under the terms of the MIT License.
 */
package org.mockito.internal.exceptions.stacktrace;

import org.mockito.exceptions.stacktrace.StackTraceCleaner;

/**
 * This predicate is used to filter "good" {@link StackTraceElement}. Good
 */
public class DefaultStackTraceCleaner implements StackTraceCleaner {

//@ ensures \result == isIn(e.getClassName());
    @Override
    public boolean isIn(StackTraceElement e) {
        return isIn(e.getClassName());
    }

//@ ensures \result == (e.getClassName()!= null);
    @Override
    public boolean isIn(StackFrameMetadata e) {
        return isIn(e.getClassName());
    }

//@ ensures \result == (className!= null);
    private boolean isIn(String className) {
        if (isFromMockitoRunner(className) || isFromMockitoRule(className)) {
            return true;
        } else if (isMockDispatcher(className)
                || isFromMockito(className)
                || isMethodHandle(className)) {
            return false;
        } else {
            return true;
        }
    }

    /* Some mock makers (like inline) use java.lang.invoke.MethodHandle to dispatch calls */
//@ ensures \result == className.startsWith("java.lang.invoke.MethodHandle");
    private static boolean isMethodHandle(String className) {
        return className.startsWith("java.lang.invoke.MethodHandle");
    }

//@ ensures \result <==> (className.contains("$$EnhancerByMockitoWithCGLIB$$") || className.contains("$MockitoMock$"));
    private static boolean isMockDispatcher(String className) {
        return (className.contains("$$EnhancerByMockitoWithCGLIB$$")
                || className.contains("$MockitoMock$"));
    }

//@ ensures \result == className.startsWith("org.mockito.");
    private static boolean isFromMockito(String className) {
        return className.startsWith("org.mockito.");
    }

//@ ensures \result == className.startsWith("org.mockito.internal.junit.JUnitRule");
    private static boolean isFromMockitoRule(String className) {
        return className.startsWith("org.mockito.internal.junit.JUnitRule");
    }

//@ ensures \result <==> className.startsWith("org.mockito.internal.runners.");
//@ ensures \result <==> className.startsWith("org.mockito.runners.");
//@ ensures \result <==> className.startsWith("org.mockito.junit.");
    private static boolean isFromMockitoRunner(String className) {
        return className.startsWith("org.mockito.internal.runners.")
                || className.startsWith("org.mockito.runners.")
                || className.startsWith("org.mockito.junit.");
    }
}
