/*
 * Copyright (c) 2007 Mockito contributors
 * This program is made available under the terms of the MIT License.
 */
package org.mockito.internal.debugging;

import org.mockito.exceptions.base.MockitoException;
import org.mockito.exceptions.stacktrace.StackTraceCleaner;
import org.mockito.exceptions.stacktrace.StackTraceCleaner.StackFrameMetadata;
import org.mockito.internal.configuration.plugins.Plugins;
import org.mockito.internal.exceptions.stacktrace.DefaultStackTraceCleaner;
import org.mockito.invocation.Location;

import java.io.Serializable;
import java.lang.StackWalker.Option;
import java.lang.StackWalker.StackFrame;
import java.util.Collections;
import java.util.List;
import java.util.function.Function;
import java.util.function.Predicate;
import java.util.stream.Collectors;
import java.util.stream.Stream;

class LocationImpl implements Location, Serializable {
    private static final long serialVersionUID = 2954388321980069195L;

    private static final String UNEXPECTED_ERROR_SUFFIX =
            "\nThis is unexpected and is likely due to a change in either Java's StackWalker or Reflection APIs."
                    + "\nIt's worth trying to upgrade to a newer version of Mockito, or otherwise to file a bug report.";

    /**
     * This is an unfortunate buffer. Inside StackWalker, a buffer is created, which is resized by
     * doubling. The resizing also allocates a tonne of StackFrame elements. If we traverse more than
     * BUFFER_SIZE elements, the resulting resize can significantly affect the overall cost of the operation.
     * If we traverse fewer than this number, we are inefficient. Empirically, 16 is enough stack frames
     * for a simple stub+call operation to succeed without resizing, as measured on Java 11.
     */
    private static final int BUFFER_SIZE = 16;

    private static final StackWalker STACK_WALKER = stackWalker();

    private static final String PREFIX = "-> at ";

    private static final StackTraceCleaner CLEANER =
            Plugins.getStackTraceCleanerProvider()
                    .getStackTraceCleaner(new DefaultStackTraceCleaner());

    /**
     * In Java, allocating lambdas is cheap, but not free. stream.map(this::doSomething)
     * will allocate a Function object each time the function is called (although not
     * per element). By assigning these Functions and Predicates to variables, we can
     * avoid the memory allocation.
     */
    private static final Function<StackFrame, StackFrameMetadata> toStackFrameMetadata =
            MetadataShim::new;

    private static final Predicate<StackFrameMetadata> cleanerIsIn = CLEANER::isIn;

    private static final int FRAMES_TO_SKIP = framesToSkip();

    private final StackFrameMetadata sfm;
    private volatile String stackTraceLine;

    LocationImpl(boolean isInline) {
        this.sfm = getStackFrame(isInline);
    }

//@ requires sfm!= null;
    @Override
    public String getSourceFile() {
        return sfm.getFileName();
    }

//@ ensures \result!= null;
    @Override
    public String toString() {
        return stackTraceLine();
    }

//@ requires sfm!= null;
    private String stackTraceLine() {
        if (stackTraceLine == null) {
            synchronized (this) {
                if (stackTraceLine == null) {
                    stackTraceLine = PREFIX + sfm.toString();
                }
            }
        }
        return stackTraceLine;
    }

//@ ensures \result == null || \result.stackFrame() == null;
    private static StackFrameMetadata getStackFrame(boolean isInline) {
        return stackWalk(
                stream ->
                        stream.map(toStackFrameMetadata)
                                .skip(FRAMES_TO_SKIP)
                                .filter(cleanerIsIn)
                                .skip(isInline ? 1 : 0)
                                .findFirst()
                                .orElseThrow(
                                        () -> new MockitoException(noStackTraceFailureMessage())));
    }

//@ ensures \result <==> CLEANER instanceof DefaultStackTraceCleaner;
    private static boolean usingDefaultStackTraceCleaner() {
        return CLEANER instanceof DefaultStackTraceCleaner;
    }

//@ ensures \result!= null;
    private static String noStackTraceFailureMessage() {
        if (usingDefaultStackTraceCleaner()) {
            return "Mockito could not find the first non-Mockito stack frame."
                    + UNEXPECTED_ERROR_SUFFIX;
        } else {
            String cleanerType = CLEANER.getClass().getName();
            String fmt =
                    "Mockito could not find the first non-Mockito stack frame. A custom stack frame cleaner \n"
                            + "(type %s) is in use and this has mostly likely filtered out all the relevant stack frames.";
            return String.format(fmt, cleanerType);
        }
    }

    /**
     * In order to trigger the stack walker, we create some reflective frames. These need to be skipped so as to
     * ensure there are no non-Mockito frames at the top of the stack trace.
     */
//@ requires isOpen;
//@ ensures isOpen;
    private static int framesToSkip() {
        return stackWalk(
                stream -> {
                    List<String> metadata =
                            stream.map(toStackFrameMetadata)
                                    .map(StackFrameMetadata::getClassName)
                                    .collect(Collectors.toList());
                    return metadata.indexOf(LocationImpl.class.getName());
                });
    }

//@ ensures \result == \old(stackWalk(function));
    private static <T> T stackWalk(Function<Stream<StackFrame>, T> function) {
        return (T) STACK_WALKER.walk(function);
    }

//@ ensures \result!= null // code not instrumented
    private static StackWalker stackWalker() {
        return StackWalker.getInstance(
                Collections.singleton(Option.SHOW_REFLECT_FRAMES), BUFFER_SIZE);
    }

    private static final class MetadataShim implements StackFrameMetadata, Serializable {
        private static final long serialVersionUID = 8491903719411428648L;
        private final StackFrame stackFrame;

        private MetadataShim(StackFrame stackFrame) {
            this.stackFrame = stackFrame;
        }

//@ requires isOpen;
//@ ensures isOpen;
        @Override
        public String getClassName() {
            return stackFrame.getClassName();
        }

//@ requires isStackFrameValid(stackFrame)
        @Override
        public String getMethodName() {
            return stackFrame.getMethodName();
        }

//@ requires isOpen;
//@ ensures isOpen;
        @Override
        public String getFileName() {
            return stackFrame.getFileName();
        }

//@ requires stackFrame!= null;
        @Override
        public int getLineNumber() {
            return stackFrame.getLineNumber();
        }

//@ ensures toString()!= null;
        @Override
        public String toString() {
            return stackFrame.toString();
        }

        /**
         * Ensure that this type remains serializable.
         */
//@ requires stackFrame!= null;
        private Object writeReplace() {
            return new SerializableShim(stackFrame.toStackTraceElement());
        }
    }

    private static final class SerializableShim implements StackFrameMetadata, Serializable {
        private static final long serialVersionUID = 7908320459080898690L;
        private final StackTraceElement ste;

        private SerializableShim(StackTraceElement ste) {
            this.ste = ste;
        }

//@ requires ste!= null;
        @Override
        public String getClassName() {
            return ste.getClassName();
        }

//@ requires ste!= null;
        @Override
        public String getMethodName() {
            return ste.getMethodName();
        }

//@ requires ste!= null;
        @Override
        public String getFileName() {
            return ste.getFileName();
        }

//@ requires ste!= null;
        @Override
        public int getLineNumber() {
            return ste.getLineNumber();
        }
    }
}
