/*
 * Copyright (c) 2016 Mockito contributors
 * This program is made available under the terms of the MIT License.
 */
package org.mockito.internal.junit;

import static org.mockito.internal.progress.ThreadSafeMockingProgress.mockingProgress;

import org.junit.runner.Description;
import org.junit.runners.model.Statement;
import org.mockito.exceptions.base.MockitoAssertionError;
import org.mockito.internal.progress.MockingProgressImpl;
import org.mockito.internal.verification.api.VerificationData;
import org.mockito.junit.VerificationCollector;
import org.mockito.verification.VerificationMode;
import org.mockito.verification.VerificationStrategy;

/**
 * Mockito implementation of VerificationCollector.
 */
public class VerificationCollectorImpl implements VerificationCollector {

    private StringBuilder builder;
    private int numberOfFailures;

    public VerificationCollectorImpl() {
        this.resetBuilder();
    }

//@ requires initialSize > 0 && sizeIncrease >= 0 && sizeMultiple >= 1;
//@ requires!(sizeIncrease == 0 && sizeMultiple == 1)
    @Override
    public Statement apply(final Statement base, final Description description) {
        return new Statement() {
//@ requires pre();
//@ ensures post();
            @Override
            public void evaluate() throws Throwable {
                try {
                    VerificationCollectorImpl.this.assertLazily();
                    base.evaluate();
                    VerificationCollectorImpl.this.collectAndReport();
                } finally {
                    // If base.evaluate() throws an error, we must explicitly reset the
                    // VerificationStrategy
                    // to prevent subsequent tests to be assert lazily
                    mockingProgress()
                            .setVerificationStrategy(
                                    MockingProgressImpl.getDefaultVerificationStrategy());
                }
            }
        };
    }

//@ ensures this.numberOfFailures > 0 ==> \result == this.builder;
    public void collectAndReport() throws MockitoAssertionError {
        mockingProgress()
                .setVerificationStrategy(MockingProgressImpl.getDefaultVerificationStrategy());

        if (this.numberOfFailures > 0) {
            String error = this.builder.toString();

            this.resetBuilder();

            throw new MockitoAssertionError(error);
        }
    }

//@ ensures \result == this;
    @Override
    public VerificationCollector assertLazily() {
        mockingProgress()
                .setVerificationStrategy(
                        new VerificationStrategy() {
//@ ensures \result == this.mode;
                            @Override
                            public VerificationMode maybeVerifyLazily(VerificationMode mode) {
                                return new VerificationWrapper(mode);
                            }
                        });
        return this;
    }

//@ ensures builder!= null;
//@ ensures numberOfFailures == 0;
    private void resetBuilder() {
        this.builder = new StringBuilder().append("There were multiple verification failures:");
        this.numberOfFailures = 0;
    }

//@ requires message!= null;
    private void append(String message) {
        this.numberOfFailures++;
        this.builder
                .append('\n')
                .append(this.numberOfFailures)
                .append(". ")
                .append(message.trim())
                .append('\n');
    }

    private class VerificationWrapper implements VerificationMode {

        private final VerificationMode delegate;

        private VerificationWrapper(VerificationMode delegate) {
            this.delegate = delegate;
        }

//@ requires data!= null
        @Override
        public void verify(VerificationData data) {
            try {
                this.delegate.verify(data);
            } catch (AssertionError error) {
                VerificationCollectorImpl.this.append(error.getMessage());
            }
        }

//@ ensures \result == this;
        @Override
        public VerificationMode description(String description) {
            throw new IllegalStateException("Should not fail in this mode");
        }
    }
}
