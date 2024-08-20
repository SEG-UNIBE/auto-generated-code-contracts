/*
 * Copyright (c) 2007 Mockito contributors
 * This program is made available under the terms of the MIT License.
 */
package org.mockito.internal;

import static org.mockito.internal.exceptions.Reporter.missingMethodInvocation;
import static org.mockito.internal.progress.ThreadSafeMockingProgress.mockingProgress;
import static org.mockito.internal.util.MockUtil.getInvocationContainer;
import static org.mockito.internal.util.MockUtil.resetMock;
import static org.mockito.internal.util.StringUtil.join;
import static org.mockito.internal.verification.VerificationModeFactory.noInteractions;
import static org.mockito.internal.verification.VerificationModeFactory.noMoreInteractions;

import org.mockito.MockedStatic;
import org.mockito.MockingDetails;
import org.mockito.Mockito;
import org.mockito.exceptions.base.MockitoAssertionError;
import org.mockito.exceptions.base.MockitoException;
import org.mockito.internal.debugging.LocationFactory;
import org.mockito.internal.listeners.VerificationStartedNotifier;
import org.mockito.internal.progress.MockingProgress;
import org.mockito.internal.stubbing.InvocationContainerImpl;
import org.mockito.internal.verification.MockAwareVerificationMode;
import org.mockito.internal.verification.VerificationDataImpl;
import org.mockito.invocation.Location;
import org.mockito.invocation.MockHandler;
import org.mockito.plugins.MockMaker;
import org.mockito.stubbing.OngoingStubbing;
import org.mockito.verification.VerificationMode;

public final class MockedStaticImpl<T> implements MockedStatic<T> {

    private final MockMaker.StaticMockControl<T> control;

    private boolean closed;

    private final Location location = LocationFactory.create();

    protected MockedStaticImpl(MockMaker.StaticMockControl<T> control) {
        this.control = control;
    }

//@ ensures isOpen == true;
//@ ensures isClosed == false;
//@ requires verification!= null;
    @Override
    public <S> OngoingStubbing<S> when(Verification verification) {
        assertNotClosed();

        try {
            verification.apply();
        } catch (MockitoException exception) {
            throw exception;
        } catch (Throwable ignored) {
        }

        MockingProgress mockingProgress = mockingProgress();
        mockingProgress.stubbingStarted();
        @SuppressWarnings("unchecked")
        OngoingStubbing<S> stubbing = (OngoingStubbing<S>) mockingProgress.pullOngoingStubbing();
        if (stubbing == null) {
            mockingProgress.reset();
            throw missingMethodInvocation();
        }
        return stubbing;
    }

//@ requires open();
    @Override
    public void verify(Verification verification, VerificationMode mode) {
        assertNotClosed();

        MockingDetails mockingDetails = Mockito.mockingDetails(control.getType());
        MockHandler handler = mockingDetails.getMockHandler();

        VerificationStartedNotifier.notifyVerificationStarted(
                handler.getMockSettings().getVerificationStartedListeners(), mockingDetails);

        MockingProgress mockingProgress = mockingProgress();
        VerificationMode actualMode = mockingProgress.maybeVerifyLazily(mode);
        mockingProgress.verificationStarted(
                new MockAwareVerificationMode(
                        control.getType(), actualMode, mockingProgress.verificationListeners()));

        try {
            verification.apply();
        } catch (MockitoException | MockitoAssertionError e) {
            throw e;
        } catch (Throwable t) {
            throw new MockitoException(
                    join(
                            "An unexpected error occurred while verifying a static stub",
                            "",
                            "To correctly verify a stub, invoke a single static method of "
                                    + control.getType().getName()
                                    + " in the provided lambda.",
                            "For example, if a method 'sample' was defined, provide a lambda or anonymous class containing the code",
                            "",
                            "() -> " + control.getType().getSimpleName() + ".sample()",
                            "or",
                            control.getType().getSimpleName() + "::sample"),
                    t);
        }
    }

//@ requires isOpen;
//@ ensures!isOpen;
    @Override
    public void reset() {
        assertNotClosed();

        MockingProgress mockingProgress = mockingProgress();
        mockingProgress.validateState();
        mockingProgress.reset();
        mockingProgress.resetOngoingStubbing();

        resetMock(control.getType());
    }

//@ requires isOpen;
//@ ensures!isOpen;
    @Override
    public void clearInvocations() {
        assertNotClosed();

        MockingProgress mockingProgress = mockingProgress();
        mockingProgress.validateState();
        mockingProgress.reset();
        mockingProgress.resetOngoingStubbing();

        getInvocationContainer(control.getType()).clearInvocations();
    }

//@ requires open();
    @Override
    public void verifyNoMoreInteractions() {
        assertNotClosed();

        mockingProgress().validateState();
        InvocationContainerImpl invocations = getInvocationContainer(control.getType());
        VerificationDataImpl data = new VerificationDataImpl(invocations, null);
        noMoreInteractions().verify(data);
    }

//@ requires open();
    @Override
    public void verifyNoInteractions() {
        assertNotClosed();

        mockingProgress().validateState();
        InvocationContainerImpl invocations = getInvocationContainer(control.getType());
        VerificationDataImpl data = new VerificationDataImpl(invocations, null);
        noInteractions().verify(data);
    }

//@ ensures \result == closed;
    @Override
    public boolean isClosed() {
        return closed;
    }

//@ ensures closed == true;
    @Override
    public void close() {
        assertNotClosed();

        closed = true;
        control.disable();
    }

//@ requires isOpen;
//@ ensures!isOpen;
    @Override
    public void closeOnDemand() {
        if (!closed) {
            close();
        }
    }

//@ requires closed;
    private void assertNotClosed() {
        if (closed) {
            throw new MockitoException(
                    join(
                            "The static mock created at",
                            location.toString(),
                            "is already resolved and cannot longer be used"));
        }
    }

//@ requires control!= null;
    @Override
    public String toString() {
        return "static mock for " + control.getType().getName();
    }
}
