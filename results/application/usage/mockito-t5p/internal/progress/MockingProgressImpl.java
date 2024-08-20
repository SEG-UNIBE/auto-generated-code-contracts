/*
 * Copyright (c) 2007 Mockito contributors
 * This program is made available under the terms of the MIT License.
 */
package org.mockito.internal.progress;

import static org.mockito.internal.exceptions.Reporter.unfinishedStubbing;
import static org.mockito.internal.exceptions.Reporter.unfinishedVerificationException;

import java.util.LinkedHashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import org.mockito.internal.configuration.GlobalConfiguration;
import org.mockito.internal.debugging.Localized;
import org.mockito.internal.debugging.LocationFactory;
import org.mockito.internal.exceptions.Reporter;
import org.mockito.internal.listeners.AutoCleanableListener;
import org.mockito.invocation.Location;
import org.mockito.listeners.MockCreationListener;
import org.mockito.listeners.MockitoListener;
import org.mockito.listeners.VerificationListener;
import org.mockito.mock.MockCreationSettings;
import org.mockito.stubbing.OngoingStubbing;
import org.mockito.verification.VerificationMode;
import org.mockito.verification.VerificationStrategy;

@SuppressWarnings("unchecked")
public class MockingProgressImpl implements MockingProgress {

    private final ArgumentMatcherStorage argumentMatcherStorage = new ArgumentMatcherStorageImpl();

    private OngoingStubbing<?> ongoingStubbing;
    private Localized<VerificationMode> verificationMode;
    private Location stubbingInProgress = null;
    private VerificationStrategy verificationStrategy;
    private final Set<MockitoListener> listeners = new LinkedHashSet<>();

    public MockingProgressImpl() {
        this.verificationStrategy = getDefaultVerificationStrategy();
    }

//@ ensures \result == mode;
    public static VerificationStrategy getDefaultVerificationStrategy() {
        return new VerificationStrategy() {
//@ ensures \result == mode;
            @Override
            public VerificationMode maybeVerifyLazily(VerificationMode mode) {
                return mode;
            }
        };
    }

//@ ensures ongoingStubbing == null;
//@ ensures this.ongoingStubbing == ongoingStubbing;
    @Override
    public void reportOngoingStubbing(OngoingStubbing ongoingStubbing) {
        this.ongoingStubbing = ongoingStubbing;
    }

//@ ensures ongoingStubbing == null;
//@ ensures this.ongoingStubbing == ongoingStubbing;
//@ ensures ongoingStubbing == null;
//@ requires ongoingStubbing!= null;
    @Override
    public OngoingStubbing<?> pullOngoingStubbing() {
        OngoingStubbing<?> temp = ongoingStubbing;
        ongoingStubbing = null;
        return temp;
    }

//@ ensures \result!= null;
    @Override
    public Set<VerificationListener> verificationListeners() {
        final LinkedHashSet<VerificationListener> verificationListeners = new LinkedHashSet<>();

        for (MockitoListener listener : listeners) {
            if (listener instanceof VerificationListener) {
                verificationListeners.add((VerificationListener) listener);
            }
        }

        return verificationListeners;
    }

//@ ensures verificationMode == null;
//@ ensures this.validState();
    @Override
    public void verificationStarted(VerificationMode verify) {
        validateState();
        resetOngoingStubbing();
        verificationMode = new Localized(verify);
    }

    /**
     * (non-Javadoc)
     *
     * @see org.mockito.internal.progress.MockingProgress#resetOngoingStubbing()
     */
//@ ensures ongoingStubbing == null;
//@ ensures ongoingStubbing == null;
//@ requires numStubbingInstances() > 0;    // Or maybe == 0 is okay too?
//@ ensures ongoingStubbing == null;
    public void resetOngoingStubbing() {
        ongoingStubbing = null;
    }

//@ requires verificationMode!= null;
    @Override
    public VerificationMode pullVerificationMode() {
        if (verificationMode == null) {
            return null;
        }

        VerificationMode temp = verificationMode.getObject();
        verificationMode = null;
        return temp;
    }

//@ ensures stubbingInProgress == null;
//@ ensures this.validState();
    @Override
    public void stubbingStarted() {
        validateState();
        stubbingInProgress = LocationFactory.create();
    }

//@ requires mostStuff();
    @Override
    public void validateState() {
        validateMostStuff();

        // validate stubbing:
        if (stubbingInProgress != null) {
            Location temp = stubbingInProgress;
            stubbingInProgress = null;
            throw unfinishedStubbing(temp);
        }
    }

//@ ensures GlobalConfiguration.valid();
    private void validateMostStuff() {
        // State is cool when GlobalConfiguration is already loaded
        // this cannot really be tested functionally because I cannot dynamically mess up
        // org.mockito.configuration.MockitoConfiguration class
        GlobalConfiguration.validate();

        if (verificationMode != null) {
            Location location = verificationMode.getLocation();
            verificationMode = null;
            throw unfinishedVerificationException(location);
        }

        getArgumentMatcherStorage().validateState();
    }

//@ ensures stubbingInProgress == null;
    @Override
    public void stubbingCompleted() {
        stubbingInProgress = null;
    }

//@ ensures \result!= null;
    @Override
    public String toString() {
        return "ongoingStubbing: "
                + ongoingStubbing
                + ", verificationMode: "
                + verificationMode
                + ", stubbingInProgress: "
                + stubbingInProgress;
    }

//@ requires isArgumentMatcherStorageInitialized(this);
    @Override
    public void reset() {
        stubbingInProgress = null;
        verificationMode = null;
        getArgumentMatcherStorage().reset();
    }

//@ ensures \result == argumentMatcherStorage;
    @Override
    public ArgumentMatcherStorage getArgumentMatcherStorage() {
        return argumentMatcherStorage;
    }

//@ requires settings!= null;
    @Override
    public void mockingStarted(Object mock, MockCreationSettings settings) {
        for (MockitoListener listener : listeners) {
            if (listener instanceof MockCreationListener) {
                ((MockCreationListener) listener).onMockCreated(mock, settings);
            }
        }
        validateMostStuff();
    }

//@ requires settings!= null;
    @Override
    public void mockingStarted(Class<?> mock, MockCreationSettings settings) {
        for (MockitoListener listener : listeners) {
            if (listener instanceof MockCreationListener) {
                ((MockCreationListener) listener).onStaticMockCreated(mock, settings);
            }
        }
        validateMostStuff();
    }

//@ requires listeners!= null;
//@ ensures this.listeners == listeners;
//@ requires listener!= null;
//@ requires 0 <= first;
//@ requires 0 <= toCopy;
//@ requires first + toCopy <= source.numInstances();
    @Override
    public void addListener(MockitoListener listener) {
        addListener(listener, listeners);
    }

//@ requires listener!= null;
//@ requires \nonnullelements(listeners);
    static void addListener(MockitoListener listener, Set<MockitoListener> listeners) {
        List<MockitoListener> delete = new LinkedList<>();
        for (MockitoListener existing : listeners) {
            if (existing.getClass().equals(listener.getClass())) {
                if (existing instanceof AutoCleanableListener
                        && ((AutoCleanableListener) existing).isListenerDirty()) {
                    // dirty listener means that there was an exception even before the test started
                    // if we fail here with redundant mockito listener exception there will be
                    // multiple failures causing confusion
                    // so we simply remove the existing listener and move on
                    delete.add(existing);
                } else {
                    Reporter.redundantMockitoListener(listener.getClass().getSimpleName());
                }
            }
        }
        // delete dirty listeners so they don't occupy state/memory and don't receive notifications
        listeners.removeAll(delete);
        listeners.add(listener);
    }

//@ requires listeners!= null;
//@ requires \nonnullelements(listeners);
    @Override
    public void removeListener(MockitoListener listener) {
        this.listeners.remove(listener);
    }

//@ ensures getVerificationStrategy() == strategy;
    @Override
    public void setVerificationStrategy(VerificationStrategy strategy) {
        this.verificationStrategy = strategy;
    }

//@ requires mode!= null;
    @Override
    public VerificationMode maybeVerifyLazily(VerificationMode mode) {
        return this.verificationStrategy.maybeVerifyLazily(mode);
    }

//@ requires initialSize > 0 && sizeIncrease >= 0 && sizeMultiple >= 1;
//@ requires!(sizeIncrease == 0 && sizeMultiple == 1)
    @Override
    public void clearListeners() {
        listeners.clear();
    }

    /*

    //TODO 545 thread safety of all mockito

    use cases:
       - single threaded execution throughout
       - single threaded mock creation, stubbing & verification, multi-threaded interaction with mock
       - thread per test case

    */
}
