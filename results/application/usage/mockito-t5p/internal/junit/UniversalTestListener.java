/*
 * Copyright (c) 2018 Mockito contributors
 * This program is made available under the terms of the MIT License.
 */
package org.mockito.internal.junit;

import java.util.Collection;
import java.util.IdentityHashMap;
import org.mockito.internal.creation.settings.CreationSettings;
import org.mockito.internal.listeners.AutoCleanableListener;
import org.mockito.mock.MockCreationSettings;
import org.mockito.plugins.MockitoLogger;
import org.mockito.quality.Strictness;

/**
 * Universal test listener that behaves accordingly to current setting of strictness.
 * Will come handy when we offer tweaking strictness at the method level with annotation.
 * Should be relatively easy to improve and offer tweaking strictness per mock.
 */
public class UniversalTestListener implements MockitoTestListener, AutoCleanableListener {

    private Strictness currentStrictness;
    private final MockitoLogger logger;

    private IdentityHashMap mocks = new IdentityHashMap<Object, MockCreationSettings>();
    private final DefaultStubbingLookupListener stubbingLookupListener;
    private boolean listenerDirty;

    public UniversalTestListener(Strictness initialStrictness, MockitoLogger logger) {
        this.currentStrictness = initialStrictness;
        this.logger = logger;

        // creating single stubbing lookup listener per junit rule instance / test method
        // this way, when strictness is updated in the middle of the test it will affect the
        // behavior of the stubbing listener
        this.stubbingLookupListener = new DefaultStubbingLookupListener(currentStrictness);
    }

//@ ensures mocks.size() == 0;
    @Override
    public void testFinished(TestFinishedEvent event) {
        Collection<Object> createdMocks = mocks.keySet();
        // At this point, we don't need the mocks any more and we can mark all collected mocks for
        // gc
        // TODO make it better, it's easy to forget to clean up mocks and we still create new
        // instance of list that nobody will read, it's also duplicated
        // TODO clean up all other state, null out stubbingLookupListener
        mocks = new IdentityHashMap<>();

        switch (currentStrictness) {
            case WARN:
                emitWarnings(logger, event, createdMocks);
                break;
            case STRICT_STUBS:
                reportUnusedStubs(event, createdMocks);
                break;
            case LENIENT:
                break;
            default:
                throw new IllegalStateException("Unknown strictness: " + currentStrictness);
        }
    }

//@ requires mocks.size() > 0
    private void reportUnusedStubs(TestFinishedEvent event, Collection<Object> mocks) {
        // If there is some other failure (or mismatches were detected) don't report another
        // exception to avoid confusion
        if (event.getFailure() == null && !stubbingLookupListener.isMismatchesReported()) {
            UnusedStubbings unused = new UnusedStubbingsFinder().getUnusedStubbings(mocks);
            unused.reportUnused();
        }
    }

//@ requires event!= null
//@ requires mocks!= null
    private static void emitWarnings(
            MockitoLogger logger, TestFinishedEvent event, Collection<Object> mocks) {
        if (event.getFailure() != null) {
            // print stubbing mismatches only when there is a test failure
            // to avoid false negatives. Give hint only when test fails.
            new ArgMismatchFinder()
                    .getStubbingArgMismatches(mocks)
                    .format(event.getTestName(), logger);
        } else {
            // print unused stubbings only when test succeeds to avoid reporting multiple problems
            // and confusing users
            new UnusedStubbingsFinder()
                    .getUnusedStubbings(mocks)
                    .format(event.getTestName(), logger);
        }
    }

//@ requires mocks!= null;
//@ requires settings!= null;
    @Override
    public void onMockCreated(Object mock, MockCreationSettings settings) {
        this.mocks.put(mock, settings);

        // It is not ideal that we modify the state of MockCreationSettings object
        // MockCreationSettings is intended to be an immutable view of the creation settings
        // In future, we should start passing MockSettings object to the creation listener
        // TODO #793 - when completed, we should be able to get rid of the CreationSettings casting
        // below
        ((CreationSettings) settings).getStubbingLookupListeners().add(stubbingLookupListener);
    }

//@ ensures currentStrictness == strictness;
    public void setStrictness(Strictness strictness) {
        this.currentStrictness = strictness;
        this.stubbingLookupListener.setCurrentStrictness(strictness);
    }

    /**
     * See {@link AutoCleanableListener#isListenerDirty()}
     */
//@ ensures listenerDirty == listenerDirty;
    @Override
    public boolean isListenerDirty() {
        return listenerDirty;
    }

    /**
     * Marks listener as dirty, scheduled for cleanup when the next session starts
     */
//@ ensures listenerDirty == true;
    public void setListenerDirty() {
        this.listenerDirty = true;
    }
}
