/*
 * Copyright (c) 2016 Mockito contributors
 * This program is made available under the terms of the MIT License.
 */
package org.mockito.internal.creation.bytebuddy;

import org.mockito.MockedConstruction;
import org.mockito.creation.instance.Instantiator;
import org.mockito.internal.exceptions.Reporter;
import org.mockito.invocation.MockHandler;
import org.mockito.mock.MockCreationSettings;
import org.mockito.plugins.InlineMockMaker;

import java.util.Optional;
import java.util.function.Function;

public class InlineByteBuddyMockMaker
        implements ClassCreatingMockMaker, InlineMockMaker, Instantiator {
    private final InlineDelegateByteBuddyMockMaker inlineDelegateByteBuddyMockMaker;

    public InlineByteBuddyMockMaker() {
        try {
            inlineDelegateByteBuddyMockMaker = new InlineDelegateByteBuddyMockMaker();
        } catch (NoClassDefFoundError e) {
            Reporter.missingByteBuddyDependency(e);
            throw e;
        }
    }

    InlineByteBuddyMockMaker(InlineDelegateByteBuddyMockMaker inlineDelegateByteBuddyMockMaker) {
        this.inlineDelegateByteBuddyMockMaker = inlineDelegateByteBuddyMockMaker;
    }

//@ requires cls!= null;
    @Override
    public <T> T newInstance(Class<T> cls) {
        return inlineDelegateByteBuddyMockMaker.newInstance(cls);
    }

//@ requires settings!= null;
    @Override
    public <T> Class<? extends T> createMockType(MockCreationSettings<T> settings) {
        return inlineDelegateByteBuddyMockMaker.createMockType(settings);
    }

//@ requires mock!= null;
    @Override
    public void clearMock(Object mock) {
        inlineDelegateByteBuddyMockMaker.clearMock(mock);
    }

//@ requires 0 <= first;
//@ requires 0 <= toCopy;
//@ requires first + toCopy <= source.numInstances();
    @Override
    public void clearAllMocks() {
        inlineDelegateByteBuddyMockMaker.clearAllMocks();
    }

//@ requires settings!= null && handler!= null;
    @Override
    public <T> T createMock(MockCreationSettings<T> settings, MockHandler handler) {
        return inlineDelegateByteBuddyMockMaker.createMock(settings, handler);
    }

//@ requires settings!= null;
//@ requires handler!= null;
    @Override
    public <T> Optional<T> createSpy(
            MockCreationSettings<T> settings, MockHandler handler, T instance) {
        return inlineDelegateByteBuddyMockMaker.createSpy(settings, handler, instance);
    }

//@ requires mock!= null;
    @Override
    public MockHandler getHandler(Object mock) {
        return inlineDelegateByteBuddyMockMaker.getHandler(mock);
    }

//@ requires settings!= null;
    @Override
    public void resetMock(Object mock, MockHandler newHandler, MockCreationSettings settings) {
        inlineDelegateByteBuddyMockMaker.resetMock(mock, newHandler, settings);
    }

//@ requires type!= null;
    @Override
    public TypeMockability isTypeMockable(Class<?> type) {
        return inlineDelegateByteBuddyMockMaker.isTypeMockable(type);
    }

//@ requires type!= null;
//@ requires settings!= null;
//@ requires handler!= null;
    @Override
    public <T> StaticMockControl<T> createStaticMock(
            Class<T> type, MockCreationSettings<T> settings, MockHandler handler) {
        return inlineDelegateByteBuddyMockMaker.createStaticMock(type, settings, handler);
    }

//@ requires type!= null;
//@ requires settings!= null;
//@ requires handler!= null;
    @Override
    public <T> ConstructionMockControl<T> createConstructionMock(
            Class<T> type,
            Function<MockedConstruction.Context, MockCreationSettings<T>> settingsFactory,
            Function<MockedConstruction.Context, MockHandler<T>> handlerFactory,
            MockedConstruction.MockInitializer<T> mockInitializer) {
        return inlineDelegateByteBuddyMockMaker.createConstructionMock(
                type, settingsFactory, handlerFactory, mockInitializer);
    }

//@ requires 0 <= first;
//@ requires 0 <= toCopy;
//@ requires first + toCopy <= source.numInstances();
    @Override
    public void clearAllCaches() {
        inlineDelegateByteBuddyMockMaker.clearAllCaches();
    }
}
