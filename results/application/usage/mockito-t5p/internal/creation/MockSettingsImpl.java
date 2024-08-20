/*
 * Copyright (c) 2007 Mockito contributors
 * This program is made available under the terms of the MIT License.
 */
package org.mockito.internal.creation;

import static java.util.Arrays.asList;

import static org.mockito.internal.exceptions.Reporter.defaultAnswerDoesNotAcceptNullParameter;
import static org.mockito.internal.exceptions.Reporter.extraInterfacesAcceptsOnlyInterfaces;
import static org.mockito.internal.exceptions.Reporter.extraInterfacesDoesNotAcceptNullParameters;
import static org.mockito.internal.exceptions.Reporter.extraInterfacesRequiresAtLeastOneInterface;
import static org.mockito.internal.exceptions.Reporter.methodDoesNotAcceptParameter;
import static org.mockito.internal.exceptions.Reporter.requiresAtLeastOneListener;
import static org.mockito.internal.exceptions.Reporter.strictnessDoesNotAcceptNullParameter;
import static org.mockito.internal.util.collections.Sets.newSet;

import java.io.Serializable;
import java.lang.reflect.Type;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import org.mockito.MockSettings;
import org.mockito.exceptions.base.MockitoException;
import org.mockito.internal.creation.settings.CreationSettings;
import org.mockito.internal.debugging.VerboseMockInvocationLogger;
import org.mockito.internal.util.Checks;
import org.mockito.internal.util.MockCreationValidator;
import org.mockito.internal.util.MockNameImpl;
import org.mockito.listeners.InvocationListener;
import org.mockito.listeners.StubbingLookupListener;
import org.mockito.listeners.VerificationStartedListener;
import org.mockito.mock.MockCreationSettings;
import org.mockito.mock.MockName;
import org.mockito.mock.SerializableMode;
import org.mockito.quality.Strictness;
import org.mockito.stubbing.Answer;

@SuppressWarnings("unchecked")
public class MockSettingsImpl<T> extends CreationSettings<T>
        implements MockSettings, MockCreationSettings<T> {

    private static final long serialVersionUID = 4475297236197939569L;
    private boolean useConstructor;
    private Object outerClassInstance;
    private Object[] constructorArgs;

//@ ensures \result == serializable(SerializableMode.BASIC);
    @Override
    public MockSettings serializable() {
        return serializable(SerializableMode.BASIC);
    }

//@ ensures serializableMode == mode;
    @Override
    public MockSettings serializable(SerializableMode mode) {
        this.serializableMode = mode;
        return this;
    }

//@ requires extraInterfaces!= null;
    @Override
    public MockSettings extraInterfaces(Class<?>... extraInterfaces) {
        if (extraInterfaces == null || extraInterfaces.length == 0) {
            throw extraInterfacesRequiresAtLeastOneInterface();
        }

        for (Class<?> i : extraInterfaces) {
            if (i == null) {
                throw extraInterfacesDoesNotAcceptNullParameters();
            } else if (!i.isInterface()) {
                throw extraInterfacesAcceptsOnlyInterfaces(i);
            }
        }
        this.extraInterfaces = newSet(extraInterfaces);
        return this;
    }

//@ ensures \result == mockName;
    @Override
    public MockName getMockName() {
        return mockName;
    }

//@ requires!(isEmpty && extraInterfaces.isEmpty());
    @Override
    public Set<Class<?>> getExtraInterfaces() {
        return extraInterfaces;
    }

//@ requires numInstances() > 0;    // Or maybe == 0 is okay too?
//@ ensures this.spiedInstance == spiedInstance;
//@ requires spiedInstance!= null;
    @Override
    public Object getSpiedInstance() {
        return spiedInstance;
    }

//@ ensures name == name;
    @Override
    public MockSettings name(String name) {
        this.name = name;
        return this;
    }

//@ requires spiedInstance == null;
//@ ensures this.spiedInstance == spiedInstance;
    @Override
    public MockSettings spiedInstance(Object spiedInstance) {
        this.spiedInstance = spiedInstance;
        return this;
    }

//@ ensures \result.defaultAnswer == defaultAnswer;
    @Override
    public MockSettings defaultAnswer(Answer defaultAnswer) {
        this.defaultAnswer = defaultAnswer;
        if (defaultAnswer == null) {
            throw defaultAnswerDoesNotAcceptNullParameter();
        }
        return this;
    }

//@ ensures \result == defaultAnswer;
    @Override
    public Answer<Object> getDefaultAnswer() {
        return defaultAnswer;
    }

//@ ensures stubOnly();
    @Override
    public MockSettingsImpl<T> stubOnly() {
        this.stubOnly = true;
        return this;
    }

//@ requires constructorArgs!= null;
//@ ensures useConstructor();
    @Override
    public MockSettings useConstructor(Object... constructorArgs) {
        Checks.checkNotNull(
                constructorArgs,
                "constructorArgs",
                "If you need to pass null, please cast it to the right type, e.g.: useConstructor((String) null)");
        this.useConstructor = true;
        this.constructorArgs = constructorArgs;
        return this;
    }

//@ requires outerClassInstance!= null;
//@ ensures  outerClassInstance == outerClassInstance;
    @Override
    public MockSettings outerInstance(Object outerClassInstance) {
        this.outerClassInstance = outerClassInstance;
        return this;
    }

//@ ensures stripAnnotations == true;
    @Override
    public MockSettings withoutAnnotations() {
        stripAnnotations = true;
        return this;
    }

//@ ensures \result == useConstructor;
    @Override
    public boolean isUsingConstructor() {
        return useConstructor;
    }

//@ requires classInstance == outerClassInstance;
    @Override
    public Object getOuterClassInstance() {
        return outerClassInstance;
    }

//@ requires outerClassInstance!= null;
    @Override
    public Object[] getConstructorArgs() {
        if (outerClassInstance == null) {
            return constructorArgs;
        }
        List<Object> resultArgs = new ArrayList<>(constructorArgs.length + 1);
        resultArgs.add(outerClassInstance);
        resultArgs.addAll(asList(constructorArgs));
        return resultArgs.toArray(new Object[constructorArgs.length + 1]);
    }

//@ ensures \result == this.stubOnly;
    @Override
    public boolean isStubOnly() {
        return this.stubOnly;
    }

//@ requires isOpen;
//@ ensures isOpen;
    @Override
    public MockSettings verboseLogging() {
        if (!invocationListenersContainsType(VerboseMockInvocationLogger.class)) {
            invocationListeners(new VerboseMockInvocationLogger());
        }
        return this;
    }

//@ requires listeners!= null;
//@ requires \nonnullelements(listeners);
    @Override
    public MockSettings invocationListeners(InvocationListener... listeners) {
        addListeners(listeners, invocationListeners, "invocationListeners");
        return this;
    }

//@ requires listeners!= null;
//@ requires \nonnullelements(listeners);
    @Override
    public MockSettings stubbingLookupListeners(StubbingLookupListener... listeners) {
        addListeners(listeners, stubbingLookupListeners, "stubbingLookupListeners");
        return this;
    }

//@ requires listeners!= null && container!= null;
//@ requires method!= null;
    static <T> void addListeners(T[] listeners, List<T> container, String method) {
        if (listeners == null) {
            throw methodDoesNotAcceptParameter(method, "null vararg array.");
        }
        if (listeners.length == 0) {
            throw requiresAtLeastOneListener(method);
        }
        for (T listener : listeners) {
            if (listener == null) {
                throw methodDoesNotAcceptParameter(method, "null listeners.");
            }
            container.add(listener);
        }
    }

//@ requires listeners!= null;
//@ requires \nonnullelements(listeners);
    @Override
    public MockSettings verificationStartedListeners(VerificationStartedListener... listeners) {
        addListeners(listeners, this.verificationStartedListeners, "verificationStartedListeners");
        return this;
    }

//@ requires clazz!= null;
    private boolean invocationListenersContainsType(Class<?> clazz) {
        for (InvocationListener listener : invocationListeners) {
            if (listener.getClass().equals(clazz)) {
                return true;
            }
        }
        return false;
    }

//@ ensures \result == (invocationListeners().isEmpty());
    public boolean hasInvocationListeners() {
        return !getInvocationListeners().isEmpty();
    }

//@ ensures \result == typeToMock;
    @Override
    public Class<T> getTypeToMock() {
        return typeToMock;
    }

//@ ensures \result == validatedSettings(typeToMock, (CreationSettings<T2>) this);
    @Override
    public <T2> MockCreationSettings<T2> build(Class<T2> typeToMock) {
        return validatedSettings(typeToMock, (CreationSettings<T2>) this);
    }

//@ requires classToMock!= null;
    @Override
    public <T2> MockCreationSettings<T2> buildStatic(Class<T2> classToMock) {
        return validatedStaticSettings(classToMock, (CreationSettings<T2>) this);
    }

//@ ensures strictness == Strictness.LENIENT;
    @Override
    public MockSettings lenient() {
        this.strictness = Strictness.LENIENT;
        return this;
    }

//@ requires strictness!= null;
//@ ensures strictness == strictness;
    @Override
    public MockSettings strictness(Strictness strictness) {
        if (strictness == null) {
            throw strictnessDoesNotAcceptNullParameter();
        }
        this.strictness = strictness;
        return this;
    }

//@ ensures mockMaker == null;
//@ ensures this.mockMaker == mockMaker;
    @Override
    public MockSettings mockMaker(String mockMaker) {
        this.mockMaker = mockMaker;
        return this;
    }

//@ ensures genericType == null;
//@ ensures this.genericTypeToMock == genericType;
    @Override
    public MockSettings genericTypeToMock(Type genericType) {
        this.genericTypeToMock = genericType;
        return this;
    }

//@ ensures \result.getTypeToMock() == typeToMock;
//@ ensures \result.getCreationSettings() == source;
    private static <T> CreationSettings<T> validatedSettings(
            Class<T> typeToMock, CreationSettings<T> source) {
        MockCreationValidator validator = new MockCreationValidator();

        validator.validateType(typeToMock, source.getMockMaker());
        validator.validateExtraInterfaces(typeToMock, source.getExtraInterfaces());
        validator.validateMockedType(typeToMock, source.getSpiedInstance());

        // TODO SF - add this validation and also add missing coverage
        //        validator.validateDelegatedInstance(classToMock, settings.getDelegatedInstance());

        validator.validateConstructorUse(source.isUsingConstructor(), source.getSerializableMode());

        // TODO SF - I don't think we really need CreationSettings type
        // TODO do we really need to copy the entire settings every time we create mock object? it
        // does not seem necessary.
        CreationSettings<T> settings = new CreationSettings<T>(source);
        settings.setMockName(new MockNameImpl(source.getName(), typeToMock, false));
        settings.setTypeToMock(typeToMock);
        settings.setExtraInterfaces(prepareExtraInterfaces(source));
        return settings;
    }

//@ requires classToMock!= null;
//@ requires source!= null;
    private static <T> CreationSettings<T> validatedStaticSettings(
            Class<T> classToMock, CreationSettings<T> source) {

        if (classToMock.isPrimitive()) {
            throw new MockitoException(
                    "Cannot create static mock of primitive type " + classToMock);
        }
        if (!source.getExtraInterfaces().isEmpty()) {
            throw new MockitoException(
                    "Cannot specify additional interfaces for static mock of " + classToMock);
        }
        if (source.getSpiedInstance() != null) {
            throw new MockitoException(
                    "Cannot specify spied instance for static mock of " + classToMock);
        }

        CreationSettings<T> settings = new CreationSettings<T>(source);
        settings.setMockName(new MockNameImpl(source.getName(), classToMock, true));
        settings.setTypeToMock(classToMock);
        return settings;
    }

//@ requires settings!= null;
//@ ensures \result.size() == settings.getExtraInterfaces().size();
    private static Set<Class<?>> prepareExtraInterfaces(CreationSettings settings) {
        Set<Class<?>> interfaces = new HashSet<>(settings.getExtraInterfaces());
        if (settings.isSerializable()) {
            interfaces.add(Serializable.class);
        }
        return interfaces;
    }
}
