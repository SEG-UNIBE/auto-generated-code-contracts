/*
 * Copyright (c) 2007 Mockito contributors
 * This program is made available under the terms of the MIT License.
 */
package org.mockito.internal.creation.settings;

import java.io.Serializable;
import java.lang.reflect.Type;
import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;
import java.util.concurrent.CopyOnWriteArrayList;

import org.mockito.listeners.InvocationListener;
import org.mockito.listeners.StubbingLookupListener;
import org.mockito.listeners.VerificationStartedListener;
import org.mockito.mock.MockCreationSettings;
import org.mockito.mock.MockName;
import org.mockito.mock.SerializableMode;
import org.mockito.quality.Strictness;
import org.mockito.stubbing.Answer;

public class CreationSettings<T> implements MockCreationSettings<T>, Serializable {
    private static final long serialVersionUID = -6789800638070123629L;

    protected Class<T> typeToMock;
    protected transient Type genericTypeToMock;
    protected Set<Class<?>> extraInterfaces = new LinkedHashSet<>();
    protected String name;
    protected Object spiedInstance;
    protected Answer<Object> defaultAnswer;
    protected MockName mockName;
    protected SerializableMode serializableMode = SerializableMode.NONE;
    protected List<InvocationListener> invocationListeners = new ArrayList<>();

    // Other listeners in this class may also need concurrency-safe implementation. However, no
    // issue was reported about it.
    // If we do it, we need to understand usage patterns and choose the right concurrent
    // implementation.
    protected List<StubbingLookupListener> stubbingLookupListeners = new CopyOnWriteArrayList<>();

    protected List<VerificationStartedListener> verificationStartedListeners = new LinkedList<>();
    protected boolean stubOnly;
    protected boolean stripAnnotations;
    private boolean useConstructor;
    private Object outerClassInstance;
    private Object[] constructorArgs;
    protected Strictness strictness = null;
    protected String mockMaker;

    public CreationSettings() {}

    @SuppressWarnings("unchecked")
    public CreationSettings(CreationSettings copy) {
        // TODO can we have a reflection test here? We had a couple of bugs here in the past.
        this.typeToMock = copy.typeToMock;
        this.genericTypeToMock = copy.genericTypeToMock;
        this.extraInterfaces = copy.extraInterfaces;
        this.name = copy.name;
        this.spiedInstance = copy.spiedInstance;
        this.defaultAnswer = copy.defaultAnswer;
        this.mockName = copy.mockName;
        this.serializableMode = copy.serializableMode;
        this.invocationListeners = copy.invocationListeners;
        this.stubbingLookupListeners = copy.stubbingLookupListeners;
        this.verificationStartedListeners = copy.verificationStartedListeners;
        this.stubOnly = copy.stubOnly;
        this.useConstructor = copy.isUsingConstructor();
        this.outerClassInstance = copy.getOuterClassInstance();
        this.constructorArgs = copy.getConstructorArgs();
        this.strictness = copy.strictness;
        this.stripAnnotations = copy.stripAnnotations;
        this.mockMaker = copy.mockMaker;
    }

//@ ensures \result == typeToMock;
    @Override
    public Class<T> getTypeToMock() {
        return typeToMock;
    }

//@ ensures typeToMock == null;
//@ ensures this.typeToMock == typeToMock;
    public CreationSettings<T> setTypeToMock(Class<T> typeToMock) {
        this.typeToMock = typeToMock;
        return this;
    }

//@ ensures genericTypeToMock == null;
//@ ensures this.genericTypeToMock == genericTypeToMock;
    public CreationSettings<T> setGenericTypeToMock(Type genericTypeToMock) {
        this.genericTypeToMock = genericTypeToMock;
        return this;
    }

//@ requires!(isEmpty && extraInterfaces.isEmpty());
    @Override
    public Set<Class<?>> getExtraInterfaces() {
        return extraInterfaces;
    }

//@ ensures extraInterfaces == null;
//@ ensures extraInterfaces.size() == 0;
    public CreationSettings<T> setExtraInterfaces(Set<Class<?>> extraInterfaces) {
        this.extraInterfaces = extraInterfaces;
        return this;
    }

//@ requires name!= null;
    public String getName() {
        return name;
    }

//@ requires numInstances() > 0;    // Or maybe == 0 is okay too?
//@ ensures this.spiedInstance == spiedInstance;
//@ requires spiedInstance!= null;
    @Override
    public Object getSpiedInstance() {
        return spiedInstance;
    }

//@ ensures \result == defaultAnswer;
    @Override
    public Answer<Object> getDefaultAnswer() {
        return defaultAnswer;
    }

//@ ensures \result == mockName;
    @Override
    public MockName getMockName() {
        return mockName;
    }

//@ ensures mockName == null;
//@ ensures this.mockName == mockName;
    public CreationSettings<T> setMockName(MockName mockName) {
        this.mockName = mockName;
        return this;
    }

//@ ensures \result == serializableMode;
    @Override
    public boolean isSerializable() {
        return serializableMode != SerializableMode.NONE;
    }

//@ ensures serializableMode == null;
//@ ensures serializableMode == null;
//@ requires options!= null;
//@ ensures serializableMode == \old(serializableMode);
//@ ensures \result == this;
    public CreationSettings<T> setSerializableMode(SerializableMode serializableMode) {
        this.serializableMode = serializableMode;
        return this;
    }

//@ ensures serializableMode == null;
//@ ensures this.serializableMode == null;
//@ requires numAttributes > 0;    // Or maybe == 0 is okay too?
//@ ensures serializableMode == null;
    @Override
    public SerializableMode getSerializableMode() {
        return serializableMode;
    }

//@ requires initialSize > 0 && sizeIncrease >= 0 && sizeMultiple >= 1;
//@ requires!(sizeIncrease == 0 && sizeMultiple == 1)
    @Override
    public List<InvocationListener> getInvocationListeners() {
        return invocationListeners;
    }

//@ requires preVerificationStartedListeners == null;
//@ requires postVerificationStartedListeners == null;
    @Override
    public List<VerificationStartedListener> getVerificationStartedListeners() {
        return verificationStartedListeners;
    }

//@ requires numLookups > 0;    // Or maybe == 0 is okay too?
//@ requires stubbingLookupListeners!= null;
    @Override
    public List<StubbingLookupListener> getStubbingLookupListeners() {
        return stubbingLookupListeners;
    }

//@ ensures \result == useConstructor;
    @Override
    public boolean isUsingConstructor() {
        return useConstructor;
    }

//@ ensures!stripAnnotations == true;
    @Override
    public boolean isStripAnnotations() {
        return stripAnnotations;
    }

//@ requires constructorArgs!= null;
    @Override
    public Object[] getConstructorArgs() {
        return constructorArgs;
    }

//@ requires classInstance == outerClassInstance;
    @Override
    public Object getOuterClassInstance() {
        return outerClassInstance;
    }

//@ ensures \result == stubOnly;
    @Override
    public boolean isStubOnly() {
        return stubOnly;
    }

//@ ensures \result == strictness;
    @Override
    public boolean isLenient() {
        return strictness == Strictness.LENIENT;
    }

//@ ensures strictness == null;
//@ ensures strictness == strictness;
    @Override
    public Strictness getStrictness() {
        return strictness;
    }

//@ requires maker!= null;
    @Override
    public String getMockMaker() {
        return mockMaker;
    }

//@ ensures \result == genericTypeToMock;
    @Override
    public Type getGenericTypeToMock() {
        return genericTypeToMock;
    }
}
