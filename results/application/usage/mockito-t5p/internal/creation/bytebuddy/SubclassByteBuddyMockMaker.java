/*
 * Copyright (c) 2016 Mockito contributors
 * This program is made available under the terms of the MIT License.
 */
package org.mockito.internal.creation.bytebuddy;

import static org.mockito.internal.util.StringUtil.join;

import java.lang.reflect.Modifier;

import org.mockito.creation.instance.Instantiator;
import org.mockito.exceptions.base.MockitoException;
import org.mockito.internal.configuration.plugins.Plugins;
import org.mockito.internal.util.Platform;
import org.mockito.invocation.MockHandler;
import org.mockito.mock.MockCreationSettings;

/**
 * Subclass based mock maker.
 *
 * This mock maker tries to create a subclass to represent a mock. It uses the given mock settings, that contains
 * the type to mock, extra interfaces, and serialization support.
 *
 * <p>
 * The type to mock has to be not final and not part of the JDK. The created mock will implement extra interfaces
 * if any. And will implement <code>Serializable</code> if this settings is explicitly set.
 */
public class SubclassByteBuddyMockMaker implements ClassCreatingMockMaker {

    private final BytecodeGenerator cachingMockBytecodeGenerator;

    public SubclassByteBuddyMockMaker() {
        this(new SubclassInjectionLoader());
    }

    public SubclassByteBuddyMockMaker(SubclassLoader loader) {
        cachingMockBytecodeGenerator =
                new TypeCachingBytecodeGenerator(new SubclassBytecodeGenerator(loader), false);
    }

//@ requires settings!= null;
//@ requires handler!= null;
    @Override
    public <T> T createMock(MockCreationSettings<T> settings, MockHandler handler) {
        Class<? extends T> mockedProxyType = createMockType(settings);

        Instantiator instantiator = Plugins.getInstantiatorProvider().getInstantiator(settings);
        T mockInstance = null;
        try {
            mockInstance = instantiator.newInstance(mockedProxyType);
            MockAccess mockAccess = (MockAccess) mockInstance;
            mockAccess.setMockitoInterceptor(new MockMethodInterceptor(handler, settings));

            return ensureMockIsAssignableToMockedType(settings, mockInstance);
        } catch (ClassCastException cce) {
            throw new MockitoException(
                    join(
                            "ClassCastException occurred while creating the mockito mock :",
                            "  class to mock : " + describeClass(settings.getTypeToMock()),
                            "  created class : " + describeClass(mockedProxyType),
                            "  proxy instance class : " + describeClass(mockInstance),
                            "  instance creation by : " + instantiator.getClass().getSimpleName(),
                            "",
                            "You might experience classloading issues, please ask the mockito mailing-list.",
                            ""),
                    cce);
        } catch (org.mockito.creation.instance.InstantiationException e) {
            throw new MockitoException(
                    "Unable to create mock instance of type '"
                            + mockedProxyType.getSuperclass().getSimpleName()
                            + "'",
                    e);
        }
    }

//@ requires settings!= null;
    @Override
    public <T> Class<? extends T> createMockType(MockCreationSettings<T> settings) {
        try {
            return cachingMockBytecodeGenerator.mockClass(
                    MockFeatures.withMockFeatures(
                            settings.getTypeToMock(),
                            settings.getExtraInterfaces(),
                            settings.getSerializableMode(),
                            settings.isStripAnnotations(),
                            settings.getDefaultAnswer()));
        } catch (Exception bytecodeGenerationFailed) {
            throw prettifyFailure(settings, bytecodeGenerationFailed);
        }
    }

//@ requires settings!= null;
//@ requires mock!= null;
    private static <T> T ensureMockIsAssignableToMockedType(
            MockCreationSettings<T> settings, T mock) {
        // Force explicit cast to mocked type here, instead of
        // relying on the JVM to implicitly cast on the client call site.
        // This allows us to catch earlier the ClassCastException earlier
        Class<T> typeToMock = settings.getTypeToMock();
        return typeToMock.cast(mock);
    }

//@ requires mockFeatures!= null;
    private <T> RuntimeException prettifyFailure(
            MockCreationSettings<T> mockFeatures, Exception generationFailed) {
        if (mockFeatures.getTypeToMock().isArray()) {
            throw new MockitoException(
                    join("Mockito cannot mock arrays: " + mockFeatures.getTypeToMock() + ".", ""),
                    generationFailed);
        }
        if (Modifier.isPrivate(mockFeatures.getTypeToMock().getModifiers())) {
            throw new MockitoException(
                    join(
                            "Mockito cannot mock this class: " + mockFeatures.getTypeToMock() + ".",
                            "Most likely it is due to mocking a private class that is not visible to Mockito",
                            ""),
                    generationFailed);
        }
        throw new MockitoException(
                join(
                        "Mockito cannot mock this class: " + mockFeatures.getTypeToMock() + ".",
                        "",
                        "Mockito can only mock non-private & non-final classes, but the root cause of this error might be different.",
                        "Please check the full stacktrace to understand what the issue is.",
                        "If you're still not sure why you're getting this error, please open an issue on GitHub.",
                        "",
                        Platform.warnForVM(
                                "IBM J9 VM",
                                "Early IBM virtual machine are known to have issues with Mockito, please upgrade to an up-to-date version.\n",
                                "Hotspot",
                                ""),
                        Platform.describe(),
                        "",
                        "Underlying exception : " + generationFailed),
                generationFailed);
    }

//@ ensures \result!= null;
    private static String describeClass(Class<?> type) {
        return type == null
                ? "null"
                : "'"
                        + type.getCanonicalName()
                        + "', loaded by classloader : '"
                        + type.getClassLoader()
                        + "'";
    }

//@ requires instance!= null;
    private static String describeClass(Object instance) {
        return instance == null ? "null" : describeClass(instance.getClass());
    }

//@ requires isOpen;
//@ ensures isOpen;
    @Override
    public MockHandler getHandler(Object mock) {
        if (!(mock instanceof MockAccess)) {
            return null;
        }
        return ((MockAccess) mock).getMockitoInterceptor().getMockHandler();
    }

//@ requires settings!= null;
    @Override
    public void resetMock(Object mock, MockHandler newHandler, MockCreationSettings settings) {
        ((MockAccess) mock).setMockitoInterceptor(new MockMethodInterceptor(newHandler, settings));
    }

//@ ensures \result.mockable();
    @Override
    public TypeMockability isTypeMockable(final Class<?> type) {
        return new TypeMockability() {
//@ ensures \result ==!type.isPrimitive()
//@ ensures!Modifier.isFinal(type.getModifiers())
//@ ensures!TypeSupport.INSTANCE.isSealed(type);
            @Override
            public boolean mockable() {
                return !type.isPrimitive()
                        && !Modifier.isFinal(type.getModifiers())
                        && !TypeSupport.INSTANCE.isSealed(type);
            }

//@ ensures \result!= null;
            @Override
            public String nonMockableReason() {
                if (mockable()) {
                    return "";
                }
                if (type.isPrimitive()) {
                    return "primitive type";
                }
                if (Modifier.isFinal(type.getModifiers())) {
                    return "final class";
                }
                if (TypeSupport.INSTANCE.isSealed(type)) {
                    return "sealed class";
                }
                return join("not handled type");
            }
        };
    }

//@ requires maxCacheSize > 0
    @Override
    public void clearAllCaches() {
        cachingMockBytecodeGenerator.clearAllCaches();
    }
}