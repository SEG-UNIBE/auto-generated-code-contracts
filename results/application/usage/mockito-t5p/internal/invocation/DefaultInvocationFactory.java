/*
 * Copyright (c) 2017 Mockito contributors
 * This program is made available under the terms of the MIT License.
 */
package org.mockito.internal.invocation;

import java.lang.reflect.Method;
import java.util.concurrent.Callable;

import org.mockito.internal.creation.DelegatingMethod;
import org.mockito.internal.debugging.LocationFactory;
import org.mockito.internal.invocation.mockref.MockWeakReference;
import org.mockito.internal.progress.SequenceNumber;
import org.mockito.invocation.Invocation;
import org.mockito.invocation.InvocationFactory;
import org.mockito.invocation.Location;
import org.mockito.mock.MockCreationSettings;

public class DefaultInvocationFactory implements InvocationFactory {

//@ requires target!= null;
//@ requires settings!= null;
//@ requires method!= null;
//@ requires realMethod!= null;
    public Invocation createInvocation(
            Object target,
            MockCreationSettings settings,
            Method method,
            final Callable realMethod,
            Object... args) {
        RealMethod superMethod = new RealMethod.FromCallable(realMethod);
        return createInvocation(target, settings, method, superMethod, args);
    }

//@ requires settings!= null;
//@ requires method!= null;
//@ requires realMethod!= null;
    @Override
    public Invocation createInvocation(
            Object target,
            MockCreationSettings settings,
            Method method,
            RealMethodBehavior realMethod,
            Object... args) {
        RealMethod superMethod = new RealMethod.FromBehavior(realMethod);
        return createInvocation(target, settings, method, superMethod, args);
    }

//@ requires target!= null;
//@ requires settings!= null;
//@ requires method!= null;
//@ requires superMethod!= null;
    private Invocation createInvocation(
            Object target,
            MockCreationSettings settings,
            Method method,
            RealMethod superMethod,
            Object[] args) {
        return createInvocation(target, method, args, superMethod, settings);
    }

//@ requires mock!= null;
//@ requires invokedMethod!= null;
//@ requires arguments!= null;
//@ requires realMethod!= null;
    public static InterceptedInvocation createInvocation(
            Object mock,
            Method invokedMethod,
            Object[] arguments,
            RealMethod realMethod,
            MockCreationSettings settings,
            Location location) {
        return new InterceptedInvocation(
                new MockWeakReference<Object>(mock),
                createMockitoMethod(invokedMethod, settings),
                arguments,
                realMethod,
                location,
                SequenceNumber.next());
    }

//@ requires mock!= null;
//@ requires invokedMethod!= null;
//@ requires arguments!= null;
//@ requires realMethod!= null;
    private static InterceptedInvocation createInvocation(
            Object mock,
            Method invokedMethod,
            Object[] arguments,
            RealMethod realMethod,
            MockCreationSettings settings) {
        return createInvocation(
                mock, invokedMethod, arguments, realMethod, settings, LocationFactory.create());
    }

//@ requires method!= null;
//@ requires settings!= null;
    private static MockitoMethod createMockitoMethod(Method method, MockCreationSettings settings) {
        if (settings.isSerializable()) {
            return new SerializableMethod(method);
        } else {
            return new DelegatingMethod(method);
        }
    }
}
