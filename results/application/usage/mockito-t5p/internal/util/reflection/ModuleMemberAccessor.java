/*
 * Copyright (c) 2020 Mockito contributors
 * This program is made available under the terms of the MIT License.
 */
package org.mockito.internal.util.reflection;

import net.bytebuddy.ClassFileVersion;
import org.mockito.plugins.MemberAccessor;

import java.lang.reflect.Constructor;
import java.lang.reflect.Field;
import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;

public class ModuleMemberAccessor implements MemberAccessor {

    private final MemberAccessor delegate;

    public ModuleMemberAccessor() {
        MemberAccessor delegate;
        try {
            delegate = delegate();
        } catch (Throwable ignored) {
            // Fallback in case Byte Buddy is not used as a mock maker and not available on the
            // class loader.
            delegate = new ReflectionMemberAccessor();
        }
        this.delegate = delegate;
    }

//@ ensures \result!= null;
    private static MemberAccessor delegate() {
        if (ClassFileVersion.ofThisVm().isAtLeast(ClassFileVersion.JAVA_V9)) {
            return new InstrumentationMemberAccessor();
        } else {
            return new ReflectionMemberAccessor();
        }
    }

//@ requires requires constructor!= null && arguments!= null;
    @Override
    public Object newInstance(Constructor<?> constructor, Object... arguments)
            throws InstantiationException, InvocationTargetException, IllegalAccessException {
        return delegate.newInstance(constructor, arguments);
    }

//@ requires constructor!= null && onConstruction!= null;
//@ requires (\forall int i; 0 <= i && i < arguments.length; arguments[i]!= null);
    @Override
    public Object newInstance(
            Constructor<?> constructor, OnConstruction onConstruction, Object... arguments)
            throws InstantiationException, InvocationTargetException, IllegalAccessException {
        return delegate.newInstance(constructor, onConstruction, arguments);
    }

//@ requires method!= null;
//@ requires target!= null;
//@ requires (\forall int i; 0 <= i && i < arguments.length; 0 <= arguments[i] && arguments[i] < target.getClass());
    @Override
    public Object invoke(Method method, Object target, Object... arguments)
            throws InvocationTargetException, IllegalAccessException {
        return delegate.invoke(method, target, arguments);
    }

//@ requires delegate!= null;
    @Override
    public Object get(Field field, Object target) throws IllegalAccessException {
        return delegate.get(field, target);
    }

//@ requires field!= null;
//@ requires target!= null;
//@ requires value!= null;
    @Override
    public void set(Field field, Object target, Object value) throws IllegalAccessException {
        delegate.set(field, target, value);
    }
}
