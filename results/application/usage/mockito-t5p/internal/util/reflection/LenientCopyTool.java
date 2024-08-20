/*
 * Copyright (c) 2007 Mockito contributors
 * This program is made available under the terms of the MIT License.
 */
package org.mockito.internal.util.reflection;

import org.mockito.internal.configuration.plugins.Plugins;
import org.mockito.plugins.MemberAccessor;

import java.lang.reflect.Field;
import java.lang.reflect.Modifier;

public class LenientCopyTool {

    MemberAccessor accessor = Plugins.getMemberAccessor();

//@ requires from!= null && mock!= null;
    public <T> void copyToMock(T from, T mock) {
        copy(from, mock, from.getClass());
    }

//@ requires from!= null && to!= null;
//@ requires \nonnullelements(from.getClass());
//@ requires \nonnullelements(to.getClass());
    public <T> void copyToRealObject(T from, T to) {
        copy(from, to, from.getClass());
    }

//@ requires fromClazz!= null;
//@ requires toClazz!= null;
    private <T> void copy(T from, T to, Class<?> fromClazz) {
        while (fromClazz != Object.class) {
            copyValues(from, to, fromClazz);
            fromClazz = fromClazz.getSuperclass();
        }
    }

//@ requires classFrom!= null;
    private <T> void copyValues(T from, T mock, Class<?> classFrom) {
        Field[] fields = classFrom.getDeclaredFields();

        for (Field field : fields) {
            // ignore static fields
            if (Modifier.isStatic(field.getModifiers())) {
                continue;
            }
            try {
                Object value = accessor.get(field, from);
                accessor.set(field, mock, value);
            } catch (Throwable t) {
                // Ignore - be lenient - if some field cannot be copied then let's be it
            }
        }
    }
}
