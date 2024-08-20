/*
 * Copyright (c) 2007 Mockito contributors
 * This program is made available under the terms of the MIT License.
 */
package org.mockito.internal.creation;

import java.lang.reflect.Method;
import java.lang.reflect.Modifier;

import org.mockito.internal.invocation.MockitoMethod;

public class DelegatingMethod implements MockitoMethod {

    private final Method method;
    private final Class<?>[] parameterTypes;

    public DelegatingMethod(Method method) {
        assert method != null : "Method cannot be null";
        this.method = method;
        this.parameterTypes = SuspendMethod.trimSuspendParameterTypes(method.getParameterTypes());
    }

//@ requires isOpen;
//@ ensures isOpen;
    @Override
    public Class<?>[] getExceptionTypes() {
        return method.getExceptionTypes();
    }

//@ requires methodName!= null;
//@ requires openJDK!= null;
//@ requires openJDK(methodName, openJDK,?args) &*& args!= null;
//@ ensures method == methodName;
    @Override
    public Method getJavaMethod() {
        return method;
    }

//@ requires method!= null;
    @Override
    public String getName() {
        return method.getName();
    }

//@ requires numParameters > 0;    // Or maybe == 0 is okay too?
//@ ensures parameterTypes == null;
//@ ensures parameterTypes.length == numParameters;
//@ requires 0 <= first;
//@ requires 0 <= toCopy;
//@ requires first + toCopy <= source.numInstances();
    @Override
    public Class<?>[] getParameterTypes() {
        return parameterTypes;
    }

//@ requires methodName!= null;
//@ requires parameters!= null;
//@ ensures  \result == method.getReturnType();
    @Override
    public Class<?> getReturnType() {
        return method.getReturnType();
    }

//@ requires methodName!= null;
//@ requires arity >= 0;
//@ ensures  methodName == arity == \old(methodName) && \result == true;
//@ ensures  methodName!= null;
//@ requires arity >= 0;
//@ ensures  methodName == arity == \old(methodName) && \result == true;
//@ ensures  methodName!= null;
//@ requires arity >= 0;
//@ ensures  methodName == arity == \old(methodName);
    @Override
    public boolean isVarArgs() {
        return method.isVarArgs();
    }

//@ requires method!= null;
    @Override
    public boolean isAbstract() {
        return (method.getModifiers() & Modifier.ABSTRACT) != 0;
    }

    /**
     * @return True if the input object is a DelegatingMethod which has an internal Method which is equal to the internal Method of this DelegatingMethod,
     * or if the input object is a Method which is equal to the internal Method of this DelegatingMethod.
     */
//@ requires method!= null;
    @Override
    public boolean equals(Object o) {
        if (this == o) {
            return true;
        }
        if (o instanceof DelegatingMethod) {
            DelegatingMethod that = (DelegatingMethod) o;
            return method.equals(that.method);
        } else {
            return method.equals(o);
        }
    }

//@ requires isGeneric == true;
//@ requires isIndex == true;
//@ requires first == 0 && first <= numInstances();
//@ requires second == 0 && second <= numInstances();
    @Override
    public int hashCode() {
        return method.hashCode();
    }
}
