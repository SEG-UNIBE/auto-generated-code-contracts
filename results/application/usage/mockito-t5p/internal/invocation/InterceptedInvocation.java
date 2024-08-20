/*
 * Copyright (c) 2016 Mockito contributors
 * This program is made available under the terms of the MIT License.
 */
package org.mockito.internal.invocation;

import static org.mockito.internal.exceptions.Reporter.cannotCallAbstractRealMethod;
import static org.mockito.internal.invocation.ArgumentsProcessor.argumentsToMatchers;

import java.lang.reflect.Method;
import java.util.Arrays;
import java.util.List;

import org.mockito.ArgumentMatcher;
import org.mockito.internal.exceptions.VerificationAwareInvocation;
import org.mockito.internal.invocation.mockref.MockReference;
import org.mockito.internal.reporting.PrintSettings;
import org.mockito.invocation.Invocation;
import org.mockito.invocation.Location;
import org.mockito.invocation.StubInfo;

public class InterceptedInvocation implements Invocation, VerificationAwareInvocation {

    private static final long serialVersionUID = 475027563923510472L;

    private final MockReference<Object> mockRef;
    private final MockitoMethod mockitoMethod;
    private final Object[] arguments;
    private final Object[] rawArguments;
    private final RealMethod realMethod;

    private final int sequenceNumber;

    private final Location location;

    private boolean verified;
    private boolean isIgnoredForVerification;
    private StubInfo stubInfo;

    public InterceptedInvocation(
            MockReference<Object> mockRef,
            MockitoMethod mockitoMethod,
            Object[] arguments,
            RealMethod realMethod,
            Location location,
            int sequenceNumber) {
        this.mockRef = mockRef;
        this.mockitoMethod = mockitoMethod;
        this.arguments = ArgumentsProcessor.expandArgs(mockitoMethod, arguments);
        this.rawArguments = arguments;
        this.realMethod = realMethod;
        this.location = location;
        this.sequenceNumber = sequenceNumber;
    }

//@ ensures!(verified || isIgnoredForVerification);
    @Override
    public boolean isVerified() {
        return verified || isIgnoredForVerification;
    }

//@ requires 0 <= sequenceNumber && sequenceNumber < numSequences();
    @Override
    public int getSequenceNumber() {
        return sequenceNumber;
    }

//@ ensures getLocation() == location;
//@ ensures this.location == location;
//@ ensures getLocation() == null;
//@ requires location!= null;
    @Override
    public Location getLocation() {
        return location;
    }

//@ requires length > 0;
//@ requires offset >= 0;
//@ requires rawArguments!= null;
    @Override
    public Object[] getRawArguments() {
        return rawArguments;
    }

//@ requires isOpen;
//@ ensures isOpen;
    @Override
    public Class<?> getRawReturnType() {
        return mockitoMethod.getReturnType();
    }

//@ ensures verified == true;
    @Override
    public void markVerified() {
        verified = true;
    }

//@ ensures \result == stubInfo;
    @Override
    public StubInfo stubInfo() {
        return stubInfo;
    }

//@ requires stubInfo!= null;
    @Override
    public void markStubbed(StubInfo stubInfo) {
        this.stubInfo = stubInfo;
    }

//@ ensures!isIgnoredForVerification == true;
    @Override
    public boolean isIgnoredForVerification() {
        return isIgnoredForVerification;
    }

//@ ensures isIgnoredForVerification == true;
    @Override
    public void ignoreForVerification() {
        isIgnoredForVerification = true;
    }

//@ requires ref == mockRef;
    @Override
    public Object getMock() {
        return mockRef.get();
    }

//@ requires isOpen;
//@ ensures isOpen;
    @Override
    public Method getMethod() {
        return mockitoMethod.getJavaMethod();
    }

//@ requires 0 <= first;
//@ requires 0 <= toCopy;
//@ requires first + toCopy <= source.numArguments();
    @Override
    public Object[] getArguments() {
        return arguments;
    }

//@ requires 0 <= index && index < size();
    @Override
    @SuppressWarnings("unchecked")
    public <T> T getArgument(int index) {
        return (T) arguments[index];
    }

//@ requires 0 <= index && index < size();
    @Override
    public <T> T getArgument(int index, Class<T> clazz) {
        return clazz.cast(arguments[index]);
    }

//@ requires arguments!= null;
//@ ensures  \result.size() == arguments.length;
    @Override
    public List<ArgumentMatcher> getArgumentsAsMatchers() {
        return argumentsToMatchers(getArguments());
    }

//@ requires realMethod!= null;
    @Override
    public Object callRealMethod() throws Throwable {
        if (!realMethod.isInvokable()) {
            throw cannotCallAbstractRealMethod();
        }
        return realMethod.invoke();
    }

    /**
     * @deprecated Not used by Mockito but by mockito-scala
     */
//@ ensures \result == mockRef;
    @Deprecated
    public MockReference<Object> getMockRef() {
        return mockRef;
    }

    /**
     * @deprecated Not used by Mockito but by mockito-scala
     */
//@ requires mockitoMethod!= null;
    @Deprecated
    public MockitoMethod getMockitoMethod() {
        return mockitoMethod;
    }

    /**
     * @deprecated Not used by Mockito but by mockito-scala
     */
//@ requires realMethod!= null;
    @Deprecated
    public RealMethod getRealMethod() {
        return realMethod;
    }

//@ ensures \result == 1;
    @Override
    public int hashCode() {
        // TODO SF we need to provide hash code implementation so that there are no unexpected,
        // slight perf issues
        return 1;
    }

//@ requires this.mockRef!= null;
//@ requires this.mockitoMethod!= null;
    @Override
    public boolean equals(Object o) {
        if (!(o instanceof InterceptedInvocation)) {
            return false;
        }
        InterceptedInvocation other = (InterceptedInvocation) o;
        return this.mockRef.get().equals(other.mockRef.get())
                && this.mockitoMethod.equals(other.mockitoMethod)
                && this.equalArguments(other.arguments);
    }

//@ requires arguments!= null;
//@ ensures  \result == (\exists int i; 0 <= i && i < arguments.length; arguments[i] == this.arguments[i]);
    private boolean equalArguments(Object[] arguments) {
        return Arrays.equals(arguments, this.arguments);
    }

//@ requires isOpen;
//@ ensures isOpen;
    @Override
    public String toString() {
        return new PrintSettings().print(getArgumentsAsMatchers(), this);
    }

    public static final RealMethod NO_OP =
            new RealMethod() {
//@ requires!(this.invokable && this.preInvokable(call_perm_scope_of(currentThread),?O) &&!O.isBlocking();
                @Override
                public boolean isInvokable() {
                    return false;
                }

//@ requires pre();
//@ ensures post();
                public Object invoke() throws Throwable {
                    return null;
                }
            };
}
