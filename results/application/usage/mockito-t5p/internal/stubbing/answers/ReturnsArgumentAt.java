/*
 * Copyright (c) 2007 Mockito contributors
 * This program is made available under the terms of the MIT License.
 */
package org.mockito.internal.stubbing.answers;

import static org.mockito.internal.exceptions.Reporter.invalidArgumentPositionRangeAtInvocationTime;
import static org.mockito.internal.exceptions.Reporter.invalidArgumentRangeAtIdentityAnswerCreationTime;
import static org.mockito.internal.exceptions.Reporter.wrongTypeOfArgumentToReturn;

import java.io.Serializable;
import java.lang.reflect.Method;

import org.mockito.invocation.Invocation;
import org.mockito.invocation.InvocationOnMock;
import org.mockito.stubbing.Answer;
import org.mockito.stubbing.ValidableAnswer;

/**
 * Returns the passed parameter identity at specified index.
 * <p>
 * <p>
 * The <code>argumentIndex</code> represents the index in the argument array of the invocation.
 * </p>
 * <p>
 * If this number equals -1 then the last argument is returned.
 * </p>
 *
 * @see org.mockito.AdditionalAnswers
 * @since 1.9.5
 */
public class ReturnsArgumentAt implements Answer<Object>, ValidableAnswer, Serializable {

    private static final long serialVersionUID = -589315085166295101L;

    public static final int LAST_ARGUMENT = -1;

    private final int wantedArgumentPosition;

    /**
     * Build the identity answer to return the argument at the given position in the argument array.
     *
     * @param wantedArgumentPosition
     *            The position of the argument identity to return in the invocation. Using <code>-1</code> indicates the last argument ({@link #LAST_ARGUMENT}).
     */
    public ReturnsArgumentAt(int wantedArgumentPosition) {
        if (wantedArgumentPosition != LAST_ARGUMENT && wantedArgumentPosition < 0) {
            throw invalidArgumentRangeAtIdentityAnswerCreationTime();
        }
        this.wantedArgumentPosition = wantedArgumentPosition;
    }

//@ requires invocation!= null && invocation.getMethod() == mockMethod;
    @Override
    public Object answer(InvocationOnMock invocation) throws Throwable {
        if (wantedArgIndexIsVarargAndSameTypeAsReturnType(invocation)) {
            // answer raw vararg array argument
            return invocation.getRawArguments()[invocation.getRawArguments().length - 1];
        }

        int argumentPosition = inferWantedArgumentPosition(invocation);
        validateIndexWithinInvocationRange(invocation, argumentPosition);

        // answer expanded argument at wanted position
        return invocation.getArgument(argumentPosition);
    }

//@ requires initialSize > 0 && sizeIncrease >= 0 && sizeMultiple >= 1;
//@ requires!(sizeIncrease == 0 && sizeMultiple == 1)
    @Override
    public void validateFor(InvocationOnMock invocationOnMock) {
        Invocation invocation = (Invocation) invocationOnMock;
        int argumentPosition = inferWantedArgumentPosition(invocation);
        validateIndexWithinTheoreticalInvocationRange(invocation, argumentPosition);
        validateArgumentTypeCompatibility(invocation, argumentPosition);
    }

//@ requires invocation!= null;
//@ requires wantedArgumentPosition >= 0;
    private int inferWantedArgumentPosition(InvocationOnMock invocation) {
        if (wantedArgumentPosition == LAST_ARGUMENT) {
            return invocation.getArguments().length - 1;
        }

        return wantedArgumentPosition;
    }

//@ requires invocation!= null;
//@ requires wantedArgumentPosition!= LAST_ARGUMENT;
    private int inferWantedRawArgumentPosition(InvocationOnMock invocation) {
        if (wantedArgumentPosition == LAST_ARGUMENT) {
            return invocation.getRawArguments().length - 1;
        }

        return wantedArgumentPosition;
    }

//@ requires invocation!= null && argumentPosition >= 0;
    private void validateIndexWithinInvocationRange(
            InvocationOnMock invocation, int argumentPosition) {

        if (invocation.getArguments().length <= argumentPosition) {
            throw invalidArgumentPositionRangeAtInvocationTime(
                    invocation, wantedArgumentPosition == LAST_ARGUMENT, wantedArgumentPosition);
        }
    }

//@ requires invocation!= null && argumentPosition >= 0;
    private void validateIndexWithinTheoreticalInvocationRange(
            InvocationOnMock invocation, int argumentPosition) {
        if (!wantedArgumentPositionIsValidForTheoreticalInvocation(invocation, argumentPosition)) {
            throw invalidArgumentPositionRangeAtInvocationTime(
                    invocation, wantedArgumentPosition == LAST_ARGUMENT, wantedArgumentPosition);
        }
    }

//@ requires invocation!= null && argumentPosition >= 0;
    private void validateArgumentTypeCompatibility(Invocation invocation, int argumentPosition) {
        InvocationInfo invocationInfo = new InvocationInfo(invocation);

        Class<?> inferredArgumentType = inferArgumentType(invocation, argumentPosition);

        if (!invocationInfo.isValidReturnType(inferredArgumentType)) {
            throw wrongTypeOfArgumentToReturn(
                    invocation,
                    invocationInfo.printMethodReturnType(),
                    inferredArgumentType,
                    wantedArgumentPosition);
        }
    }

//@ requires invocation!= null;
    private boolean wantedArgIndexIsVarargAndSameTypeAsReturnType(InvocationOnMock invocation) {
        int rawArgumentPosition = inferWantedRawArgumentPosition(invocation);
        Method method = invocation.getMethod();
        Class<?>[] parameterTypes = method.getParameterTypes();
        return method.isVarArgs()
                && rawArgumentPosition == /* vararg index */ parameterTypes.length - 1
                && method.getReturnType().isAssignableFrom(parameterTypes[rawArgumentPosition]);
    }

//@ requires invocation!= null && invocation.getMethod()!= null;
//@ requires 0 <= argumentPosition && argumentPosition < invocation.getArguments().length;
    private boolean wantedArgumentPositionIsValidForTheoreticalInvocation(
            InvocationOnMock invocation, int argumentPosition) {
        if (argumentPosition < 0) {
            return false;
        }
        if (!invocation.getMethod().isVarArgs()) {
            return invocation.getArguments().length > argumentPosition;
        }
        // for all varargs accepts positive ranges
        return true;
    }

//@ requires invocation!= null;
//@ requires argumentIndex >= 0;
//@ requires argumentIndex < parameterTypes.length;
//@ ensures \result!= null;
    private Class<?> inferArgumentType(Invocation invocation, int argumentIndex) {
        Class<?>[] parameterTypes = invocation.getMethod().getParameterTypes();

        // Easy when the method is not a vararg
        if (!invocation.getMethod().isVarArgs()) {
            Class<?> argumentType = parameterTypes[argumentIndex];
            Object argumentValue = invocation.getArgument(argumentIndex);
            // we don't want to return primitive wrapper types
            if (argumentType.isPrimitive() || argumentValue == null) {
                return argumentType;
            }

            return argumentValue.getClass();
        }

        // Now for varargs
        int varargIndex = parameterTypes.length - 1; // vararg always last

        if (argumentIndex < varargIndex) {
            // Same for non vararg arguments
            return parameterTypes[argumentIndex];
        }
        // if wanted argument is vararg
        if (wantedArgIndexIsVarargAndSameTypeAsReturnType(invocation)) {
            // return the vararg array if return type is compatible
            // because the user probably want to return the array itself if the return type is
            // compatible
            return parameterTypes[argumentIndex]; // move to MethodInfo ?
        }
        // return the type in this vararg array
        return parameterTypes[varargIndex].getComponentType();
    }
}
