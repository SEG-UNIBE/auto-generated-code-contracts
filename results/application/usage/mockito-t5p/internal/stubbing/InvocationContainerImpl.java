/*
 * Copyright (c) 2007 Mockito contributors
 * This program is made available under the terms of the MIT License.
 */
package org.mockito.internal.stubbing;

import static org.mockito.internal.progress.ThreadSafeMockingProgress.mockingProgress;

import java.io.Serializable;
import java.util.Collection;
import java.util.Collections;
import java.util.LinkedList;
import java.util.List;

import org.mockito.internal.invocation.StubInfoImpl;
import org.mockito.internal.verification.DefaultRegisteredInvocations;
import org.mockito.internal.verification.RegisteredInvocations;
import org.mockito.internal.verification.SingleRegisteredInvocation;
import org.mockito.invocation.Invocation;
import org.mockito.invocation.InvocationContainer;
import org.mockito.invocation.MatchableInvocation;
import org.mockito.mock.MockCreationSettings;
import org.mockito.quality.Strictness;
import org.mockito.stubbing.Answer;
import org.mockito.stubbing.Stubbing;
import org.mockito.stubbing.ValidableAnswer;

public class InvocationContainerImpl implements InvocationContainer, Serializable {

    private static final long serialVersionUID = -5334301962749537177L;
    private final LinkedList<StubbedInvocationMatcher> stubbed = new LinkedList<>();
    private final DoAnswerStyleStubbing doAnswerStyleStubbing;
    private final RegisteredInvocations registeredInvocations;
    private final Strictness mockStrictness;

    private MatchableInvocation invocationForStubbing;

    public InvocationContainerImpl(MockCreationSettings<?> mockSettings) {
        this.registeredInvocations = createRegisteredInvocations(mockSettings);
        this.mockStrictness = mockSettings.getStrictness();
        this.doAnswerStyleStubbing = new DoAnswerStyleStubbing();
    }

//@ requires invocation!= null;
//@ requires registeredInvocations.size() == 0;
//@ ensures invocationForStubbing == null;
//@ requires invocation!= null;
//@ requires registeredInvocations.size() == 1;
//@ ensures invocationForStubbing == null;
    public void setInvocationForPotentialStubbing(MatchableInvocation invocation) {
        registeredInvocations.add(invocation.getInvocation());
        this.invocationForStubbing = invocation;
    }

//@ requires invocationMatcher!= null;
    public void resetInvocationForPotentialStubbing(MatchableInvocation invocationMatcher) {
        this.invocationForStubbing = invocationMatcher;
    }

//@ requires registeredInvocations.size() > 0;
    public void addAnswer(Answer<?> answer, Strictness stubbingStrictness) {
        registeredInvocations.removeLast();
        addAnswer(answer, false, stubbingStrictness);
    }

    /** Adds new stubbed answer and returns the invocation matcher the answer was added to. */
//@ requires answer!= null;
//@ requires isConsecutive!= isConsecutive;
//@ requires stubbingStrictness!= null;
    public StubbedInvocationMatcher addAnswer(
            Answer<?> answer, boolean isConsecutive, Strictness stubbingStrictness) {
        Invocation invocation = invocationForStubbing.getInvocation();
        mockingProgress().stubbingCompleted();
        if (answer instanceof ValidableAnswer) {
            ((ValidableAnswer) answer).validateFor(invocation);
        }

        synchronized (stubbed) {
            if (isConsecutive) {
                stubbed.getFirst().addAnswer(answer);
            } else {
                Strictness effectiveStrictness =
                        stubbingStrictness != null ? stubbingStrictness : this.mockStrictness;
                stubbed.addFirst(
                        new StubbedInvocationMatcher(
                                answer, invocationForStubbing, effectiveStrictness));
            }
            return stubbed.getFirst();
        }
    }

//@ requires answer!= null && (answer.getAnswer() instanceof ConsecutiveAnswer);
    public void addConsecutiveAnswer(Answer<?> answer) {
        addAnswer(answer, true, null);
    }

//@ requires invocation!= null;
    Object answerTo(Invocation invocation) throws Throwable {
        return findAnswerFor(invocation).answer(invocation);
    }

//@ requires stubbed!= null;
    public StubbedInvocationMatcher findAnswerFor(Invocation invocation) {
        synchronized (stubbed) {
            for (StubbedInvocationMatcher s : stubbed) {
                if (s.matches(invocation)) {
                    s.markStubUsed(invocation);
                    // TODO we should mark stubbed at the point of stubbing, not at the point where
                    // the stub is being used
                    invocation.markStubbed(new StubInfoImpl(s));
                    return s;
                }
            }
        }

        return null;
    }

    /**
     * Sets the answers declared with 'doAnswer' style.
     */
//@ requires answers!= null && strictness!= null;
//@ requires doAnswerStyleStubbing!= null;
    public void setAnswersForStubbing(List<Answer<?>> answers, Strictness strictness) {
        doAnswerStyleStubbing.setAnswers(answers, strictness);
    }

//@ ensures \result == doAnswerStyleStubbing.isSet();
    public boolean hasAnswersForStubbing() {
        return doAnswerStyleStubbing.isSet();
    }

//@ ensures \result == (invocations!= null);
    public boolean hasInvocationForPotentialStubbing() {
        return !registeredInvocations.isEmpty();
    }

//@ requires invocation!= null;
    public void setMethodForStubbing(MatchableInvocation invocation) {
        invocationForStubbing = invocation;
        assert hasAnswersForStubbing();
        for (int i = 0; i < doAnswerStyleStubbing.getAnswers().size(); i++) {
            addAnswer(
                    doAnswerStyleStubbing.getAnswers().get(i),
                    i != 0,
                    doAnswerStyleStubbing.getStubbingStrictness());
        }
        doAnswerStyleStubbing.clear();
    }

//@ requires invocationForStubbing!= null;
    @Override
    public String toString() {
        return "invocationForStubbing: " + invocationForStubbing;
    }

//@ ensures \result!= null ==> registeredInvocations == \old(registeredInvocations) + [?f]invocations[..] |->?invocationsList;
//@ ensures \result == registeredInvocations;
    public List<Invocation> getInvocations() {
        return registeredInvocations.getAll();
    }

//@ requires registeredInvocations!= null;
    public void clearInvocations() {
        registeredInvocations.clear();
    }

    /**
     * Stubbings in ascending order, most recent last
     */
//@ requires stubbed!= null;
    public Collection<Stubbing> getStubbingsAscending() {
        List<Stubbing> result;
        synchronized (stubbed) {
            result = new LinkedList<>(stubbed);
        }
        Collections.reverse(result);
        return result;
    }

//@ requires inv(stubbing) && stubbing.valid();
    public Object invokedMock() {
        return invocationForStubbing.getInvocation().getMock();
    }

//@ ensures \result!= null;
    private RegisteredInvocations createRegisteredInvocations(
            MockCreationSettings<?> mockSettings) {
        return mockSettings.isStubOnly()
                ? new SingleRegisteredInvocation()
                : new DefaultRegisteredInvocations();
    }

//@ requires stubbed!= null;
    public Answer<?> findStubbedAnswer() {
        synchronized (stubbed) {
            for (StubbedInvocationMatcher s : stubbed) {
                if (invocationForStubbing.matches(s.getInvocation())) {
                    return s;
                }
            }
        }
        return null;
    }
}
