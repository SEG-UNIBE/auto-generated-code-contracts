/*
 * Copyright (c) 2007 Mockito contributors
 * This program is made available under the terms of the MIT License.
 */
package org.mockito.internal.stubbing;

import java.io.Serializable;
import java.util.ArrayList;
import java.util.List;

import org.mockito.quality.Strictness;
import org.mockito.stubbing.Answer;

/**
 * Holds answers declared using 'doAnswer' stubbing style.
 */
class DoAnswerStyleStubbing implements Serializable {

    private final List<Answer<?>> answers = new ArrayList<>();
    private Strictness stubbingStrictness;

//@ requires answers!= null && stubbingStrictness!= null;
    void setAnswers(List<Answer<?>> answers, Strictness stubbingStrictness) {
        this.stubbingStrictness = stubbingStrictness;
        this.answers.addAll(answers);
    }

//@ ensures \result == (answers.size() > 0);
    boolean isSet() {
        return answers.size() > 0;
    }

//@ ensures answers.isEmpty();
//@ ensures stubbingStrictness == null;
    void clear() {
        answers.clear();
        stubbingStrictness = null;
    }

//@ ensures \fresh(\result);
    List<Answer<?>> getAnswers() {
        return answers;
    }

//@ ensures \result == stubbingStrictness;
    Strictness getStubbingStrictness() {
        return stubbingStrictness;
    }
}
