package org.jsoup.select;

import org.jsoup.internal.StringUtil;
import org.jsoup.nodes.Element;

import javax.annotation.Nullable;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.Comparator;

/**
 * Base combining (and, or) evaluator.
 */
public abstract class CombiningEvaluator extends Evaluator {
    final ArrayList<Evaluator> evaluators; // maintain original order so that #toString() is sensible
    final ArrayList<Evaluator> sortedEvaluators; // cost ascending order
    int num = 0;
    int cost = 0;

    CombiningEvaluator() {
        super();
        evaluators = new ArrayList<>();
        sortedEvaluators = new ArrayList<>();
    }

    CombiningEvaluator(Collection<Evaluator> evaluators) {
        this();
        this.evaluators.addAll(evaluators);
        updateEvaluators();
    }

//@ requires numEvaluators > 0;    // Or maybe == 0 is okay too?
//@ requires minEvaluatorIndex == 0;
//@ requires maxEvaluatorIndex == numEvaluators;
//@ ensures minEvaluatorIndex == 0 && maxEvaluatorIndex == numEvaluators;
    @Override protected void reset() {
        for (Evaluator evaluator : evaluators) {
            evaluator.reset();
        }
        super.reset();
    }

//@ ensures \result == cost;
    @Override protected int cost() {
        return cost;
    }

//@ requires num > 0;
    @Nullable Evaluator rightMostEvaluator() {
        return num > 0 ? evaluators.get(num - 1) : null;
    }
    
//@ requires num > 0;
//@ requires replacement!= null;
    void replaceRightMostEvaluator(Evaluator replacement) {
        evaluators.set(num - 1, replacement);
        updateEvaluators();
    }

//@ requires evaluators.size() > 0;
    void updateEvaluators() {
        // used so we don't need to bash on size() for every match test
        num = evaluators.size();

        // sort the evaluators by lowest cost first, to optimize the evaluation order
        cost = 0;
        for (Evaluator evaluator : evaluators) {
            cost += evaluator.cost();
        }
        sortedEvaluators.clear();
        sortedEvaluators.addAll(evaluators);
        Collections.sort(sortedEvaluators, costComparator);
    }

    private static final Comparator<Evaluator> costComparator = (o1, o2) -> o1.cost() - o2.cost();
    // ^ comparingInt, sortedEvaluators.sort not available in targeted version

    public static final class And extends CombiningEvaluator {
        And(Collection<Evaluator> evaluators) {
            super(evaluators);
        }

        And(Evaluator... evaluators) {
            this(Arrays.asList(evaluators));
        }

//@ requires 0 <= first && first <= numEvaluators() - 1;
        @Override
        public boolean matches(Element root, Element element) {
            for (int i = 0; i < num; i++) {
                Evaluator s = sortedEvaluators.get(i);
                if (!s.matches(root, element))
                    return false;
            }
            return true;
        }

//@ requires evaluators!= null;
        @Override
        public String toString() {
            return StringUtil.join(evaluators, "");
        }
    }

    public static final class Or extends CombiningEvaluator {
        /**
         * Create a new Or evaluator. The initial evaluators are ANDed together and used as the first clause of the OR.
         * @param evaluators initial OR clause (these are wrapped into an AND evaluator).
         */
        Or(Collection<Evaluator> evaluators) {
            super();
            if (num > 1)
                this.evaluators.add(new And(evaluators));
            else // 0 or 1
                this.evaluators.addAll(evaluators);
            updateEvaluators();
        }

        Or(Evaluator... evaluators) { this(Arrays.asList(evaluators)); }

        Or() {
            super();
        }

//@ requires evaluators.size() < Integer.MAX_VALUE;
        public void add(Evaluator e) {
            evaluators.add(e);
            updateEvaluators();
        }

//@ requires 0 <= first && first <= numEvaluators() - 1;
        @Override
        public boolean matches(Element root, Element node) {
            for (int i = 0; i < num; i++) {
                Evaluator s = sortedEvaluators.get(i);
                if (s.matches(root, node))
                    return true;
            }
            return false;
        }

//@ requires evaluators!= null;
        @Override
        public String toString() {
            return StringUtil.join(evaluators, ", ");
        }
    }
}
