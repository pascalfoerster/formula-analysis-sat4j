/*
 * Copyright (C) 2024 FeatJAR-Development-Team
 *
 * This file is part of FeatJAR-formula-analysis-sat4j.
 *
 * formula-analysis-sat4j is free software: you can redistribute it and/or modify it
 * under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation, either version 3.0 of the License,
 * or (at your option) any later version.
 *
 * formula-analysis-sat4j is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.
 * See the GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with formula-analysis-sat4j. If not, see <https://www.gnu.org/licenses/>.
 *
 * See <https://github.com/FeatureIDE/FeatJAR-formula-analysis-sat4j> for further information.
 */
package de.featjar.formula.analysis.sat4j.twise;

import de.featjar.base.computation.Computations;
import de.featjar.base.computation.Dependency;
import de.featjar.base.computation.IComputation;
import de.featjar.base.computation.Progress;
import de.featjar.base.data.ExpandableIntegerList;
import de.featjar.base.data.Result;
import de.featjar.formula.analysis.RuntimeContradictionException;
import de.featjar.formula.analysis.bool.BooleanAssignment;
import de.featjar.formula.analysis.bool.BooleanClauseList;
import de.featjar.formula.analysis.bool.BooleanSolution;
import de.featjar.formula.analysis.bool.BooleanSolutionList;
import de.featjar.formula.analysis.combinations.LexicographicIterator;
import de.featjar.formula.analysis.combinations.LexicographicIterator.Combination;
import de.featjar.formula.analysis.mig.solver.MIGBuilder;
import de.featjar.formula.analysis.mig.solver.ModalImplicationGraph;
import de.featjar.formula.analysis.sat4j.ASAT4JAnalysis;
import de.featjar.formula.analysis.sat4j.solver.ISelectionStrategy;
import de.featjar.formula.analysis.sat4j.solver.SAT4JSolutionSolver;
import de.featjar.formula.analysis.sat4j.solver.SAT4JSolver;
import java.util.ArrayList;
import java.util.List;
import java.util.Random;

/**
 * Calculates statistics regarding t-wise feature coverage of a set of
 * solutions.
 *
 * @author Sebastian Krieter
 */
public class TWiseCoverageComputation extends ASAT4JAnalysis<CoverageStatistic> {
    public static final Dependency<Integer> T = Dependency.newDependency(Integer.class);
    public static final Dependency<ModalImplicationGraph> MIG = Dependency.newDependency(ModalImplicationGraph.class);
    public static final Dependency<BooleanAssignment> FILTER = Dependency.newDependency(BooleanAssignment.class);
    public static final Dependency<BooleanSolutionList> SAMPLE = Dependency.newDependency(BooleanSolutionList.class);

    public class Environment {
        private final CoverageStatistic statistic = new CoverageStatistic(t);
        private final SAT4JSolutionSolver solver = initializeSolver(dependencyList);
        private final ModalImplicationGraph.Visitor visitor =
                MIG.get(dependencyList).getVisitor();
        private final ExpandableIntegerList[] selectedIndexedSolutions = new ExpandableIntegerList[t];
        private final int[] literals = new int[t];

        public CoverageStatistic getStatistic() {
            return statistic;
        }
    }

    public TWiseCoverageComputation(IComputation<BooleanClauseList> booleanClauseList) {
        super(
                booleanClauseList, //
                Computations.of(2), //
                new MIGBuilder(booleanClauseList), //
                Computations.of(new BooleanAssignment()), //
                Computations.of(new BooleanSolutionList()));
    }

    public TWiseCoverageComputation(TWiseCoverageComputation other) {
        super(other);
    }

    private ArrayList<ExpandableIntegerList> indexedSolutions;
    private ArrayList<ExpandableIntegerList> indexedRandomSolutions;
    private ArrayList<Environment> statisticList = new ArrayList<>();

    private List<Object> dependencyList;
    private int t;

    @Override
    public Result<CoverageStatistic> compute(List<Object> dependencyList, Progress progress) {
        this.dependencyList = dependencyList;
        BooleanSolutionList sample = SAMPLE.get(dependencyList);
        t = T.get(dependencyList);

        if (!sample.isEmpty()) {
            final int size = sample.get(0).get().size();
            initIndexedLists(sample, size);
            final int[] literals = TWiseCoverageComputationUtils.getFilteredLiterals(size, FILTER.get(dependencyList));
            final boolean[][] masks = TWiseCoverageComputationUtils.getMasks(t);

            LexicographicIterator.stream(t, literals.length, this::createStatistic)
                    .forEach(combo -> {
                        for (boolean[] mask : masks) {
                            for (int k = 0; k < mask.length; k++) {
                                combo.environment.literals[k] = mask[k]
                                        ? literals[combo.elementIndices[k]]
                                        : -literals[combo.elementIndices[k]];
                            }
                            if (TWiseCoverageComputationUtils.isCovered(
                                    indexedSolutions,
                                    t,
                                    combo.environment.literals,
                                    combo.environment.selectedIndexedSolutions)) {
                                combo.environment.statistic.incNumberOfCoveredConditions();
                            } else if (isCombinationInvalidMIG(combo.environment)) {
                                combo.environment.statistic.incNumberOfInvalidConditions();
                            } else if (TWiseCoverageComputationUtils.isCovered(
                                    indexedRandomSolutions,
                                    t,
                                    combo.environment.literals,
                                    combo.environment.selectedIndexedSolutions)) {
                                combo.environment.statistic.incNumberOfUncoveredConditions();
                            } else if (isCombinationInvalidSAT(combo.environment)) {
                                combo.environment.statistic.incNumberOfInvalidConditions();
                            } else {
                                combo.environment.statistic.incNumberOfUncoveredConditions();
                            }
                        }
                    });
        }
        return Result.ofOptional(statisticList.stream() //
                .map(Environment::getStatistic) //
                .reduce((s1, s2) -> s1.merge(s2)));
    }

    private void initIndexedLists(BooleanSolutionList sample, final int size) {
        final int indexedListSize = 2 * size;
        indexedSolutions = new ArrayList<>(indexedListSize);
        indexedRandomSolutions = new ArrayList<>(indexedListSize);
        for (int i = indexedListSize; i >= 0; --i) {
            indexedSolutions.add(new ExpandableIntegerList());
            indexedRandomSolutions.add(new ExpandableIntegerList());
        }
        addConfigurations(sample, indexedSolutions);
        addRandomConfigurations(initializeSolver(dependencyList), new Random(RANDOM_SEED.get(dependencyList)), (int)
                Math.ceil(30 * Math.log(size)));
    }

    private void addConfigurations(
            BooleanSolutionList sample, final ArrayList<ExpandableIntegerList> indexedSolutions) {
        int configurationIndex = 0;
        for (BooleanSolution configuration : sample) {
            TWiseCoverageComputationUtils.addConfigurations(
                    indexedSolutions, configuration.get(), configurationIndex++);
        }
    }

    private void addRandomConfigurations(SAT4JSolutionSolver solver, Random random, int limit) {
        solver.setSelectionStrategy(ISelectionStrategy.random(random));
        for (int j = 0; j < limit; j++) {
            if (solver.hasSolution().valueEquals(Boolean.TRUE)) {
                TWiseCoverageComputationUtils.addConfigurations(
                        indexedRandomSolutions, solver.getInternalSolution(), j);
                solver.shuffleOrder(random);
            } else {
                break;
            }
        }
    }

    private Environment createStatistic(Combination<Environment> combo) {
        Environment env = new Environment();
        synchronized (statisticList) {
            statisticList.add(env);
        }
        return env;
    }

    private boolean isCombinationInvalidMIG(Environment env) {
        try {
            env.visitor.propagate(env.literals);
        } catch (RuntimeContradictionException e) {
            return true;
        } finally {
            env.visitor.reset();
        }
        return false;
    }

    private boolean isCombinationInvalidSAT(Environment env) {
        final int orgAssignmentLength = env.solver.getAssignment().size();
        try {
            env.solver.getAssignment().addAll(env.literals);
            return env.solver.hasSolution().valueEquals(Boolean.FALSE);
        } finally {
            env.solver.getAssignment().clear(orgAssignmentLength);
        }
    }

    @Override
    protected SAT4JSolver newSolver(BooleanClauseList clauseList) {
        return new SAT4JSolutionSolver(clauseList);
    }
}
