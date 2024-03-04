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

import de.featjar.base.computation.AComputation;
import de.featjar.base.computation.Computations;
import de.featjar.base.computation.Dependency;
import de.featjar.base.computation.IComputation;
import de.featjar.base.computation.Progress;
import de.featjar.base.data.ExpandableIntegerList;
import de.featjar.base.data.Result;
import de.featjar.formula.analysis.bool.BooleanAssignment;
import de.featjar.formula.analysis.bool.BooleanClauseList;
import de.featjar.formula.analysis.bool.BooleanSolution;
import de.featjar.formula.analysis.bool.BooleanSolutionList;
import de.featjar.formula.analysis.combinations.LexicographicIterator;
import de.featjar.formula.analysis.combinations.LexicographicIterator.Combination;
import java.util.ArrayList;
import java.util.List;

/**
 * Calculates statistics regarding t-wise feature coverage of a set of
 * solutions.
 *
 * @author Sebastian Krieter
 */
public class RelativeTWiseCoverageComputation extends AComputation<CoverageStatistic> {
    public static final Dependency<Integer> T = Dependency.newDependency(Integer.class);
    public static final Dependency<BooleanSolutionList> SAMPLE = Dependency.newDependency(BooleanSolutionList.class);
    public static final Dependency<BooleanAssignment> FILTER = Dependency.newDependency(BooleanAssignment.class);
    public static final Dependency<BooleanSolutionList> REFERENCE_SAMPLE =
            Dependency.newDependency(BooleanSolutionList.class);

    public class Environment {
        private final CoverageStatistic statistic = new CoverageStatistic(t);
        private final ExpandableIntegerList[] selectedIndexedSolutions = new ExpandableIntegerList[t];
        private final int[] literals = new int[t];

        public CoverageStatistic getStatistic() {
            return statistic;
        }
    }

    public RelativeTWiseCoverageComputation(IComputation<BooleanClauseList> booleanClauseList) {
        super(
                Computations.of(2), //
                Computations.of(new BooleanSolutionList()), //
                Computations.of(new BooleanAssignment()), //
                Computations.of(new BooleanSolutionList()));
    }

    public RelativeTWiseCoverageComputation(RelativeTWiseCoverageComputation other) {
        super(other);
    }

    private ArrayList<ExpandableIntegerList> indexedSolutions;
    private ArrayList<ExpandableIntegerList> indexedReferenceSolutions;
    private ArrayList<Environment> statisticList = new ArrayList<>();
    private int t;

    @Override
    public Result<CoverageStatistic> compute(List<Object> dependencyList, Progress progress) {
        BooleanSolutionList sample = SAMPLE.get(dependencyList);

        if (!sample.isEmpty()) {
            BooleanSolutionList referenceSample = REFERENCE_SAMPLE.get(dependencyList);
            t = T.get(dependencyList);
            assert referenceSample.isEmpty()
                    || sample.get(0).get().size()
                            == referenceSample.get(0).get().size();
            final int size = sample.get(0).get().size();
            initIndexedLists(sample, referenceSample, size);
            final int[] literals = TWiseCoverageComputationUtils.getFilteredLiterals(size, FILTER.get(dependencyList));
            final boolean[][] masks = TWiseCoverageComputationUtils.getMasks(t);

            LexicographicIterator.parallelStream(t, literals.length, this::createStatistic)
                    .forEach(combo -> {
                        for (boolean[] mask : masks) {
                            for (int k = 0; k < mask.length; k++) {
                                combo.environment.literals[k] = mask[k]
                                        ? literals[combo.elementIndices[k]]
                                        : -literals[combo.elementIndices[k]];
                            }
                            if (TWiseCoverageComputationUtils.isCovered(
                                    indexedReferenceSolutions,
                                    t,
                                    combo.environment.literals,
                                    combo.environment.selectedIndexedSolutions)) {
                                if (TWiseCoverageComputationUtils.isCovered(
                                        indexedSolutions,
                                        t,
                                        combo.environment.literals,
                                        combo.environment.selectedIndexedSolutions)) {
                                    combo.environment.statistic.incNumberOfCoveredConditions();
                                } else {
                                    combo.environment.statistic.incNumberOfUncoveredConditions();
                                }
                            } else {
                                combo.environment.statistic.incNumberOfInvalidConditions();
                            }
                        }
                    });
        }
        return Result.ofOptional(statisticList.stream() //
                .map(Environment::getStatistic) //
                .reduce((s1, s2) -> s1.merge(s2)));
    }

    private void initIndexedLists(BooleanSolutionList sample, BooleanSolutionList referenceSample, final int size) {
        final int indexedListSize = 2 * size;
        indexedSolutions = new ArrayList<>(indexedListSize);
        indexedReferenceSolutions = new ArrayList<>(indexedListSize);
        for (int i = indexedListSize; i >= 0; --i) {
            indexedSolutions.add(new ExpandableIntegerList());
            indexedReferenceSolutions.add(new ExpandableIntegerList());
        }
        addConfigurations(sample, indexedSolutions);
        addConfigurations(referenceSample, indexedReferenceSolutions);
    }

    private void addConfigurations(
            BooleanSolutionList sample, final ArrayList<ExpandableIntegerList> indexedSolutions) {
        int configurationIndex = 0;
        for (BooleanSolution configuration : sample) {
            TWiseCoverageComputationUtils.addConfigurations(
                    indexedSolutions, configuration.get(), configurationIndex++);
        }
    }

    private Environment createStatistic(Combination<Environment> combo) {
        Environment env = new Environment();
        synchronized (statisticList) {
            statisticList.add(env);
        }
        return env;
    }
}
