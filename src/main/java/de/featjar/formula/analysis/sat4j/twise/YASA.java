/*
 * Copyright (C) 2023 FeatJAR-Development-Team
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
import de.featjar.formula.analysis.RuntimeTimeoutException;
import de.featjar.formula.analysis.bool.ABooleanAssignment;
import de.featjar.formula.analysis.bool.ABooleanAssignmentList;
import de.featjar.formula.analysis.bool.BooleanAssignment;
import de.featjar.formula.analysis.bool.BooleanAssignmentList;
import de.featjar.formula.analysis.bool.BooleanClause;
import de.featjar.formula.analysis.bool.BooleanClauseList;
import de.featjar.formula.analysis.bool.BooleanSolution;
import de.featjar.formula.analysis.bool.BooleanSolutionList;
import de.featjar.formula.analysis.combinations.BinomialCalculator;
import de.featjar.formula.analysis.combinations.LexicographicIterator;
import de.featjar.formula.analysis.combinations.LexicographicIterator.Combination;
import de.featjar.formula.analysis.mig.solver.MIGBuilder;
import de.featjar.formula.analysis.mig.solver.ModalImplicationGraph;
import de.featjar.formula.analysis.mig.solver.ModalImplicationGraph.Visitor;
import de.featjar.formula.analysis.sat4j.ASAT4JAnalysis;
import de.featjar.formula.analysis.sat4j.solver.ISelectionStrategy;
import de.featjar.formula.analysis.sat4j.solver.SAT4JSolutionSolver;
import de.featjar.formula.analysis.sat4j.solver.SAT4JSolver;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;
import java.util.Map;
import java.util.Random;
import java.util.function.Function;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

/**
 * YASA sampling algorithm. Generates configurations for a given propositional
 * formula such that t-wise feature coverage is achieved.
 *
 * @author Sebastian Krieter
 */
public class YASA extends ASAT4JAnalysis<BooleanSolutionList> {

    // public static class NodeList extends ArrayList<List<BooleanClause>> {
    // private static final long serialVersionUID = 1L;
    // }
    // public static final Dependency<NodeList> NODES =
    // Dependency.newDependency(NodeList.class);

    public static final Dependency<BooleanAssignment> LITERALS = Dependency.newDependency(BooleanAssignment.class);
    public static final Dependency<Integer> T = Dependency.newDependency(Integer.class);
    public static final Dependency<Integer> CONFIGURATION_LIMIT = Dependency.newDependency(Integer.class);
    public static final Dependency<Integer> ITERATIONS = Dependency.newDependency(Integer.class);

    @SuppressWarnings("rawtypes")
    public static final Dependency<ABooleanAssignmentList> SAMPLE =
            Dependency.newDependency(ABooleanAssignmentList.class);

    public static final Dependency<ModalImplicationGraph> MIG = Dependency.newDependency(ModalImplicationGraph.class);

    public YASA(IComputation<BooleanClauseList> booleanClauseList) {
        super(
                booleanClauseList,
                Computations.of(new BooleanAssignment()),
                Computations.of(2),
                Computations.of(Integer.MAX_VALUE),
                Computations.of(2),
                Computations.of(new BooleanAssignmentList()),
                new MIGBuilder(booleanClauseList));
    }

    protected YASA(YASA other) {
        super(other);
    }

    /**
     * Converts a set of single literals into a grouped expression list.
     *
     * @param literalSet the literal set
     * @return a grouped expression list (can be used as an input for the
     *         configuration generator).
     */
    public static List<List<BooleanClause>> convertLiterals(BooleanAssignment literalSet) {
        final List<List<BooleanClause>> arrayList = new ArrayList<>(literalSet.size());
        for (final Integer literal : literalSet.get()) {
            final List<BooleanClause> clauseList = new ArrayList<>(1);
            clauseList.add(new BooleanClause(literal));
            arrayList.add(clauseList);
        }
        return arrayList;
    }

    private class PartialConfiguration extends BooleanSolution {
        private final int id;

        private Visitor visitor;
        private ArrayList<BooleanSolution> solverSolutions;

        public PartialConfiguration(PartialConfiguration config) {
            super(config);
            id = config.id;
            visitor = config.visitor.getVisitorProvider().new Visitor(config.visitor, elements);
            solverSolutions = config.solverSolutions != null ? new ArrayList<>(config.solverSolutions) : null;
        }

        public PartialConfiguration(int id, ModalImplicationGraph mig, int... newliterals) {
            super(new int[mig.size()], false);
            this.id = id;
            visitor = mig.getVisitor(this.elements);
            solverSolutions = new ArrayList<>();
            visitor.propagate(newliterals);
        }

        public void initSolutionList() {
            solutionLoop:
            for (BooleanSolution solution : randomSample) {
                final int[] solverSolutionLiterals = solution.get();
                for (int j = 0; j < visitor.getAddedLiteralCount(); j++) {
                    final int l = visitor.getAddedLiterals()[j];
                    if (solverSolutionLiterals[Math.abs(l) - 1] != l) {
                        continue solutionLoop;
                    }
                }
                solverSolutions.add(solution);
            }
        }

        public void updateSolutionList(int lastIndex) {
            if (!isComplete()) {
                for (int i = lastIndex; i < visitor.getAddedLiteralCount(); i++) {
                    final int newLiteral = visitor.getAddedLiterals()[i];
                    final int k = Math.abs(newLiteral) - 1;
                    for (int j = solverSolutions.size() - 1; j >= 0; j--) {
                        final int[] solverSolutionLiterals =
                                solverSolutions.get(j).get();
                        if (solverSolutionLiterals[k] != newLiteral) {
                            final int last = solverSolutions.size() - 1;
                            Collections.swap(solverSolutions, j, last);
                            solverSolutions.remove(last);
                        }
                    }
                }
            }
        }

        public int setLiteral(int... literals) {
            final int oldModelCount = visitor.getAddedLiteralCount();
            visitor.propagate(literals);
            return oldModelCount;
        }

        public void clear() {
            solverSolutions = null;
        }

        public boolean isComplete() {
            return visitor.getAddedLiteralCount() == numberOfVariableLiterals;
        }

        public int countLiterals() {
            return visitor.getAddedLiteralCount();
        }
    }

    public static final int GLOBAL_SOLUTION_LIMIT = 100_000;

    private int t, maxSampleSize, iterations, numberOfVariableLiterals;

    private SAT4JSolutionSolver solver;
    private BooleanClauseList cnf;
    private ModalImplicationGraph mig;
    private Random random;
    private ABooleanAssignmentList<?> inputSample;

    private final ArrayList<PartialConfiguration> candidateConfiguration = new ArrayList<>();
    private final ArrayDeque<BooleanSolution> randomSample = new ArrayDeque<>(GLOBAL_SOLUTION_LIMIT);
    private ArrayList<ExpandableIntegerList> indexedSolutions;
    private ArrayList<ExpandableIntegerList> indexedBestSolutions;
    private List<PartialConfiguration> bestSolutionList;
    private List<PartialConfiguration> solutionList;
    private ExpandableIntegerList[] selectedIndexedSolutions;

    private PartialConfiguration newConfiguration;
    private int curSolutionId;
    private boolean overLimit;

    private final List<List<BooleanClause>> presenceConditions = new ArrayList<>();

    @Override
    public Result<BooleanSolutionList> compute(List<Object> dependencyList, Progress progress) {
        t = T.get(dependencyList);
        if (t < 1) {
            throw new IllegalArgumentException(String.valueOf(t));
        }
        maxSampleSize = CONFIGURATION_LIMIT.get(dependencyList);
        iterations = ITERATIONS.get(dependencyList);
        if (iterations < 0) {
            iterations = Integer.MAX_VALUE;
        }
        random = new Random(RANDOM_SEED.get(dependencyList));

        solver = initializeSolver(dependencyList);
        mig = MIG.get(dependencyList);
        inputSample = SAMPLE.get(dependencyList);
        cnf = BOOLEAN_CLAUSE_LIST.get(dependencyList);
        BooleanAssignment variables = LITERALS.get(dependencyList);
        BooleanAssignment core = new BooleanAssignment(mig.getCore());

        solver.setSelectionStrategy(ISelectionStrategy.random(random));
        selectedIndexedSolutions = new ExpandableIntegerList[t];

        List<List<BooleanClause>> nodes;
        if (variables.isEmpty()) {
            nodes = convertLiterals(
                    new BooleanAssignment(IntStream.range(-cnf.getVariableCount(), cnf.getVariableCount() + 1)
                            .filter(i -> i != 0)
                            .toArray()));
        } else {
            nodes = convertLiterals(variables);
        }
        numberOfVariableLiterals = nodes.size() - core.countNegatives() - core.countPositives();

        expressionLoop:
        for (final List<BooleanClause> clauses : nodes) {
            final List<BooleanClause> newClauses = new ArrayList<>(clauses.size());
            for (final BooleanClause clause : clauses) {
                // If clause can be satisfied
                if (!core.containsAnyNegated(clause)) {
                    // If clause is already satisfied
                    if (core.containsAll(clause)) {
                        continue expressionLoop;
                    } else {
                        newClauses.add(new BooleanClause(clause));
                    }
                }
            }
            if (!newClauses.isEmpty()) {
                Collections.sort(newClauses, (o1, o2) -> o1.size() - o2.size());
                presenceConditions.add(newClauses);
            }
        }

        progress.setTotalSteps((int) (BinomialCalculator.computeBinomial(presenceConditions.size(), t)));

        buildCombinations(progress);
        for (int j = 1; j < iterations; j++) {
            checkCancel();
            if (overLimit) {
                buildCombinations(progress);
            } else {
                rebuildCombinations(progress);
            }
        }

        return finalizeResult();
    }

    @Override
    public Result<BooleanSolutionList> getIntermediateResult() {
        return finalizeResult();
    }

    private Result<BooleanSolutionList> finalizeResult() {
        if (bestSolutionList != null) {
            List<PartialConfiguration> solution = reduce(bestSolutionList);
            BooleanSolutionList result = new BooleanSolutionList(cnf.getVariableCount());
            for (int j = solution.size() - 1; j >= 0; j--) {
                result.add(autoComplete(solution.get(j)));
            }
            return Result.of(result);
        } else {
            return Result.empty();
        }
    }

    private void buildCombinations(Progress monitor) {
        final int[] literals = initliterals(false);
        initSolutionList();

        final int[] combinationLiterals = new int[t];
        LexicographicIterator.stream(t, presenceConditions.size()).forEach(combo -> {
            checkCancel();
            monitor.incrementCurrentStep();
            int[] next = combo.elementIndices;
            for (int i = 0; i < next.length; i++) {
                combinationLiterals[i] = literals[next[i]];
            }

            if (isCovered(combinationLiterals, indexedSolutions)) {
                return;
            }
            if (isCombinationInvalidMIG(combinationLiterals)) {
                return;
            }

            if (isCombinationValidSample(combinationLiterals)) {
                if (firstCover(combinationLiterals)) {
                    return;
                }
            } else {
                if (isCombinationInvalidSAT(combinationLiterals)) {
                    return;
                }
                addToCandidateList(combinationLiterals);
            }

            if (coverSat(combinationLiterals)) {
                return;
            }
            newConfiguration(combinationLiterals);
        });
        setBestSolutionList();
    }

    private void rebuildCombinations(Progress monitor) {
        final int[] literals = initliterals(true);
        initSolutionList();

        final int indexSize = indexedSolutions.size();
        indexedBestSolutions = new ArrayList<>(indexSize);
        for (int i = 0; i < indexSize; i++) {
            indexedBestSolutions.add(new ExpandableIntegerList());
        }
        for (PartialConfiguration solution : bestSolutionList) {
            final int[] solutionLiterals = solution.get();
            for (int i = 0; i < solutionLiterals.length; i++) {
                final int literal = solutionLiterals[i];
                if (literal != 0) {
                    indexedBestSolutions
                            .get(ModalImplicationGraph.getVertexIndex(literal))
                            .add(solution.id);
                }
            }
        }
        for (ExpandableIntegerList indexList : indexedBestSolutions) {
            indexList.sort();
        }

        final int[] combinationLiterals = new int[t];
        LexicographicIterator.stream(t, presenceConditions.size()).forEach(combo -> {
            int[] next = combo.elementIndices;
            for (int i = 0; i < next.length; i++) {
                combinationLiterals[i] = literals[next[i]];
            }

            if (isCovered(combinationLiterals, indexedSolutions)) {
                return;
            }
            if (!isCovered(combinationLiterals, indexedBestSolutions)) {
                return;
            }
            if (firstCover(combinationLiterals)) {
                return;
            }
            if (coverSat(combinationLiterals)) {
                return;
            }
            newConfiguration(combinationLiterals);
        });
        setBestSolutionList();
    }

    private void setBestSolutionList() {
        if (bestSolutionList == null || bestSolutionList.size() > solutionList.size()) {
            bestSolutionList = solutionList;
        }
    }

    private void initSolutionList() {
        curSolutionId = 0;
        overLimit = false;
        solutionList = new ArrayList<>();
        for (ABooleanAssignment config : inputSample) {
            newConfiguration(config.get());
        }
        final int indexSize = 2 * mig.size();
        indexedSolutions = new ArrayList<>(indexSize);
        for (int i2 = 0; i2 < indexSize; i2++) {
            indexedSolutions.add(new ExpandableIntegerList());
        }
    }

    private int[] initliterals(boolean shuffle) {
        if (shuffle) {
            shuffleSort();
        }
        final int[] literals = new int[presenceConditions.size()];
        for (int i1 = 0; i1 < literals.length; i1++) {
            literals[i1] = presenceConditions.get(i1).get(0).get()[0];
        }
        return literals;
    }

    private void shuffleSort() {
        final Map<Integer, List<List<BooleanClause>>> groupedPCs =
                presenceConditions.stream().collect(Collectors.groupingBy(List::size));
        for (final List<List<BooleanClause>> pcList : groupedPCs.values()) {
            Collections.shuffle(pcList, random);
        }
        final List<Map.Entry<Integer, List<List<BooleanClause>>>> shuffledPCs = new ArrayList<>(groupedPCs.entrySet());
        Collections.sort(shuffledPCs, (a, b) -> a.getKey() - b.getKey());
        presenceConditions.clear();
        for (final Map.Entry<Integer, List<List<BooleanClause>>> entry : shuffledPCs) {
            presenceConditions.addAll(entry.getValue());
        }
    }

    private boolean isCovered(int[] literals, ArrayList<ExpandableIntegerList> indexedSolutions) {
        if (t < 2) {
            return !indexedSolutions
                    .get(ModalImplicationGraph.getVertexIndex(literals[0]))
                    .isEmpty();
        }
        for (int i = 0; i < t; i++) {
            final ExpandableIntegerList indexedSolution =
                    indexedSolutions.get(ModalImplicationGraph.getVertexIndex(literals[i]));
            if (indexedSolution.size() == 0) {
                return false;
            }
            selectedIndexedSolutions[i] = indexedSolution;
        }
        Arrays.sort(selectedIndexedSolutions, (a, b) -> a.size() - b.size());
        final int[] ix = new int[t - 1];

        final ExpandableIntegerList i0 = selectedIndexedSolutions[0];
        final int[] ia0 = i0.toArray();
        loop:
        for (int i = 0; i < i0.size(); i++) {
            int id0 = ia0[i];
            for (int j = 1; j < t; j++) {
                final ExpandableIntegerList i1 = selectedIndexedSolutions[j];
                int binarySearch = Arrays.binarySearch(i1.toArray(), ix[j - 1], i1.size(), id0);
                if (binarySearch < 0) {
                    ix[j - 1] = -binarySearch - 1;
                    continue loop;
                } else {
                    ix[j - 1] = binarySearch;
                }
            }
            return true;
        }
        return false;
    }

    private void select(PartialConfiguration solution, int[] literals) {
        final int lastIndex = solution.setLiteral(literals);
        for (int i = lastIndex; i < solution.visitor.getAddedLiteralCount(); i++) {
            ExpandableIntegerList indexList = indexedSolutions.get(
                    ModalImplicationGraph.getVertexIndex(solution.visitor.getAddedLiterals()[i]));
            final int idIndex = Arrays.binarySearch(indexList.toArray(), 0, indexList.size(), solution.id);
            if (idIndex < 0) {
                indexList.add(solution.id, -(idIndex + 1));
            }
        }
        solution.updateSolutionList(lastIndex);
    }

    private boolean firstCover(int[] literals) {
        candidateConfiguration.clear();
        if (newConfiguration != null) {
            configLoop:
            for (final PartialConfiguration configuration : solutionList) {
                if (!configuration.isComplete()) {
                    final int[] literals2 = configuration.get();
                    for (int i = 0; i < newConfiguration.visitor.getAddedLiteralCount(); i++) {
                        final int l = newConfiguration.visitor.getAddedLiterals()[i];
                        if (literals2[Math.abs(l) - 1] == -l) {
                            continue configLoop;
                        }
                    }
                    if (isSelectionPossibleSol(configuration, literals)) {
                        select(configuration, literals);
                        change(configuration);
                        return true;
                    }
                    candidateConfiguration.add(configuration);
                }
            }
        } else {
            configLoop:
            for (final PartialConfiguration configuration : solutionList) {
                if (!configuration.isComplete()) {
                    final int[] literals2 = configuration.get();
                    for (int i = 0; i < literals.length; i++) {
                        final int l = literals[i];
                        if (literals2[Math.abs(l) - 1] == -l) {
                            continue configLoop;
                        }
                    }
                    if (isSelectionPossibleSol(configuration, literals)) {
                        select(configuration, literals);
                        change(configuration);
                        return true;
                    }
                    candidateConfiguration.add(configuration);
                }
            }
        }
        return false;
    }

    private void addToCandidateList(int[] literals) {
        candidateConfiguration.clear();
        if (newConfiguration != null) {
            configLoop:
            for (final PartialConfiguration configuration : solutionList) {
                if (!configuration.isComplete()) {
                    final int[] literals2 = configuration.get();
                    for (int i = 0; i < newConfiguration.visitor.getAddedLiteralCount(); i++) {
                        final int l = newConfiguration.visitor.getAddedLiterals()[i];
                        if (literals2[Math.abs(l) - 1] == -l) {
                            continue configLoop;
                        }
                    }
                    candidateConfiguration.add(configuration);
                }
            }
        } else {
            configLoop:
            for (final PartialConfiguration configuration : solutionList) {
                if (!configuration.isComplete()) {
                    final int[] literals2 = configuration.get();
                    for (int i = 0; i < literals.length; i++) {
                        final int l = literals[i];
                        if (literals2[Math.abs(l) - 1] == -l) {
                            continue configLoop;
                        }
                    }
                    candidateConfiguration.add(configuration);
                }
            }
        }
    }

    private void change(final PartialConfiguration configuration) {
        if (configuration.isComplete()) {
            configuration.clear();
        }
        Collections.sort(solutionList, (a, b) -> b.countLiterals() - a.countLiterals());
    }

    private boolean isCombinationInvalidMIG(int[] literals) {
        if (newConfiguration != null) {
            newConfiguration.visitor.reset();
            try {
                newConfiguration.visitor.propagate(literals);
            } catch (RuntimeContradictionException e) {
                newConfiguration.visitor.reset();
                return true;
            }
        } else {
            try {
                newConfiguration = new PartialConfiguration(curSolutionId++, mig, literals);
            } catch (RuntimeContradictionException e) {
                return true;
            }
        }
        return false;
    }

    private boolean isCombinationValidSample(int[] literals) {
        for (final BooleanSolution s : randomSample) {
            if (!s.containsAnyNegated(literals)) {
                return true;
            }
        }
        return false;
    }

    private boolean isCombinationInvalidSAT(int[] literals) {
        final int orgAssignmentLength = solver.getAssignment().size();
        try {
            if (newConfiguration != null) {
                for (int i = 0; i < newConfiguration.visitor.getAddedLiteralCount(); i++) {
                    solver.getAssignment().add(newConfiguration.visitor.getAddedLiterals()[i]);
                }
            } else {
                for (int i = 0; i < literals.length; i++) {
                    solver.getAssignment().add(literals[i]);
                }
            }
            Result<Boolean> hasSolution = solver.hasSolution();
            if (hasSolution.isPresent()) {
                if (hasSolution.get()) {
                    final BooleanSolution e = addSolverSolution();

                    PartialConfiguration compatibleConfiguration = null;
                    for (PartialConfiguration c : candidateConfiguration) {
                        if (!c.containsAnyNegated(e)) {
                            if (compatibleConfiguration == null) {
                                compatibleConfiguration = c;
                            } else {
                                c.solverSolutions.add(e);
                            }
                        }
                    }
                    if (compatibleConfiguration != null) {
                        select(compatibleConfiguration, literals);
                        compatibleConfiguration.solverSolutions.add(e);
                        change(compatibleConfiguration);
                        return true;
                    }
                    return false;
                } else {
                    return true;
                }
            } else {
                return true;
            }
        } finally {
            solver.getAssignment().clear(orgAssignmentLength);
        }
    }

    private boolean coverSat(int[] literals) {
        for (PartialConfiguration configuration : candidateConfiguration) {
            if (trySelectSat(configuration, literals)) {
                change(configuration);
                return true;
            }
        }
        return false;
    }

    private void newConfiguration(int[] literals) {
        if (solutionList.size() < maxSampleSize) {
            if (newConfiguration == null) {
                newConfiguration = new PartialConfiguration(curSolutionId++, mig, literals);
            }
            newConfiguration.initSolutionList();
            solutionList.add(newConfiguration);
            change(newConfiguration);
            for (int i = 0; i < newConfiguration.visitor.getAddedLiteralCount(); i++) {
                ExpandableIntegerList indexList = indexedSolutions.get(ModalImplicationGraph.getVertexIndex(
                        newConfiguration.visitor.getAddedLiterals()[i]));
                indexList.add(newConfiguration.id);
            }
        } else {
            overLimit = true;
        }
        newConfiguration = null;
    }

    private BooleanSolution autoComplete(PartialConfiguration configuration) {
        if (!configuration.isComplete()) {
            if (configuration.solverSolutions.size() > 0) {
                final int[] configuration2 =
                        configuration.solverSolutions.get(0).get();
                System.arraycopy(configuration2, 0, configuration.get(), 0, configuration.size());
                configuration.clear();
            } else {
                final int orgAssignmentSize = setUpSolver(configuration);
                try {
                    Result<Boolean> hasSolution = solver.hasSolution();
                    if (hasSolution.isPresent()) {
                        if (hasSolution.get()) {
                            final int[] internalSolution = solver.getInternalSolution();
                            System.arraycopy(internalSolution, 0, configuration.get(), 0, configuration.size());
                            configuration.clear();
                        } else {
                            throw new RuntimeContradictionException();
                        }
                    } else {
                        throw new RuntimeTimeoutException();
                    }
                } finally {
                    solver.getAssignment().clear(orgAssignmentSize);
                }
            }
        }
        return new BooleanSolution(configuration.get(), false);
    }

    private boolean isSelectionPossibleSol(PartialConfiguration configuration, int[] literals) {
        for (BooleanSolution configuration2 : configuration.solverSolutions) {
            if (!configuration2.containsAnyNegated(literals)) {
                return true;
            }
        }
        return false;
    }

    private boolean trySelectSat(PartialConfiguration configuration, final int[] literals) {
        final int oldModelCount = configuration.visitor.getAddedLiteralCount();
        try {
            configuration.visitor.propagate(literals);
        } catch (RuntimeException e) {
            configuration.visitor.reset(oldModelCount);
            return false;
        }

        final int orgAssignmentSize = setUpSolver(configuration);
        try {
            if (newConfiguration != null) {
                for (int i = 0; i < newConfiguration.visitor.getAddedLiteralCount(); i++) {
                    int l = newConfiguration.visitor.getAddedLiterals()[i];
                    if (configuration.get()[Math.abs(l) - 1] == 0) {
                        solver.getAssignment().add(l);
                    }
                }
            } else {
                for (int i = 0; i < literals.length; i++) {
                    int l = literals[i];
                    if (configuration.get()[Math.abs(l) - 1] == 0) {
                        solver.getAssignment().add(l);
                    }
                }
            }
            Result<Boolean> hasSolution = solver.hasSolution();
            if (hasSolution.isPresent()) {
                if (hasSolution.get()) {
                    final BooleanSolution e = addSolverSolution();
                    for (int i = oldModelCount; i < configuration.visitor.getAddedLiteralCount(); i++) {
                        ExpandableIntegerList indexList = indexedSolutions.get(ModalImplicationGraph.getVertexIndex(
                                configuration.visitor.getAddedLiterals()[i]));
                        final int idIndex =
                                Arrays.binarySearch(indexList.toArray(), 0, indexList.size(), configuration.id);
                        if (idIndex < 0) {
                            indexList.add(configuration.id, -(idIndex + 1));
                        }
                    }
                    configuration.updateSolutionList(oldModelCount);
                    configuration.solverSolutions.add(e);
                    return true;
                } else {
                    configuration.visitor.reset(oldModelCount);
                }
            } else {
                configuration.visitor.reset(oldModelCount);
            }
        } finally {
            solver.getAssignment().clear(orgAssignmentSize);
        }
        return false;
    }

    private BooleanSolution addSolverSolution() {
        if (randomSample.size() == GLOBAL_SOLUTION_LIMIT) {
            randomSample.removeFirst();
        }
        final int[] solution = solver.getInternalSolution();
        final BooleanSolution e = new BooleanSolution(Arrays.copyOf(solution, solution.length), false);
        randomSample.add(e);
        solver.shuffleOrder(random);
        return e;
    }

    private int setUpSolver(PartialConfiguration configuration) {
        final int orgAssignmentSize = solver.getAssignment().size();
        for (int i = 0; i < configuration.visitor.getAddedLiteralCount(); i++) {
            solver.getAssignment().add(configuration.visitor.getAddedLiterals()[i]);
        }
        return orgAssignmentSize;
    }

    @Override
    protected SAT4JSolver newSolver(BooleanClauseList clauseList) {
        return new SAT4JSolutionSolver(clauseList);
    }

    private List<PartialConfiguration> reduce(List<PartialConfiguration> solutionList) {
        if (solutionList.isEmpty()) {
            return solutionList;
        }
        final int n = solutionList.get(0).size();
        int t2 = (n < t) ? n : t;
        int nonUniqueIndex = solutionList.size();
        final Function<Combination<int[]>, int[]> environmentCreator = c -> new int[t2];

        for (int i = 0; i < nonUniqueIndex; i++) {
            PartialConfiguration config = solutionList.get(i);
            int finalNonUniqueIndex = nonUniqueIndex;

            boolean hasUnique = LexicographicIterator.parallelStream(t2, n, environmentCreator)
                    .anyMatch(combo -> {
                        final int[] configLiterals = config.get();
                        int[] literals = combo.environment;
                        for (int k = 0; k < literals.length; k++) {
                            literals[k] = configLiterals[combo.elementIndices[k]];
                        }
                        for (int j = 0; j < finalNonUniqueIndex; j++) {
                            PartialConfiguration config2 = solutionList.get(j);
                            if (config != config2 && config2.containsAll(literals)) {
                                return false;
                            }
                        }
                        return true;
                    });
            if (!hasUnique) {
                Collections.swap(solutionList, i--, --nonUniqueIndex);
            }
        }
        return solutionList.subList(0, nonUniqueIndex);
    }
}
