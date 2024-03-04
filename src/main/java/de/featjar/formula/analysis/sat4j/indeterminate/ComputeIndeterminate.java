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
package de.featjar.formula.analysis.sat4j.indeterminate;

import de.featjar.base.computation.ComputeConstant;
import de.featjar.base.computation.Dependency;
import de.featjar.base.computation.IComputation;
import de.featjar.base.computation.Progress;
import de.featjar.base.data.ExpandableIntegerList;
import de.featjar.base.data.Result;
import de.featjar.formula.analysis.bool.BooleanAssignment;
import de.featjar.formula.analysis.bool.BooleanClause;
import de.featjar.formula.analysis.bool.BooleanClauseList;
import de.featjar.formula.analysis.sat4j.ASAT4JAnalysis;
import de.featjar.formula.analysis.sat4j.solver.SAT4JSolutionSolver;

import java.util.List;
import java.util.stream.IntStream;

/**
 * Finds indeterminate features.
 *
 * @author Sebastian Krieter
 */
public class ComputeIndeterminate extends ASAT4JAnalysis.Solution<BooleanAssignment> {

    public static final Dependency<BooleanAssignment> VARIABLES_OF_INTEREST =
            Dependency.newDependency(BooleanAssignment.class);

    public ComputeIndeterminate(IComputation<BooleanClauseList> booleanClauseList) {
        super(booleanClauseList, new ComputeConstant<>(new BooleanAssignment()));
    }

    protected ComputeIndeterminate(ComputeIndeterminate other) {
        super(other);
    }

    @Override
    public Result<BooleanAssignment> compute(List<Object> dependencyList, Progress progress) {
        BooleanClauseList clauseList = BOOLEAN_CLAUSE_LIST.get(dependencyList);
        BooleanAssignment hiddenVariables = VARIABLES_OF_INTEREST.get(dependencyList);
        SAT4JSolutionSolver solver = initializeSolver(dependencyList);
        int variableSize = clauseList.getVariableCount();
        if(hiddenVariables.isEmpty()) return Result.of(new BooleanAssignment());
        solver.getClauseList().setVariableCount(variableSize+hiddenVariables.size());
        for (final BooleanClause clause: clauseList) {
            int[] removeLiterals = clause.retainAllVariables(hiddenVariables.get());
            int[] newLiterals = clause.removeAllVariables(hiddenVariables.get());
            if(newLiterals.length !=  clause.size()) {
                for (int i = 0 ;  i < removeLiterals.length ; i++) {
                    removeLiterals[i] = removeLiterals[i] > 0
                            ?  variableSize + hiddenVariables.indexOfVariable(removeLiterals[i]) + 1
                            : -variableSize - hiddenVariables.indexOfVariable(-removeLiterals[i]) - 1;
                }
                solver.getClauseList().add(new BooleanClause(IntStream.concat(IntStream.of(newLiterals),IntStream.of(removeLiterals)).toArray()));;
            }
        }
        final ExpandableIntegerList resultList = new ExpandableIntegerList();
        for (final int variable : hiddenVariables.get()) {
            int variableS = -variableSize-hiddenVariables.indexOfVariable(variable)-1;
            solver.getAssignment().add(variable);
            solver.getAssignment().add(variableS);

            final Result<Boolean> hasSolution = solver.hasSolution();
            if (hasSolution.valueEquals(Boolean.FALSE)) {
            } else if (hasSolution.isEmpty()) {
                // reportTimeout();
            } else if (hasSolution.valueEquals(Boolean.TRUE)) {
                resultList.add(variable);
            } else {
                throw new AssertionError(hasSolution);
            }
            solver.getAssignment().remove();
            solver.getAssignment().remove();
        }
        return Result.of(new BooleanAssignment(resultList.toIntStream().toArray()));
    }
}
