/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2019  FeatureIDE team, University of Magdeburg, Germany
 *
 * This file is part of FeatureIDE.
 *
 * FeatureIDE is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * FeatureIDE is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with FeatureIDE.  If not, see <http://www.gnu.org/licenses/>.
 *
 * See http://featureide.cs.ovgu.de/ for further information.
 */

package de.featjar.formula.analysis.sat4j.indeterminate;

import java.util.Arrays;
import java.util.List;

import de.featjar.base.computation.*;
import de.featjar.base.data.ExpandableIntegerList;
import de.featjar.base.data.Result;
import de.featjar.formula.analysis.bool.BooleanAssignment;
import de.featjar.formula.analysis.bool.BooleanClause;
import de.featjar.formula.analysis.bool.BooleanClauseList;
import de.featjar.formula.analysis.sat4j.ASAT4JAnalysis;
import de.featjar.formula.analysis.sat4j.solver.SAT4JSolutionSolver;
import de.featjar.formula.transform.CNFSlicer;
import org.sat4j.core.VecInt;



/**
 * Finds indetermined features.
 *
 * @author Sebastian Krieter
 */
public class ComputeIndeterminateSlicing extends ASAT4JAnalysis.Solution<BooleanAssignment> {

    public static final Dependency<BooleanAssignment> VARIABLES_OF_INTEREST =
            Dependency.newDependency(BooleanAssignment.class);

    public static final Dependency<Boolean> PARALLEL =
            Dependency.newDependency(Boolean.class);

    public ComputeIndeterminateSlicing(IComputation<BooleanClauseList> booleanClauseList) {
        super(booleanClauseList, new ComputeConstant<>(new BooleanAssignment()),Computations.of(false));
    }

    protected ComputeIndeterminateSlicing(ComputeIndeterminate other) {
        super(other);
    }

    @Override
    public Result<BooleanAssignment> compute(List<Object> dependencyList, Progress progress) {
        BooleanClauseList clauseList = BOOLEAN_CLAUSE_LIST.get(dependencyList);
        BooleanAssignment hiddenVariables = VARIABLES_OF_INTEREST.get(dependencyList);

        BooleanClauseList relevantClauses = new BooleanClauseList(clauseList.getVariableCount());
        VecInt potentialResultList = new VecInt();
        final ExpandableIntegerList resultList = new ExpandableIntegerList();
        variableLoop:
        for (final int variable : hiddenVariables.get()) {
            BooleanClauseList modClauseList = new BooleanClauseList(clauseList.getVariableCount());
            for (final BooleanClause clause : clauseList.getAll()) {
                    final int[] newLiterals = cleanClause(clause,variable);
                    if(newLiterals != null) {
                        if (newLiterals.length > 0) {
                            modClauseList.add(new BooleanClause(newLiterals));
                        } else {
                            potentialResultList.push(variable);
                            continue variableLoop;
                        }
                    }

            }
            final SAT4JSolutionSolver modSolver = new SAT4JSolutionSolver(modClauseList);

            final Result<Boolean> hasSolution = modSolver.hasSolution();
            if (hasSolution.valueEquals(Boolean.FALSE)) {
                potentialResultList.push(variable);
            } else if (hasSolution.isEmpty()) {
                // reportTimeout();
            } else if (hasSolution.valueEquals(Boolean.TRUE)) {
                resultList.add(variable);
            } else {
                throw new AssertionError(hasSolution);
            }
        }
        sliceLoop:
        while (!potentialResultList.isEmpty()) {
            final int literal = potentialResultList.last();
            potentialResultList.pop();
            final BooleanClauseList slicedCNF = new CNFSlicer(Computations.of(clauseList))
                    .set(CNFSlicer.VARIABLES_OF_INTEREST, hiddenVariables.removeAll(new BooleanAssignment(literal)))
                    .compute();
            relevantClauses.addAll(slicedCNF);
            for (final BooleanClause clause : slicedCNF) {
                if (hiddenVariables.containsVariable(literal)) {
                    int[] newClause = cleanClause(clause, literal);
                    if (newClause != null) {
                        if (newClause.length > 0) {
                            relevantClauses.add(new BooleanClause(newClause));
                        } else {
                            relevantClauses.clear();
                            continue sliceLoop;
                        }
                    }
                }

            }
            final SAT4JSolutionSolver modSolver = new SAT4JSolutionSolver(relevantClauses);
            final Result<Boolean> hasSolution = modSolver.hasSolution();
            if (hasSolution.valueEquals(Boolean.FALSE)) {
            } else if (hasSolution.isEmpty()) {
                System.out.println("timeout   "+ literal );;
            } else if (hasSolution.valueEquals(Boolean.TRUE)) {
                resultList.add(literal);
            } else {
                throw new AssertionError(hasSolution);
            }
            relevantClauses.clear();
        }

        return Result.of(new BooleanAssignment(resultList.toArray()));
    }

    private int[] cleanClause(BooleanClause clause, int variable) {
        if(clause.contains(variable) && clause.contains(-variable)) return null;
        return clause.removeAllVariables(variable);
    }

}