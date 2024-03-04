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
package de.featjar.formula.analysis.mig;

import de.featjar.base.computation.ComputeConstant;
import de.featjar.base.computation.Dependency;
import de.featjar.base.computation.IComputation;
import de.featjar.base.computation.Progress;
import de.featjar.base.data.Result;
import de.featjar.formula.analysis.bool.ABooleanAssignment;
import de.featjar.formula.analysis.bool.BooleanAssignment;
import de.featjar.formula.analysis.bool.BooleanClauseList;
import de.featjar.formula.analysis.bool.BooleanSolution;
import de.featjar.formula.analysis.mig.solver.ModalImplicationGraph;
import de.featjar.formula.analysis.mig.solver.ModalImplicationGraph.Visitor;
import de.featjar.formula.analysis.sat4j.solver.ISelectionStrategy;
import de.featjar.formula.analysis.sat4j.solver.SAT4JSolutionSolver;
import java.util.List;
import java.util.Random;

/**
 * Finds core and dead features using a {@link ModalImplicationGraph model implication graph}.
 *
 * @author Sebastian Krieter
 */
public class ComputeCoreDead extends ASAT4JMIGAnalysis<BooleanAssignment> {

    protected static final Dependency<BooleanAssignment> VARIABLES_OF_INTEREST =
            Dependency.newDependency(BooleanAssignment.class);

    public ComputeCoreDead(IComputation<BooleanClauseList> booleanClauseList) {
        super(booleanClauseList, new ComputeConstant<>(new BooleanAssignment()));
    }

    protected ComputeCoreDead(ComputeCoreDead other) {
        super(other);
    }

    @Override
    public Result<BooleanAssignment> compute(List<Object> dependencyList, Progress progress) {
        SAT4JSolutionSolver solver = initializeSolver(dependencyList);
        Random random = new Random(RANDOM_SEED.get(dependencyList));
        ABooleanAssignment assignment = ASSUMED_ASSIGNMENT.get(dependencyList);
        ABooleanAssignment variablesOfInterest = VARIABLES_OF_INTEREST.get(dependencyList);
        ModalImplicationGraph mig = MIG.get(dependencyList);

        solver.setSelectionStrategy(ISelectionStrategy.positive()); // TODO: fails for berkeley db
        Result<BooleanSolution> solution = solver.findSolution();
        if (solution.isEmpty()) return Result.empty();
        int[] model1 = solution.get().get();

        if (model1 != null) {
            solver.setSelectionStrategy(ISelectionStrategy.inverse(model1));

            if (!variablesOfInterest.isEmpty()) {
                final int[] model3 = new int[model1.length];
                for (int i = 0; i < variablesOfInterest.get().length; i++) {
                    final int index = variablesOfInterest.get()[i] - 1;
                    if (index >= 0) {
                        model3[index] = model1[index];
                    }
                }
                model1 = model3;
            }

            Visitor visitor = mig.getVisitor();
            visitor.propagate(assignment.get());

            int addedLiteralCount = visitor.getAddedLiteralCount();
            for (int i = 0; i < addedLiteralCount; i++) {
                model1[Math.abs(visitor.getAddedLiterals()[i]) - 1] = 0;
            }

            for (int i = 0; i < model1.length; i++) {
                final int varX = model1[i];
                if (varX != 0) {
                    solver.getAssignment().add(-varX);
                    Result<Boolean> hasSolution = solver.hasSolution();
                    if (hasSolution.valueEquals(false)) {
                        solver.getAssignment().replaceLast(varX);
                        visitor.propagate(varX);
                        for (int j = addedLiteralCount; j < visitor.getAddedLiteralCount(); j++) {
                            model1[Math.abs(visitor.getAddedLiterals()[j]) - 1] = 0;
                        }
                        addedLiteralCount = visitor.getAddedLiteralCount();
                    } else if (hasSolution.isEmpty()) {
                        solver.getAssignment().remove();
                    } else if (hasSolution.valueEquals(true)) {
                        solver.getAssignment().remove();
                        BooleanSolution.removeConflictsInplace(model1, solver.getInternalSolution());
                        solver.shuffleOrder(random);
                    }
                }
            }
        }

        return solver.createResult(solver.getAssignment().toAssignment());
    }
}
