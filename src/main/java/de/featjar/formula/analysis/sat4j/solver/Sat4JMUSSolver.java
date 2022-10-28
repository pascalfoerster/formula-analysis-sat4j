/*
 * Copyright (C) 2022 Sebastian Krieter
 *
 * This file is part of formula-analysis-sat4j.
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
package de.featjar.formula.analysis.sat4j.solver;

import de.featjar.base.data.Result;
import de.featjar.formula.analysis.solver.MUSSolver;
import de.featjar.formula.clauses.CNF;

import java.util.Collections;
import java.util.List;
import java.util.stream.Collectors;
import java.util.stream.IntStream;
import org.sat4j.minisat.SolverFactory;
import org.sat4j.specs.IConstr;
import org.sat4j.specs.ISolver;
import org.sat4j.specs.TimeoutException;
import org.sat4j.tools.xplain.Xplain;

/**
 * Implements a {@link MUSSolver} using Sat4J.
 *
 * <br>
 * <br>
 * Sat4J only support the extraction of one minimal unsatisfiable subset, thus
 * {@link #getAllMinimalUnsatisfiableSubsets()} only returns one solution.
 *
 * <br>
 * <br>
 * Note: The usage of a solver to solve expression and to find minimal
 * unsatisfiable subset should be divided into two task because the native
 * solver for the MUS extractor are substantially slower in solving
 * satisfiability requests. If for solving the usage of the {@link Sat4JSolutionSolver}
 * is recommended.
 *
 * @author Joshua Sprey
 * @author Sebastian Krieter
 */
public class Sat4JMUSSolver extends Sat4JSolver<Xplain<ISolver>> implements MUSSolver<IConstr> {
    public Sat4JMUSSolver(CNF cnf) {
        super(cnf);
    }

    @Override
    protected Xplain<ISolver> createSolver() {
        return new Xplain<>(SolverFactory.newDefault());
    }

    @Override
    public Result<List<IConstr>> getMinimalUnsatisfiableSubset() throws IllegalStateException {
        if (hasSolution().equals(Result.of(true))) {
            return Result.empty(new IllegalStateException("Problem is satisfiable"));
        }
        try {
            return Result.of(IntStream.of(solver.minimalExplanation()) //
                    .mapToObj(getSolverFormula().get()::get) //
                    .collect(Collectors.toList()));
        } catch (final TimeoutException e) {
            throw new IllegalStateException(e);
        }
    }

    @Override
    public Result<List<List<IConstr>>> getAllMinimalUnsatisfiableSubsets() throws IllegalStateException {
        return Result.of(Collections.singletonList(getMinimalUnsatisfiableSubset().get()));
    }
}