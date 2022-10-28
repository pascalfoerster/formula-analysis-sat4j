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
package de.featjar.formula.analysis.sat4j.configuration;

import de.featjar.formula.analysis.solver.SolverContradictionException;
import de.featjar.formula.clauses.LiteralList;

/**
 * Generates all configurations for a given propositional formula.
 *
 * @author Sebastian Krieter
 */
public class AllConfigurationGenerator extends AbstractConfigurationGenerator {
    private boolean satisfiable = true;

    @Override
    public LiteralList get() {
        if (!satisfiable) {
            return null;
        }
        final LiteralList solution = solver.findSolution();
        if (solution == null) {
            satisfiable = false;
            return null;
        }
        try {
            solver.getFormula().push(solution.negate());
        } catch (final SolverContradictionException e) {
            satisfiable = false;
        }
        return solution;
    }
}