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
package de.featjar.formula.analysis.cli;

import de.featjar.base.computation.Computations;
import de.featjar.base.computation.IComputation;
import de.featjar.formula.analysis.bool.BooleanAssignmentList;
import de.featjar.formula.analysis.bool.BooleanClauseList;
import de.featjar.formula.analysis.bool.BooleanSolutionList;
import de.featjar.formula.analysis.bool.ComputeBooleanRepresentation;
import de.featjar.formula.analysis.sat4j.ComputeAtomicSetsSAT4J;
import de.featjar.formula.structure.formula.IFormula;

public class AtomicSetsCommand extends ASAT4JAnalysisCommand<BooleanAssignmentList, BooleanSolutionList> {

    @Override
    public String getDescription() {
        return "Computes atomic sets for a given formula using SAT4J";
    }

    @Override
    public IComputation<BooleanAssignmentList> newAnalysis(
            ComputeBooleanRepresentation<IFormula, BooleanClauseList> formula) {
        return formula.map(Computations::getKey).map(ComputeAtomicSetsSAT4J::new);
    }

    @Override
    public String serializeResult(BooleanAssignmentList list) {
        return list.print();
    }
}
