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
package de.featjar.formula.analysis.sat4j;

import static de.featjar.base.computation.Computations.async;
import static de.featjar.base.computation.Computations.await;
import static de.featjar.formula.structure.Expressions.literal;
import static de.featjar.formula.structure.Expressions.or;
import static org.junit.jupiter.api.Assertions.assertNotNull;

import de.featjar.AnalysisTest;
import de.featjar.base.computation.Computations;
import de.featjar.base.computation.IComputation;
import de.featjar.formula.analysis.bool.BooleanAssignment;
import de.featjar.formula.analysis.bool.BooleanAssignmentList;
import de.featjar.formula.analysis.bool.BooleanClauseList;
import de.featjar.formula.analysis.bool.BooleanSolution;
import de.featjar.formula.analysis.bool.ComputeBooleanClauseList;
import de.featjar.formula.analysis.bool.ComputeBooleanRepresentation;
import de.featjar.formula.structure.formula.IFormula;
import de.featjar.formula.transformer.ComputeCNFFormula;
import de.featjar.formula.transformer.ComputeNNFFormula;
import org.junit.jupiter.api.Test;

public class Sat4JAnalysesTest extends AnalysisTest {

    public void getTWiseSample(IFormula formula, int t) {
        ComputeBooleanRepresentation<IFormula, BooleanClauseList> cnf = async(formula)
                .map(ComputeNNFFormula::new)
                .map(ComputeCNFFormula::new)
                .map(ComputeBooleanRepresentation::new);
        IComputation<BooleanClauseList> clauses = cnf.map(Computations::getKey);

        BooleanSolution solution = await((IComputation<BooleanSolution>) clauses.map(ComputeSolutionSAT4J::new));
        BooleanAssignment core = await((IComputation<BooleanAssignment>) clauses.map(ComputeCoreSAT4J::new));
        BooleanAssignmentList atomicSets =
                await((IComputation<BooleanAssignmentList>) clauses.map(ComputeAtomicSetsSAT4J::new));
        assertNotNull(solution);
        assertNotNull(core);
        assertNotNull(atomicSets);
    }

    @Test
    void tWiseSampleHasCorrectSize() {
        getTWiseSample(or(literal("x"), literal(false, "y"), literal(false, "z")), 2);
    }

    @Test
    void satisfiabilityIsCorrectlyComputed() {
        testSatisfiability(ComputeBooleanClauseList::new, ComputeSatisfiableSAT4J::new);
    }

    @Test
    void coreIsCorrectlyComputed() {
        testCore(ComputeBooleanClauseList::new, ComputeCoreSAT4J::new);
    }

    @Test
    void computedSolutionIsSatisfying() {
        testSolution(ComputeBooleanClauseList::new, ComputeSolutionSAT4J::new);
    }
}
