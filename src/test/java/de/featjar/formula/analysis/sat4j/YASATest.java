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
import static de.featjar.formula.structure.Expressions.literal;
import static de.featjar.formula.structure.Expressions.or;
import static org.junit.jupiter.api.Assertions.assertEquals;

import de.featjar.Common;
import de.featjar.base.FeatJAR;
import de.featjar.base.computation.Computations;
import de.featjar.base.computation.IComputation;
import de.featjar.formula.analysis.bool.BooleanAssignment;
import de.featjar.formula.analysis.bool.BooleanClauseList;
import de.featjar.formula.analysis.bool.BooleanSolutionList;
import de.featjar.formula.analysis.bool.ComputeBooleanRepresentation;
import de.featjar.formula.analysis.sat4j.solver.ISelectionStrategy;
import de.featjar.formula.analysis.sat4j.twise.CoverageStatistic;
import de.featjar.formula.analysis.sat4j.twise.RelativeTWiseCoverageComputation;
import de.featjar.formula.analysis.sat4j.twise.TWiseCoverageComputation;
import de.featjar.formula.analysis.sat4j.twise.TWiseStatisticGenerator;
import de.featjar.formula.analysis.sat4j.twise.YASA;
import de.featjar.formula.structure.formula.IFormula;
import de.featjar.formula.transformer.ComputeCNFFormula;
import de.featjar.formula.transformer.ComputeNNFFormula;
import java.time.Duration;
import java.util.Arrays;
import org.junit.jupiter.api.Test;

public class YASATest extends Common {

    @Test
    void formulaHas1WiseCoverage() {
        assertFullCoverageWithAllAlgorithms(or(literal("x"), literal(false, "y"), literal(false, "z")), 1);
    }

    @Test
    void gplHas1WiseCoverage() {
        assertFullCoverageWithAllAlgorithms(loadFormula("GPL/model.xml"), 1);
    }

    @Test
    void formulaHas2WiseCoverage() {
        assertFullCoverageWithAllAlgorithms(or(literal("x"), literal(false, "y"), literal(false, "z")), 2);
    }

    @Test
    void gplHas2WiseCoverage() {
        assertFullCoverageWithAllAlgorithms(loadFormula("GPL/model.xml"), 2);
    }

    @Test
    void formulaHas3WiseCoverage() {
        assertFullCoverageWithAllAlgorithms(or(literal("x"), literal(false, "y"), literal(false, "z")), 3);
    }

    @Test
    void gplHas3WiseCoverage() {
        assertFullCoverageWithAllAlgorithms(loadFormula("GPL/model.xml"), 3);
    }

    @Test
    void modelWithFreeVariablesHas1WiseCoverage() {
        assertFullCoverageWithAllAlgorithms(loadFormula("testFeatureModels/model_with_free_variables.dimacs"), 1);
    }

    @Test
    void modelWithFreeVariablesHas2WiseCoverage() {
        assertFullCoverageWithAllAlgorithms(loadFormula("testFeatureModels/model_with_free_variables.dimacs"), 2);
    }

    @Test
    void modelWithFreeVariablesHas3WiseCoverage() {
        assertFullCoverageWithAllAlgorithms(loadFormula("testFeatureModels/model_with_free_variables.dimacs"), 3);
    }

    //	@Test
    void embToolkitHas2WiseCoverage() {
        assertFullCoverage(loadFormula("EMBToolkit/model.xml"), 2);
    }

    //	@Test
    void financial_servicesHas2WiseCoverage() {
        assertFullCoverage(loadFormula("financial_services/model.xml"), 2);
    }

    //	@Test
    public void testBothCoverageRandom() {
        bothRandom(loadFormula("models_stability_light/busybox_monthlySnapshot/2007-05-20_17-12-43/clean.dimacs"));
    }

    //	@Test
    public void benchmark() {
        benchmarkCompareSample("models_stability_light/busybox_monthlySnapshot/2007-05-20_17-12-43/clean.dimacs", 2);
        benchmarkCompareSample("EMBToolkit/model.xml", 2);
    }

    //	@Test
    public void variants() {
        compareVariants(loadFormula("models_stability_light/busybox_monthlySnapshot/2007-05-20_17-12-43/clean.dimacs"));
        compareVariants(loadFormula("EMBToolkit/model.xml"));
    }

    @Test
    void gplRunsUntilTimeout() {
        testTimeout(loadFormula("GPL/model.xml"), 10);
    }

    private void testTimeout(IFormula formula, int timeoutSeconds) {
        IComputation<BooleanClauseList> clauses = getClauses(formula);
        BooleanSolutionList sample = clauses.map(YASA::new)
                .set(YASA.T, 3)
                .set(YASA.ITERATIONS, Integer.MAX_VALUE)
                .computeResult(Duration.ofSeconds(timeoutSeconds))
                .orElseThrow();
        FeatJAR.log().info("Sample Size: %d", sample.size());

        long time = System.currentTimeMillis();
        CoverageStatistic statistic1 = computeCoverageNew(3, clauses, sample);
        assertEquals(1.0, statistic1.coverage());
        FeatJAR.log().info((System.currentTimeMillis() - time) / 1000.0);
    }

    private void benchmarkCompareSample(String modelPath, int t) {
        IFormula formula = loadFormula(modelPath);
        IComputation<BooleanClauseList> clauses = getClauses(formula);

        FeatJAR.log().info("Comparing random sample (10) for %s with t = %d", modelPath, t);
        benchmarkCompare(clauses, computeRandomSample(clauses, 10), t);
        FeatJAR.log().info("Comparing random sample (100) for %s with t = %d", modelPath, t);
        benchmarkCompare(clauses, computeRandomSample(clauses, 100), t);
        FeatJAR.log().info("Comparing  %d-wise for %s with t = %d", t, modelPath, t);
        benchmarkCompare(clauses, computeSample(t, clauses), t);
    }

    private void benchmarkCompare(IComputation<BooleanClauseList> clauses, BooleanSolutionList sample, int t) {
        long time;
        time = System.currentTimeMillis();
        computeCoverageNew(t, clauses, sample);
        FeatJAR.log().info((System.currentTimeMillis() - time) / 1000.0);

        time = System.currentTimeMillis();
        computeCoverageOld(t, clauses, sample);
        FeatJAR.log().info((System.currentTimeMillis() - time) / 1000.0);
    }

    void onlyNew(IFormula formula) {
        IComputation<BooleanClauseList> clauses = getClauses(formula);
        BooleanSolutionList sample = computeSample(2, clauses);
        computeCoverageNew(2, clauses, sample);
    }

    void compareVariants(IFormula formula) {
        IComputation<BooleanClauseList> clauses = getClauses(formula);
        BooleanSolutionList sample = computeRandomSample(clauses, 10);
        computeCoverageVariants(2, clauses, sample);
    }

    private void bothRandom(IFormula formula) {
        IComputation<BooleanClauseList> clauses = getClauses(formula);
        BooleanSolutionList sample = computeRandomSample(clauses, 10);
        CoverageStatistic statistic1 = computeCoverageNew(2, clauses, sample);
        CoverageStatistic statistic3 = computeCoverageOld(2, clauses, sample);

        FeatJAR.log().info("total     %d | %d", statistic1.total(), statistic3.total());
        FeatJAR.log().info("covered   %d | %d", statistic1.covered(), statistic3.covered());
        FeatJAR.log().info("uncovered %d | %d", statistic1.uncovered(), statistic3.uncovered());
        FeatJAR.log().info("invalid   %d | %d", statistic1.invalid(), statistic3.invalid());
        assertEquals(statistic1.total(), statistic3.total());
        assertEquals(statistic1.covered(), statistic3.covered());
        assertEquals(statistic1.uncovered(), statistic3.uncovered());
        assertEquals(statistic1.invalid(), statistic3.invalid());
    }

    void onlyNewRandom(IFormula formula) {
        IComputation<BooleanClauseList> clauses = getClauses(formula);
        BooleanSolutionList sample = computeRandomSample(clauses, 10);
        computeCoverageNew(2, clauses, sample);
    }

    private BooleanSolutionList computeRandomSample(IComputation<BooleanClauseList> clauses, int size) {
        BooleanSolutionList sample = clauses.map(ComputeSolutionsSAT4J::new)
                .set(ComputeSolutionsSAT4J.SELECTION_STRATEGY, ISelectionStrategy.Strategy.FAST_RANDOM)
                .set(ComputeSolutionsSAT4J.LIMIT, size)
                .set(ComputeSolutionsSAT4J.RANDOM_SEED, 1L)
                .compute();
        return sample;
    }

    public void assertFullCoverageWithAllAlgorithms(IFormula formula, int t) {
        IComputation<BooleanClauseList> clauses = getClauses(formula);
        BooleanSolutionList sample = computeSample(t, clauses);

        CoverageStatistic statistic1 = computeCoverageNew(t, clauses, sample);
        CoverageStatistic statistic2 = computeCoverageRel(t, clauses, sample);
        CoverageStatistic statistic3 = computeCoverageOld(t, clauses, sample);

        FeatJAR.log().info("total     %d | %d | %d", statistic1.total(), statistic2.total(), statistic3.total());
        FeatJAR.log().info("covered   %d | %d | %d", statistic1.covered(), statistic2.covered(), statistic3.covered());
        FeatJAR.log()
                .info("uncovered %d | %d | %d", statistic1.uncovered(), statistic2.uncovered(), statistic3.uncovered());
        FeatJAR.log().info("invalid   %d | %d | %d", statistic1.invalid(), statistic2.invalid(), statistic3.invalid());

        assertEquals(1.0, statistic1.coverage());
        assertEquals(1.0, statistic2.coverage());
        assertEquals(1.0, statistic3.coverage());

        assertEquals(statistic1.covered(), statistic2.covered());
        assertEquals(statistic1.uncovered(), statistic2.uncovered());
        assertEquals(statistic1.invalid(), statistic2.invalid());
        assertEquals(statistic1.covered(), statistic3.covered());
        assertEquals(statistic1.uncovered(), statistic3.uncovered());
        assertEquals(statistic1.invalid(), statistic3.invalid());
    }

    private BooleanSolutionList computeSample(int t, IComputation<BooleanClauseList> clauses) {
        BooleanSolutionList sample = clauses.map(YASA::new)
                .setDependencyComputation(YASA.T, async(t))
                .compute();
        FeatJAR.log().info("Sample Size: %d", sample.size());
        return sample;
    }

    public void assertFullCoverage(IFormula formula, int t) {
        IComputation<BooleanClauseList> clauses = getClauses(formula);
        BooleanSolutionList sample = computeSample(t, clauses);

        long time = System.currentTimeMillis();
        CoverageStatistic statistic1 = computeCoverageNew(t, clauses, sample);
        assertEquals(1.0, statistic1.coverage());
        FeatJAR.log().info((System.currentTimeMillis() - time) / 1000.0);

        time = System.currentTimeMillis();
        CoverageStatistic statistic3 = computeCoverageOld(t, clauses, sample);
        assertEquals(1.0, statistic3.coverage());
        FeatJAR.log().info((System.currentTimeMillis() - time) / 1000.0);
        assertEquals(statistic1.covered(), statistic3.covered());
        assertEquals(statistic1.uncovered(), statistic3.uncovered());
        assertEquals(statistic1.invalid(), statistic3.invalid());
    }

    private CoverageStatistic computeCoverageOld(
            int t, IComputation<BooleanClauseList> clauses, BooleanSolutionList sample) {
        CoverageStatistic statistic = clauses.map(TWiseStatisticGenerator::new)
                .set(TWiseStatisticGenerator.SAMPLE, sample)
                .set(TWiseStatisticGenerator.CORE, new BooleanAssignment())
                .set(TWiseStatisticGenerator.T, t)
                .compute();
        FeatJAR.log().info("Computed Coverage (TWiseStatisticGenerator)");
        return statistic;
    }

    private CoverageStatistic computeCoverageRel(
            int t, IComputation<BooleanClauseList> clauses, BooleanSolutionList sample) {
        CoverageStatistic statistic = clauses.map(RelativeTWiseCoverageComputation::new)
                .set(RelativeTWiseCoverageComputation.SAMPLE, sample)
                .setDependencyComputation(
                        RelativeTWiseCoverageComputation.REFERENCE_SAMPLE, clauses.map(ComputeSolutionsSAT4J::new))
                .set(RelativeTWiseCoverageComputation.T, t)
                .compute();
        FeatJAR.log().info("Computed Coverage (RelativeTWiseCoverageComputation)");
        return statistic;
    }

    private CoverageStatistic computeCoverageNew(
            int t, IComputation<BooleanClauseList> clauses, BooleanSolutionList sample) {
        CoverageStatistic statistic = clauses.map(TWiseCoverageComputation::new)
                .set(TWiseCoverageComputation.SAMPLE, sample)
                .set(TWiseCoverageComputation.T, t)
                .compute();
        FeatJAR.log().info("Computed Coverage (TWiseCoverageComputation)");
        return statistic;
    }

    private void computeCoverageVariants(int t, IComputation<BooleanClauseList> clauses, BooleanSolutionList sample) {
        BooleanAssignment core = clauses.map(ComputeCoreSAT4J::new).compute();
        BooleanAssignment atomic = new BooleanAssignment(clauses.map(ComputeAtomicSetsSAT4J::new).compute().stream()
                .skip(1)
                .flatMapToInt(l -> Arrays.stream(l.get(), 1, l.get().length))
                .toArray());

        CoverageStatistic statisticNone = clauses.map(TWiseCoverageComputation::new)
                .set(TWiseCoverageComputation.SAMPLE, sample)
                .set(TWiseCoverageComputation.T, t)
                .compute();

        CoverageStatistic statisticCore = clauses.map(TWiseCoverageComputation::new)
                .set(TWiseCoverageComputation.SAMPLE, sample)
                .set(TWiseCoverageComputation.T, t)
                .set(TWiseCoverageComputation.FILTER, core)
                .compute();

        CoverageStatistic statisticAtomic = clauses.map(TWiseCoverageComputation::new)
                .set(TWiseCoverageComputation.SAMPLE, sample)
                .set(TWiseCoverageComputation.T, t)
                .set(TWiseCoverageComputation.FILTER, atomic)
                .compute();

        CoverageStatistic statisticCoreAtomic = clauses.map(TWiseCoverageComputation::new)
                .set(TWiseCoverageComputation.SAMPLE, sample)
                .set(TWiseCoverageComputation.T, t)
                .set(TWiseCoverageComputation.FILTER, new BooleanAssignment(core.addAll(atomic.get())))
                .compute();
        FeatJAR.log().info("Coverage statisticNone: %f", statisticNone.coverage());
        FeatJAR.log().info("Coverage statisticCore: %f", statisticCore.coverage());
        FeatJAR.log().info("Coverage statisticAtomic: %f", statisticAtomic.coverage());
        FeatJAR.log().info("Coverage statisticCoreAtomic: %f", statisticCoreAtomic.coverage());
    }

    private IComputation<BooleanClauseList> getClauses(IFormula formula) {
        ComputeBooleanRepresentation<IFormula, BooleanClauseList> cnf = async(formula)
                .map(ComputeNNFFormula::new)
                .map(ComputeCNFFormula::new)
                .map(ComputeBooleanRepresentation::new);
        return cnf.map(Computations::getKey);
    }
}
