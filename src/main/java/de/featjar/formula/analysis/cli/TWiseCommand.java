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
package de.featjar.formula.analysis.cli;

import de.featjar.base.cli.ICommand;
import de.featjar.base.cli.Option;
import de.featjar.base.computation.Computations;
import de.featjar.base.computation.IComputation;
import de.featjar.formula.analysis.bool.BooleanClauseList;
import de.featjar.formula.analysis.bool.BooleanRepresentationComputation;
import de.featjar.formula.analysis.bool.BooleanSolution;
import de.featjar.formula.analysis.bool.BooleanSolutionList;
import de.featjar.formula.analysis.sat4j.twise.YASA;
import de.featjar.formula.structure.formula.IFormula;
import java.util.List;

public class TWiseCommand extends ASAT4JAnalysisCommand<BooleanSolutionList, BooleanSolutionList> {

    public static final Option<Integer> LIMIT_OPTION = new Option<>("n", Option.IntegerParser) //
            .setDescription("Maximum number of configurations to be generated") //
            .setDefaultValue(Integer.MAX_VALUE);

    public static final Option<Integer> T_OPTION = new Option<>("t", Option.IntegerParser) //
            .setDescription("Value of t") //
            .setDefaultValue(2);

    public static final Option<Integer> ITERATIONS_OPTION = new Option<>("i", Option.IntegerParser) //
            .setDescription("Number of iterations") //
            .setDefaultValue(1);

    @Override
    public List<Option<?>> getOptions() {
        return ICommand.addOptions(super.getOptions(), LIMIT_OPTION, T_OPTION, ITERATIONS_OPTION);
    }

    @Override
    public String getDescription() {
        return "Computes solutions for a given formula using SAT4J";
    }

    @Override
    public IComputation<BooleanSolutionList> newAnalysis(
            BooleanRepresentationComputation<IFormula, BooleanClauseList> formula) {
        return formula.map(Computations::getKey)
                .map(YASA::new)
                .set(YASA.T, optionParser.get(T_OPTION))
                .set(YASA.CONFIGURATION_LIMIT, optionParser.get(LIMIT_OPTION))
                .set(YASA.ITERATIONS, optionParser.get(ITERATIONS_OPTION))
                .set(YASA.RANDOM_SEED, optionParser.get(RANDOM_SEED_OPTION))
                .set(YASA.SAT_TIMEOUT, optionParser.get(SAT_TIMEOUT_OPTION));
    }

    @Override
    public String serializeResult(BooleanSolutionList list) {
        StringBuilder sb = new StringBuilder();
        for (BooleanSolution booleanSolution : list) {
            sb.append("\n");
            sb.append(booleanSolution.print());
        }
        return sb.toString();
    }
}
