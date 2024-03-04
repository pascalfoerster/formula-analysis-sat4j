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

import de.featjar.base.cli.Flag;
import de.featjar.base.cli.ICommand;
import de.featjar.base.cli.Option;
import de.featjar.base.computation.Computations;
import de.featjar.base.computation.IComputation;
import de.featjar.formula.analysis.bool.BooleanClauseList;
import de.featjar.formula.analysis.bool.BooleanSolutionList;
import de.featjar.formula.analysis.bool.ComputeBooleanRepresentation;
import de.featjar.formula.analysis.sat4j.ComputeSolutionsSAT4J;
import de.featjar.formula.analysis.sat4j.solver.ISelectionStrategy;
import de.featjar.formula.structure.formula.IFormula;
import java.util.List;

public class SolutionsCommand extends ASAT4JAnalysisCommand<BooleanSolutionList, BooleanSolutionList> {

    public static final Option<Integer> LIMIT_OPTION = new Option<>("n", Option.IntegerParser) //
            .setDescription("Maximum number of configurations to be generated") //
            .setDefaultValue(1);

    public static final Option<ISelectionStrategy.Strategy> SELECTION_STRATEGY_OPTION = new Option<>(
                    "strategy", Option.valueOf(ISelectionStrategy.Strategy.class)) //
            .setDescription(String.format(
                    "Strategy to use for generating each configuration (%s)",
                    Option.possibleValues(ISelectionStrategy.Strategy.class))) //
            .setDefaultValue(ISelectionStrategy.Strategy.ORIGINAL);

    public static final Option<Boolean> FORBID_DUPLICATES_OPTION = new Flag("no-dublicates") //
            .setDescription("Forbid dublicate configurations to be generated");

    @Override
    public List<Option<?>> getOptions() {
        return ICommand.addOptions(
                super.getOptions(), LIMIT_OPTION, SELECTION_STRATEGY_OPTION, FORBID_DUPLICATES_OPTION);
    }

    @Override
    public String getDescription() {
        return "Computes solutions for a given formula using SAT4J";
    }

    @Override
    public IComputation<BooleanSolutionList> newAnalysis(
            ComputeBooleanRepresentation<IFormula, BooleanClauseList> formula) {
        return formula.map(Computations::getKey)
                .map(ComputeSolutionsSAT4J::new)
                .set(
                        ComputeSolutionsSAT4J.FORBID_DUPLICATES,
                        optionParser.getResult(FORBID_DUPLICATES_OPTION).get())
                .set(
                        ComputeSolutionsSAT4J.LIMIT,
                        optionParser.getResult(LIMIT_OPTION).get())
                .set(
                        ComputeSolutionsSAT4J.SELECTION_STRATEGY,
                        optionParser.getResult(SELECTION_STRATEGY_OPTION).get())
                .set(
                        ComputeSolutionsSAT4J.RANDOM_SEED,
                        optionParser.getResult(RANDOM_SEED_OPTION).get())
                .set(
                        ComputeSolutionsSAT4J.SAT_TIMEOUT,
                        optionParser.getResult(SAT_TIMEOUT_OPTION).get());
    }

    @Override
    public String serializeResult(BooleanSolutionList list) {
        return list.print();
    }
}
