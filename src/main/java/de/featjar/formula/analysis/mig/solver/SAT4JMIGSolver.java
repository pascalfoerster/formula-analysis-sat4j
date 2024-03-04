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
package de.featjar.formula.analysis.mig.solver;

import de.featjar.formula.analysis.bool.BooleanClauseList;
import de.featjar.formula.analysis.sat4j.solver.SAT4JSolutionSolver;

/**
 * Sat solver using Sat4J and MIGs.
 *
 * @author Sebastian Krieter
 */
public class SAT4JMIGSolver extends SAT4JSolutionSolver {
    public ModalImplicationGraph modalImplicationGraph;

    public SAT4JMIGSolver(BooleanClauseList clauseList, ModalImplicationGraph modalImplicationGraph) {
        super(clauseList);
        this.modalImplicationGraph = modalImplicationGraph;
    }
}
