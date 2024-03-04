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
package de.featjar.formula.analysis.sat4j.twise;

import de.featjar.base.data.ExpandableIntegerList;
import de.featjar.formula.analysis.bool.BooleanAssignment;
import de.featjar.formula.analysis.bool.BooleanSolution;
import de.featjar.formula.analysis.mig.solver.ModalImplicationGraph;
import java.util.ArrayList;
import java.util.Arrays;

/**
 * Common functions for t-wise coverage calculation.
 *
 * @author Sebastian Krieter
 */
public interface TWiseCoverageComputationUtils {

    static boolean[][] getMasks(int t) {
        final boolean[][] masks = new boolean[(int) Math.pow(2, t)][t];
        for (int i = 0; i < masks.length; i++) {
            final boolean[] p = masks[i];
            for (int j = 0; j < t; j++) {
                p[j] = ((i >> j) & 1) == 0;
            }
        }
        return masks;
    }

    static int[] getFilteredLiterals(final int size, BooleanAssignment filter) {
        final BooleanSolution filteredVariables = new BooleanSolution(
                size, filter.stream().map(Math::abs).distinct().toArray());
        final int[] literals = new int[size - filteredVariables.countNonZero()];
        int literalsIndex = 0;
        for (int i = 1; i <= size; i++) {
            if (!filteredVariables.containsAny(i)) {
                literals[literalsIndex++] = i;
            }
        }
        return literals;
    }

    static void addConfigurations(
            final ArrayList<ExpandableIntegerList> indexedSolutions, int[] configuration, int configurationIndex) {
        for (int i = 0; i < configuration.length; i++) {
            final int literal = configuration[i];
            if (literal != 0) {
                indexedSolutions
                        .get(ModalImplicationGraph.getVertexIndex(literal))
                        .add(configurationIndex);
            }
        }
    }

    static boolean isCovered(
            ArrayList<ExpandableIntegerList> indexedSolutions,
            int t,
            int[] literals,
            ExpandableIntegerList[] selectedIndexedSolutions) {
        if (t < 2) {
            return !indexedSolutions
                    .get(ModalImplicationGraph.getVertexIndex(literals[0]))
                    .isEmpty();
        }
        for (int i = 0; i < t; i++) {
            final ExpandableIntegerList indexedSolution =
                    indexedSolutions.get(ModalImplicationGraph.getVertexIndex(literals[i]));
            if (indexedSolution.size() == 0) {
                return false;
            }
            selectedIndexedSolutions[i] = indexedSolution;
        }
        Arrays.sort(selectedIndexedSolutions, (a, b) -> a.size() - b.size());
        final int[] ix = new int[t - 1];

        final ExpandableIntegerList i0 = selectedIndexedSolutions[0];
        final int[] ia0 = i0.toArray();
        loop:
        for (int i = 0; i < i0.size(); i++) {
            int id0 = ia0[i];
            for (int j = 1; j < t; j++) {
                final ExpandableIntegerList i1 = selectedIndexedSolutions[j];
                int binarySearch = Arrays.binarySearch(i1.toArray(), ix[j - 1], i1.size(), id0);
                if (binarySearch < 0) {
                    ix[j - 1] = -binarySearch - 1;
                    continue loop;
                } else {
                    ix[j - 1] = binarySearch;
                }
            }
            return true;
        }
        return false;
    }
}
