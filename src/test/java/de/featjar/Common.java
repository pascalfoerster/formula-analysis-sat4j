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
package de.featjar;

import de.featjar.base.FeatJAR;
import de.featjar.base.data.Pair;
import de.featjar.base.io.IO;
import de.featjar.formula.io.FormulaFormats;
import de.featjar.formula.io.HiddenFormulaFormats;
import de.featjar.formula.structure.formula.IFormula;
import de.featjar.formula.structure.formula.connective.BiImplies;

import java.nio.file.Paths;
import java.util.List;

public class Common {

    static {
        FeatJAR.initialize();
    }

    public static IFormula loadModel(String modelPath) {
        return IO.load(Paths.get("src/test/resources/" + modelPath), FormulaFormats.getInstance())
                .orElseThrow();
    }
    public static Pair<IFormula,Pair<List<String>,List<BiImplies>>> loadHiddenModel(String modelPath) {
          return IO.load(Paths.get("src/test/resources/" + modelPath), HiddenFormulaFormats.getInstance())
                .orElseThrow();
    }
    public IFormula load(String modelPath) {
        return loadModel(modelPath);
    }
}
