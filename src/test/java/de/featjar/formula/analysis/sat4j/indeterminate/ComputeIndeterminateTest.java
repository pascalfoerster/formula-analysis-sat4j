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
package de.featjar.formula.analysis.sat4j.indeterminate;

import static org.junit.jupiter.api.Assertions.assertEquals;

import de.featjar.Common;
import de.featjar.base.computation.Computations;
import de.featjar.base.computation.IComputation;
import de.featjar.base.data.Pair;
import de.featjar.formula.analysis.VariableMap;
import de.featjar.formula.analysis.bool.BooleanAssignment;
import de.featjar.formula.analysis.bool.BooleanClauseList;
import de.featjar.formula.analysis.bool.BooleanRepresentationComputation;
import de.featjar.formula.analysis.bool.IBooleanRepresentation;
import de.featjar.formula.analysis.mig.solver.MIGBuilder;
import de.featjar.formula.structure.formula.IFormula;
import de.featjar.formula.structure.formula.connective.BiImplies;
import de.featjar.formula.transformer.ComputeCNFFormula;
import de.featjar.formula.transformer.ComputeNNFFormula;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.stream.Collectors;

import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.api.Test;

public class ComputeIndeterminateTest extends Common {

    private static IComputation<IFormula> formula;
    private static ComputeCNFFormula cnfC;
    private static IComputation<IBooleanRepresentation> clauses;
    private static VariableMap variables;
    private static BooleanAssignment hiddenVariables;
    private static BooleanAssignment deadFeature = new BooleanAssignment();
    private static BooleanAssignment coreFeature = new BooleanAssignment();
    private static List<String> eIndeterminate;
    private static List<BiImplies> biImplies;


    @BeforeAll
    static void createTests(){
       Pair<IFormula,Pair<List<String>,List<BiImplies>>> model = loadHiddenModel("testFeatureModels/megasimple.xml");
//      Pair<IFormula,Pair<List<String>,List<BiImplies>>> model = loadHiddenModel("GPL/model.xml");
//        Pair<IFormula,Pair<List<String>,List<BiImplies>>> model = loadHiddenModel("testFeatureModels/testmodel.xml");
//        Pair<IFormula,Pair<List<String>,List<BiImplies>>> model = Computations.of(loadModel("testFeatureModels/simple3.xml"));
        formula = Computations.of(model.getKey());
   //     formula = Computations.of(loadModel("testFeatureModels/megasimple.xml"));
        cnfC = formula.map(ComputeNNFFormula::new)
                .map(ComputeCNFFormula::new);
        BooleanRepresentationComputation<IFormula, IBooleanRepresentation> cnf = cnfC
                .map(BooleanRepresentationComputation::new);
        clauses = cnf.map(Computations::getKey);
        variables = cnf.map(Computations::getValue).compute();
        hiddenVariables = new BooleanAssignment(model.getValue().getKey().stream().mapToInt(x-> variables.get(x).get()).toArray());
        biImplies = model.getValue().getValue();
//       eIndeterminate = new ArrayList<>(Arrays.asList("+n","+h","+q","+r")).stream().sorted().collect(Collectors.toList());
        eIndeterminate = new ArrayList<>(Arrays.asList("+f","+g","+h","+i")).stream().sorted().collect(Collectors.toList());
//          coreFeature = new BooleanAssignment(variables.get("a").get(),variables.get("d").get(),variables.get("e").get());
  //        deadFeature = new BooleanAssignment(variables.get("g").get());
  //      eIndeterminate = new ArrayList<>();

    }

    @Test
    void formulaOnlyIndeterminateAnalysis() {
        long time = System.currentTimeMillis();
        BooleanAssignment result = clauses.cast(BooleanClauseList.class)
                .map(ComputeIndeterminate::new)
                .set(ComputeIndeterminate.VARIABLES_OF_INTEREST, hiddenVariables)
                .compute();
        List<String> indeterminate = result.streamValues()
                .map(v -> (v.getValue() ? "+" : "-") + variables.get(v.getKey()).get()).sorted()
                .collect(Collectors.toCollection(ArrayList::new));
        time = System.currentTimeMillis() - time;
        System.out.println("Normal: " + time + " ns");
        assertEquals(eIndeterminate, indeterminate);
    }
    @Test
    void formulaOnlyIndeterminateSlicingAnalysis() {
        Long time = System.currentTimeMillis();
        BooleanAssignment result = clauses.cast(BooleanClauseList.class)
                .map(ComputeIndeterminateSlicing::new)
                .set(ComputeIndeterminate.VARIABLES_OF_INTEREST,hiddenVariables)
                .compute();
        List<String> indeterminate = result.streamValues()
                .map(v -> (v.getValue() ? "+" : "-") + variables.get(v.getKey()).get()).sorted()
                .collect(Collectors.toCollection(ArrayList::new));
        time = System.currentTimeMillis() -time;
        System.out.println("Slicing: "+ time+" ns");
        assertEquals(eIndeterminate, indeterminate);;
    }


    @Test
    void simplePreprocess(){
        long time = System.currentTimeMillis();
            BooleanAssignment hiddenVariables = new PreprocessIff(formula)
                    .set(PreprocessIff.VARIABLES_OF_INTEREST, ComputeIndeterminateTest.hiddenVariables)
                    .set(PreprocessIff.VARIABLE_MAP, variables)
                    .set(PreprocessIff.CORE_FEATURE,coreFeature)
                    .set(PreprocessIff.DEAD_FEATURE,deadFeature)
                    .compute();
            BooleanAssignment result = clauses.cast(BooleanClauseList.class)
                    .map(ComputeIndeterminate::new)
                    .set(ComputeIndeterminate.VARIABLES_OF_INTEREST, hiddenVariables)
                    .compute();
            List<String> indeterminate = result.streamValues()
                    .map(v -> (v.getValue() ? "+" : "-") + variables.get(v.getKey()).get()).sorted()
                    .collect(Collectors.toCollection(ArrayList::new));
        time = System.currentTimeMillis() - time;
        System.out.println("Pre2: " + time + " ns");
            assertEquals(eIndeterminate, indeterminate);
    }
    @Test
    void preprocessMem(){
        long time = System.currentTimeMillis();
            BooleanAssignment hiddenVariables = new PreprocessIffV2(formula)
                    .set(PreprocessIff.VARIABLES_OF_INTEREST, ComputeIndeterminateTest.hiddenVariables)
                    .set(PreprocessIff.VARIABLE_MAP, variables)
                    .compute();
            BooleanAssignment result = clauses.cast(BooleanClauseList.class)
                    .map(ComputeIndeterminate::new)
                    .set(ComputeIndeterminate.VARIABLES_OF_INTEREST, hiddenVariables)
                    .compute();
            List<String> indeterminate = result.streamValues()
                    .map(v -> (v.getValue() ? "+" : "-") + variables.get(v.getKey()).get()).sorted()
                    .collect(Collectors.toCollection(ArrayList::new));
            time = System.currentTimeMillis() - time;
        System.out.println("Pre: " + time + " ns");
            assertEquals(eIndeterminate, indeterminate);
    }
    @Test
    void preprocessSort(){
        long time = System.currentTimeMillis();
        BooleanAssignment hiddenVariables = new PreprocessIffSort(formula)
                .set(PreprocessIff.VARIABLES_OF_INTEREST, ComputeIndeterminateTest.hiddenVariables)
                .set(PreprocessIff.VARIABLE_MAP, variables)
                .compute();
        BooleanAssignment result = clauses.cast(BooleanClauseList.class)
                .map(ComputeIndeterminate::new)
                .set(ComputeIndeterminate.VARIABLES_OF_INTEREST, hiddenVariables)
                .compute();
        List<String> indeterminate = result.streamValues()
                .map(v -> (v.getValue() ? "+" : "-") + variables.get(v.getKey()).get()).sorted()
                .collect(Collectors.toCollection(ArrayList::new));
        time = System.currentTimeMillis() - time;
        System.out.println("PreSort: " + time + " ns");
        assertEquals(eIndeterminate, indeterminate);
    }
    @Test
    void preprocessImplicationGraph(){
        long time = System.currentTimeMillis();
        BooleanAssignment hiddenVariables = new PreprocessImGraph(Computations.of(clauses
                    .cast(BooleanClauseList.class)
                    .map(MIGBuilder::new).compute()))
                .set(PreprocessImGraph.VARIABLES_OF_INTEREST,ComputeIndeterminateTest.hiddenVariables)
                .set(PreprocessImGraph.VARIABLE_MAP,variables)
                .compute();
        BooleanAssignment result = clauses.cast(BooleanClauseList.class)
                .map(ComputeIndeterminate::new)
                .set(ComputeIndeterminate.VARIABLES_OF_INTEREST, hiddenVariables)
                .compute();
        List<String> indeterminate = result.streamValues()
                .map(v -> (v.getValue() ? "+" : "-") + variables.get(v.getKey()).get()).sorted()
                .collect(Collectors.toCollection(ArrayList::new));
        time = System.currentTimeMillis() - time;
        System.out.println("Impl: " + time + " ns");
        assertEquals(eIndeterminate, indeterminate);
    }

    @Test
    void preprocessBiComplicated(){
        long time = System.currentTimeMillis();
        BooleanAssignment hiddenVariables = new PreprocessIffComp(formula)
                .set(PreprocessIff.VARIABLES_OF_INTEREST, ComputeIndeterminateTest.hiddenVariables)
                .set(PreprocessIff.VARIABLE_MAP, variables)
                .compute();
        BooleanAssignment result = clauses.cast(BooleanClauseList.class)
                .map(ComputeIndeterminate::new)
                .set(ComputeIndeterminate.VARIABLES_OF_INTEREST, hiddenVariables)
                .compute();
        List<String> indeterminate = result.streamValues()
                .map(v -> (v.getValue() ? "+" : "-") + variables.get(v.getKey()).get()).sorted()
                .collect(Collectors.toCollection(ArrayList::new));
        time = System.currentTimeMillis() - time;
        System.out.println("PreComplicated: " + time + " ns");
        assertEquals(eIndeterminate, indeterminate);
    }
}
