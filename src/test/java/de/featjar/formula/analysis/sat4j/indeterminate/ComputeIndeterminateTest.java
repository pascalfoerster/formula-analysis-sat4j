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

import static de.featjar.base.computation.Computations.await;
import static org.junit.jupiter.api.Assertions.assertEquals;

import de.featjar.Common;
import de.featjar.base.computation.Computations;
import de.featjar.base.computation.IComputation;
import de.featjar.base.data.Pair;
import de.featjar.base.data.Result;
import de.featjar.base.tree.Trees;
import de.featjar.formula.analysis.VariableMap;
import de.featjar.formula.analysis.bool.BooleanAssignment;
import de.featjar.formula.analysis.bool.BooleanClauseList;
import de.featjar.formula.analysis.bool.ComputeBooleanRepresentation;
import de.featjar.formula.analysis.bool.IBooleanRepresentation;
import de.featjar.formula.analysis.mig.solver.MIGBuilder;
import de.featjar.formula.analysis.mig.solver.ModalImplicationGraph;
import de.featjar.formula.analysis.sat4j.ComputeCoreSAT4J;
import de.featjar.formula.io.HiddenFormulaFormats;
import de.featjar.formula.structure.formula.IFormula;
import de.featjar.formula.structure.formula.connective.*;
import de.featjar.formula.structure.formula.predicate.Literal;
import de.featjar.formula.transformer.ComputeCNFFormula;
import de.featjar.formula.transformer.ComputeNNFFormula;

import java.util.ArrayList;
import java.util.List;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import de.featjar.formula.visitor.CoreDeadSimplifier;
import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.api.Test;

public class ComputeIndeterminateTest extends Common {

    private final static ArrayList<IComputation<IFormula>> formulas = new ArrayList<>();

    private static final ArrayList<IComputation<IBooleanRepresentation>> clauses= new ArrayList<>();
    private static final ArrayList<VariableMap> variables = new ArrayList<>();
    private static final ArrayList<BooleanAssignment> hiddenVariables = new ArrayList<>();
    private static final ArrayList<BooleanAssignment> coredeadFeatures = new ArrayList<>();
    private static final ArrayList<List<BiImplies>> biImplies = new ArrayList<>();


    @BeforeAll
    static void createTests(){
        for(int i = 1; i < 6; i++){
            Pair<IFormula,Pair<List<String>,List<BiImplies>>> model = load("testFeatureModels/testIndeterminateFeatureModels/model"+i+".xml", HiddenFormulaFormats.getInstance());
            IComputation<IFormula> formula = Computations.of(model.getKey());
            formulas.add(formula);
            ComputeBooleanRepresentation<IFormula, IBooleanRepresentation> cnf =
                    formula.map(ComputeNNFFormula::new)
                            .map(ComputeCNFFormula::new)
                            .map(ComputeBooleanRepresentation::new);
            clauses.add(cnf.map(Computations::getKey));
            VariableMap variableMap = cnf.map(Computations::getValue).compute();
            variables.add(variableMap);
            hiddenVariables.add(new BooleanAssignment(model.getValue().getKey().stream().mapToInt(x-> variableMap.get(x).get()).toArray()));
            biImplies.add(model.getValue().getValue());

        }

        coredeadFeatures.add( new BooleanAssignment(variables.get(1).get("h").get(),-variables.get(1).get("g").get()));
        coredeadFeatures.add( new BooleanAssignment(variables.get(2).get("h").get(),-variables.get(2).get("g").get()));

    }

    @Test
    void formulaOnlyIndeterminateAnalysis() {
        BooleanAssignment result = clauses.get(0).cast(BooleanClauseList.class)
            .map(ComputeIndeterminate::new)
            .set(ComputeIndeterminate.VARIABLES_OF_INTEREST, new BooleanAssignment())
            .compute();
        List<String> indeterminate = result.streamValues()
                .map(v -> variables.get(0).get(v.getKey()).get()).sorted()
                .collect(Collectors.toCollection(ArrayList::new));
        assertEquals(0, indeterminate.size());
        BooleanAssignment result2 = clauses.get(0).cast(BooleanClauseList.class)
                .map(ComputeIndeterminate::new)
                .set(ComputeIndeterminate.VARIABLES_OF_INTEREST, hiddenVariables.get(0))
                .compute();
        List<String> indeterminate2 = result2.streamValues()
                .map(v -> variables.get(0).get(v.getKey()).get()).sorted()
                .collect(Collectors.toCollection(ArrayList::new));
        assertEquals(Stream.of("d","e","f","m").sorted().collect(Collectors.toList()), indeterminate2);

        BooleanAssignment result3 = clauses.get(2).cast(BooleanClauseList.class)
                .map(ComputeIndeterminate::new)
                .set(ComputeIndeterminate.VARIABLES_OF_INTEREST, hiddenVariables.get(2))
                .compute();
        List<String> indeterminate3 = result3.streamValues()
                .map(v -> variables.get(2).get(v.getKey()).get()).sorted()
                .collect(Collectors.toCollection(ArrayList::new));
        assertEquals(Stream.of("la","ld","ma","md","na","oa","ta","tc","te","ua","uc","ue","va","wa","xa","xe","ya","yb","yc","ye","yf").sorted().collect(Collectors.toList()), indeterminate3);
    }


    @Test
    void formulaOnlyIndeterminateSlicingAnalysis() {
        BooleanAssignment result = clauses.get(0).cast(BooleanClauseList.class)
                .map(ComputeIndeterminateSlicing::new)
                .set(ComputeIndeterminateSlicing.VARIABLES_OF_INTEREST, hiddenVariables.get(0))
                .compute();
        List<String> indeterminate = result.streamValues()
                .map(v -> variables.get(0).get(v.getKey()).get()).sorted()
                .collect(Collectors.toCollection(ArrayList::new));
        assertEquals(Stream.of("d","e","f","m").sorted().collect(Collectors.toList()), indeterminate);
    }


    @Test
    void simplePreprocess() {
        BooleanAssignment hiddenVariables = new PreprocessIff(formulas.get(1))
                .set(PreprocessIff.VARIABLES_OF_INTEREST, ComputeIndeterminateTest.hiddenVariables.get(1))
                .set(PreprocessIff.VARIABLE_MAP, variables.get(1))
                .set(PreprocessIff.CORE_DEAD_FEATURE, coredeadFeatures.get(0))
                .compute();
        List<String> indeterminate = hiddenVariables.streamValues()
                .map(v ->  variables.get(1).get(v.getKey()).get()).sorted()
                .collect(Collectors.toCollection(ArrayList::new));

        assertEquals(Stream.of("bb","ca","cb","cc").sorted().collect(Collectors.toList()), indeterminate);
        BooleanAssignment hiddenVariables2 = new PreprocessIff(formulas.get(1))
                .set(PreprocessIff.VARIABLES_OF_INTEREST, ComputeIndeterminateTest.hiddenVariables.get(1))
                .set(PreprocessIff.VARIABLE_MAP, variables.get(1))
                .set(PreprocessIff.CORE_DEAD_FEATURE, new BooleanAssignment())
                .compute();
        List<String> indeterminate2 = hiddenVariables2.streamValues()
                .map(v ->  variables.get(1).get(v.getKey()).get()).sorted()
                .collect(Collectors.toCollection(ArrayList::new));

        assertEquals(Stream.of("bb","ia","cb","ca","cc").sorted().collect(Collectors.toList()), indeterminate2);
    }
    @Test
    void preprocessMem(){
        BooleanAssignment hiddenVariables = new PreprocessIffV2(formulas.get(1))
                .set(PreprocessIff.VARIABLES_OF_INTEREST, ComputeIndeterminateTest.hiddenVariables.get(1))
                .set(PreprocessIff.VARIABLE_MAP, variables.get(1))
                .set(PreprocessIff.CORE_DEAD_FEATURE,coredeadFeatures.get(0))
                .compute();
        List<String> indeterminate = hiddenVariables.streamValues()
                .map(v ->  variables.get(1).get(v.getKey()).get()).sorted()
                .collect(Collectors.toCollection(ArrayList::new));

        assertEquals(0, indeterminate.size());
        BooleanAssignment hiddenVariables2 = new PreprocessIffV2(formulas.get(2))
                .set(PreprocessIffV2.VARIABLES_OF_INTEREST, ComputeIndeterminateTest.hiddenVariables.get(2))
                .set(PreprocessIffV2.VARIABLE_MAP, variables.get(2))
                .set(PreprocessIffV2.CORE_DEAD_FEATURE, coredeadFeatures.get(1))
                .compute();
        List<String> indeterminate2 = hiddenVariables2.streamValues()
                .map(v ->  variables.get(2).get(v.getKey()).get()).sorted()
                .collect(Collectors.toCollection(ArrayList::new));

        assertEquals(Stream.of("la","ld","le","ma","md","me","na","ne","oa","od","ta","tc","te","tg","ua","uc","ue","ug","va","vd","wa","wd","xa","xe","ya","yb","yc","ye","yf","yg").sorted().collect(Collectors.toList()), indeterminate2);

    }
    @Test
    void preprocessSort(){
        BooleanAssignment hiddenVariables = new PreprocessIffSort(formulas.get(1))
                .set(PreprocessIffSort.VARIABLES_OF_INTEREST, ComputeIndeterminateTest.hiddenVariables.get(1))
                .set(PreprocessIffSort.VARIABLE_MAP, variables.get(1))
                .set(PreprocessIffSort.CORE_DEAD_FEATURE, coredeadFeatures.get(0))
                .compute();
        List<String> indeterminate = hiddenVariables.streamValues()
                .map(v ->  variables.get(1).get(v.getKey()).get()).sorted()
                .collect(Collectors.toCollection(ArrayList::new));

        assertEquals(List.of("cb"), indeterminate);
    }
    @Test
    void preprocessImplicationGraph(){
        ModalImplicationGraph modalImplicationGraph = clauses.get(3)
                .cast(BooleanClauseList.class)
                .map(MIGBuilder::new).compute();
        BooleanAssignment hiddenVariables = new PreprocessImGraph(Computations.of(modalImplicationGraph))
                .set(PreprocessImGraph.VARIABLES_OF_INTEREST,ComputeIndeterminateTest.hiddenVariables.get(3))
                .set(PreprocessImGraph.VARIABLE_MAP,variables.get(3))
                .compute();
        List<String> indeterminate = hiddenVariables.streamValues()
                .map(v ->  variables.get(3).get(v.getKey()).get()).sorted()
                .collect(Collectors.toCollection(ArrayList::new));
        assertEquals(List.of("k","m"), indeterminate);
    }

    @Test
    void preprocessBiComplicated(){
        BooleanAssignment hiddenVariables = new PreprocessIffComp(formulas.get(2))
                .set(PreprocessIffComp.VARIABLES_OF_INTEREST, ComputeIndeterminateTest.hiddenVariables.get(2))
                .set(PreprocessIffComp.VARIABLE_MAP, variables.get(2))
                .set(PreprocessIffComp.EXPRESSION_MAX_LENGTH,5)
                .set(PreprocessIffComp.CORE_DEAD_FEATURE,coredeadFeatures.get(1))
                .compute();
        List<String> indeterminate = hiddenVariables.streamValues()
                .map(v ->  variables.get(2).get(v.getKey()).get()).sorted()
                .collect(Collectors.toCollection(ArrayList::new));
        assertEquals(Stream.of("bb","ca", "cb","la","ld","ma","md","me","na","oa","od","ta","tc","te","tg","ua","uc","ue","va","vd","wa","xa","xe","ya","yb","yc","ye","yf").sorted().collect(Collectors.toList()), indeterminate);
    }

    @Test
    void preprocessBiComplicatedSort(){
        BooleanAssignment hiddenVariables = new PreprocessIffCompSort(formulas.get(2))
                .set(PreprocessIffCompSort.VARIABLES_OF_INTEREST, ComputeIndeterminateTest.hiddenVariables.get(2))
                .set(PreprocessIffCompSort.VARIABLE_MAP, variables.get(2))
                .set(PreprocessIffCompSort.EXPRESSION_MAX_LENGTH,5)
                .set(PreprocessIffCompSort.CORE_DEAD_FEATURE, coredeadFeatures.get(1))
                .compute();
        List<String> indeterminate = hiddenVariables.streamValues()
                .map(v ->  variables.get(2).get(v.getKey()).get()).sorted()
                .collect(Collectors.toCollection(ArrayList::new));
        assertEquals(Stream.of("cb","la","ld","ma","md","na","oa","od","ta","tc","te","tg","ua","uc","ue","va","wa","xa","xe","ya","yb","yc","ye","yf").sorted().collect(Collectors.toList()), indeterminate);
    }

    @Test
    void testCoreDeadSimplifier() {
        BooleanAssignment assignment = await(clauses.get(4).cast(BooleanClauseList.class).map(ComputeCoreSAT4J::new));
        IFormula formula = formulas.get(4).compute();
        formula.getChildren().get(26).getChildren().get(1).replaceChild(1,new Literal(false,"h"));

        Result<IFormula> formulaResult = Reference.mutateClone(formula, reference -> Trees.traverse(reference, new CoreDeadSimplifier(assignment.toValueName(variables.get(4)))));
        IFormula result = new And(
                new Or(new Literal("i"), new Literal("j")),
                new BiImplies(new Literal("k"), new Not(new Literal("l"))),
                new BiImplies(new Literal("l"), new Not(new Literal("k"))),
                new Implies(new Literal("n"), new Literal("m")),
                new Implies(new Literal("o"), new Literal("m")),
                new Not(new And(new Literal("f"), new Literal("g"))),
                new Or(new Literal("f"), new Literal("g")),
                new Or(new Literal("g"), new Literal("f")),
                new Or(new Literal("f"), new Literal("i")),
                new Or(new Literal("f"), new Literal("g")),
                new Or(new Literal("f"), new Literal("g")),
                new Not(new And(new Literal("n"), new And(new Literal("o"),new Literal("h")))),
                new BiImplies(new Literal("m"), new Literal("h")),
                new Or(new Literal("f"), new Literal("g")),
                new Or(new Literal("f"), new Literal("g"))


                );
        assert result.equalsTree(formulaResult.get());


    }

    @Test
    void testBiImplicationTransformer(){
        IFormula cnf = formulas.get(3).map(ComputeNNFFormula::new).map(ComputeCNFFormula::new).compute();
        List<BiImplies> biImpliesList1 = new ComputeBiImplicationFormula(cnf,variables.get(3))
                .set(ComputeBiImplicationFormula.ALREADY_EXISTING_BI_IMPL,biImplies.get(3))
                .set(ComputeBiImplicationFormula.MAXIMUM_CLAUSE_SIZE,2)
                .compute();
        List<BiImplies> results = new ArrayList<>();
        results.add(new BiImplies(new Literal("b"),new Literal("d")));
        assertEquals(results.size(),biImpliesList1.size());
        for(BiImplies biImplies: biImpliesList1) {
            assert results.stream().anyMatch(biImplies1 -> biImplies1.equalsTree(biImplies));
        }
        List<BiImplies> biImpliesList2 = new ComputeBiImplicationFormula(cnf,variables.get(3))
                .set(ComputeBiImplicationFormula.ALREADY_EXISTING_BI_IMPL,biImplies.get(3))
                .set(ComputeBiImplicationFormula.MAXIMUM_CLAUSE_SIZE,4)
                .compute();
        results.add(new BiImplies(new Literal("m"),new Or(new Literal("e"),new Literal("i"))));
        assertEquals(results.size(),biImpliesList2.size());
        for(BiImplies biImplies: biImpliesList2) {
            assert results.stream().anyMatch(biImplies1 -> biImplies1.equalsTree(biImplies));
        }
        results.add(new BiImplies(new Literal("b"),new Literal("a")));
        results.add(new BiImplies(new Literal("n"), new Or(new Literal("o"),new Literal("p"))));
        results.add(new BiImplies(new Literal(false,"r"),new Or(new Literal("s"),new Literal("t"),new Literal(false,"q"))));
        results.add(new BiImplies(new Literal(false,"s"),new Or(new Literal("t"),new Literal(false,"q"),new Literal("r"))));
        results.add(new BiImplies(new Literal(false,"t"),new Or(new Literal("s"),new Literal(false,"q"),new Literal("r"))));
        results.add(new BiImplies(new Literal("q"),new Or(new Literal("s"), new Literal("t"),new Literal("r"))));
        List<BiImplies> biImpliesList3 = new ComputeBiImplicationFormula(cnf,variables.get(3))
                .set(ComputeBiImplicationFormula.MAXIMUM_CLAUSE_SIZE,4)
                .compute();
        assertEquals(results.size(),biImpliesList3.size());
        for(BiImplies biImplies: biImpliesList3) {
            assert results.stream().anyMatch(biImplies1 -> biImplies1.equalsTree(biImplies));
        }
        results.add(new BiImplies(new Literal(false,"u"),new Or(new Literal("v"),new Literal("w"),new Literal("x"),new Literal("y"),new Literal("z"))));
        List<BiImplies> biImpliesList4 = new ComputeBiImplicationFormula(cnf,variables.get(3))
                .set(ComputeBiImplicationFormula.MAXIMUM_CLAUSE_SIZE,6)
                .compute();
        assertEquals(results.size(),biImpliesList4.size());
        for(BiImplies biImplies: biImpliesList4) {
            assert results.stream().anyMatch(biImplies1 -> biImplies1.equalsTree(biImplies));
        }


    }

}
