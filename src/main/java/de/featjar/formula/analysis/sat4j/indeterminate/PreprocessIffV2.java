package de.featjar.formula.analysis.sat4j.indeterminate;

import de.featjar.base.computation.Computations;
import de.featjar.base.computation.Dependency;
import de.featjar.base.computation.IComputation;
import de.featjar.base.computation.Progress;
import de.featjar.base.data.Result;
import de.featjar.formula.analysis.VariableMap;
import de.featjar.formula.analysis.bool.BooleanAssignment;
import de.featjar.formula.structure.IExpression;
import de.featjar.formula.structure.formula.IFormula;
import de.featjar.formula.structure.formula.connective.And;
import de.featjar.formula.structure.formula.connective.BiImplies;
import de.featjar.formula.structure.formula.connective.Not;
import de.featjar.formula.structure.formula.predicate.Literal;
import de.featjar.formula.structure.term.value.IValue;
import de.featjar.formula.structure.term.value.Variable;

import java.util.*;
import java.util.stream.Collectors;

public class PreprocessIffV2 extends IndeterminatePreprocess{
    private static final Dependency<IFormula> FORMULA =
            Dependency.newDependency(IFormula.class);
    public static final Dependency<BooleanAssignment> DEAD_FEATURE =
            Dependency.newDependency(BooleanAssignment.class);
    public static final Dependency<BooleanAssignment> CORE_FEATURE =
            Dependency.newDependency(BooleanAssignment.class);

    private BooleanAssignment hiddenVariables;
    private VariableMap mapping;
    private Set<BiImplies> interestBiImplies ;
    private Set<Integer> definedHidden;
    private Set<Integer> undefinedHidden;
    public PreprocessIffV2(IComputation<IFormula> formula) {
        super(formula, Computations.of(new BooleanAssignment()),Computations.of(new BooleanAssignment()));
        interestBiImplies = new HashSet<>();
        definedHidden = new HashSet<>();
        undefinedHidden = new HashSet<>();
    }


    @Override
    public Result<BooleanAssignment> compute(List<Object> dependencyList, Progress progress) {
        hiddenVariables = VARIABLES_OF_INTEREST.get(dependencyList);
        mapping = VARIABLE_MAP.get(dependencyList);
        IFormula formula = FORMULA.get(dependencyList);
        BooleanAssignment deadVariables = DEAD_FEATURE.get(dependencyList);
        BooleanAssignment coreFeatures = CORE_FEATURE.get(dependencyList);
        // check whether conditions for preprocess are satisfied
        if(hiddenVariables.isEmpty() || mapping.isEmpty() || !(formula instanceof  And)) return Result.of(hiddenVariables);
        if(!deadVariables.isEmpty() || ! coreFeatures.isEmpty()){
            hiddenVariables = new BooleanAssignment(hiddenVariables.stream().filter((hidden ) ->
                    !deadVariables.contains(hidden) && ! coreFeatures.contains(hidden)).toArray());
            //TODO simplify formal with dead and core feature
        }
        for(IExpression child :formula.getChildren()){
            if(child instanceof BiImplies){
                checkBiImplies((BiImplies) child);
            }
            //if a clause is unit clause and  literal is hidden variable remove it from booleanAssignment
            else if( child instanceof Literal){
                Variable unitClause = (Variable) child.getChildren().get(0);
                hiddenVariables = removeHidden(hiddenVariables,mapping,unitClause);
            }
            else if( child instanceof Not && child.getChildren().get(0) instanceof Literal){
                Variable unitClause = (Variable) child.getChildren().get(0).getChildren().get(0);
                hiddenVariables = removeHidden(hiddenVariables,mapping,unitClause);
            }else if (child instanceof And){
                hiddenVariables = removeHidden(hiddenVariables,mapping,  getUnitVariables(child));
            }
        }
        while (undefinedHidden.stream().anyMatch(definedHidden::contains) && !interestBiImplies.isEmpty() && !hiddenVariables.isEmpty()){
            undefinedHidden = new HashSet<>();
            definedHidden = new HashSet<>();
            Set<BiImplies> copy = new HashSet<>(interestBiImplies);
            interestBiImplies = new HashSet<>();
            for(BiImplies biImplies: copy){
                checkBiImplies(biImplies);
            }
        }
        return Result.of(hiddenVariables);
    }

    private void checkBiImplies(BiImplies biImplies){
        IExpression leftExpression = biImplies.getLeftExpression();
        IExpression rightExpression = biImplies.getRightExpression();
        if(leftExpression instanceof Literal ){
            checkLiteralIsUnique((Literal) leftExpression,rightExpression,biImplies);
        }
        if( rightExpression instanceof Literal){
            checkLiteralIsUnique((Literal) rightExpression,leftExpression, biImplies);
        }
    }
    /**
     * check if one side of {@link BiImplies} only have {@link Literal}s which are not hidden or hidden features which aren't indeterminate,
     */
    private void checkLiteralIsUnique(Literal literal, IExpression otherExpression, BiImplies biImplies) {
        int id = unwrapLiteral(literal,mapping);
        if(hiddenVariables.contains(id)){
            int[] variables = otherExpression.getVariables().stream().
                    mapToInt(variable -> getMapping(variable.getName(),mapping))
                    .filter((variable) ->hiddenVariables.contains(variable) && variable!=id)
                    .toArray();
            if(variables.length == 0) {
                definedHidden.add(id);
                hiddenVariables = new BooleanAssignment(hiddenVariables.removeAll(id));
            }else {
                Arrays.stream(variables).forEach(undefinedHidden::add);
                interestBiImplies.add(biImplies);
            }
        }
    }
}