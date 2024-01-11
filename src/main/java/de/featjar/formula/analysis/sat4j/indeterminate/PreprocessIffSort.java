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
import de.featjar.formula.structure.term.value.Variable;

import java.util.*;
import java.util.stream.Collectors;

/**
 * preprocess step, to find not indeterminate hidden features
 */
public class PreprocessIffSort extends IndeterminatePreprocess {
    private static final Dependency<IFormula> FORMULA =
            Dependency.newDependency(IFormula.class);
    public static final Dependency<BooleanAssignment> DEAD_FEATURE =
            Dependency.newDependency(BooleanAssignment.class);
    public static final Dependency<BooleanAssignment> CORE_FEATURE =
            Dependency.newDependency(BooleanAssignment.class);

    private BooleanAssignment hiddenVariables;
    private VariableMap mapping;
    private Set<BiImplies> checkingBiImplies;

    public PreprocessIffSort(IComputation<IFormula> formula) {
        super(formula, Computations.of(new BooleanAssignment()), Computations.of(new BooleanAssignment()));
        checkingBiImplies = new HashSet<>();
    }


    @Override
    public Result<BooleanAssignment> compute(List<Object> dependencyList, Progress progress) {
        hiddenVariables = VARIABLES_OF_INTEREST.get(dependencyList);
        mapping = VARIABLE_MAP.get(dependencyList);
        IFormula formula = FORMULA.get(dependencyList);
        BooleanAssignment deadVariables = DEAD_FEATURE.get(dependencyList);
        BooleanAssignment coreFeatures = CORE_FEATURE.get(dependencyList);

        // check whether conditions for preprocess are satisfied
        if (hiddenVariables.isEmpty() || mapping.isEmpty() || !(formula instanceof And))
            return Result.of(hiddenVariables);
        if (!deadVariables.isEmpty() || !coreFeatures.isEmpty()) {
            hiddenVariables = new BooleanAssignment(hiddenVariables.stream().filter((hidden) ->
                    !deadVariables.contains(hidden) && !coreFeatures.contains(hidden)).toArray());
            //TODO simplify formal with dead and core feature
        }
        for (IExpression child : formula.getChildren()) {
            if (child instanceof BiImplies) {
                BiImplies implies = (BiImplies) child;
                IExpression leftExpression = implies.getLeftExpression();
                IExpression rightExpression = implies.getRightExpression();
                if (leftExpression instanceof Literal && hiddenVariables.contains(unwrapLiteral((Literal) leftExpression,mapping))) {
                    checkingBiImplies.add(implies);
                }else if (rightExpression instanceof Literal&& hiddenVariables.contains(unwrapLiteral((Literal) rightExpression,mapping))) {
                    checkingBiImplies.add(implies);
                }
            }
            //if a clause is unit clause and  literal is hidden variable remove it from booleanAssignment
            else if (child instanceof Literal) {
                Variable unitClause = (Variable) child.getChildren().get(0);
                hiddenVariables = removeHidden(hiddenVariables, mapping, unitClause);
            } else if (child instanceof Not && child.getChildren().get(0) instanceof Literal) {
                Variable unitClause = (Variable) child.getChildren().get(0).getChildren().get(0);
                hiddenVariables = removeHidden(hiddenVariables, mapping, unitClause);
            } else if (child instanceof And) {
                hiddenVariables = removeHidden(hiddenVariables, mapping, getUnitVariables(child));
            }
        }
        sortBiImplies();
        for(BiImplies biImplies: checkingBiImplies){
            IExpression leftExpression = biImplies.getLeftExpression();
            IExpression rightExpression = biImplies.getRightExpression();
            if(leftExpression instanceof Literal ){
                checkLiteralIsUnique((Literal) leftExpression,rightExpression);
            }
            if( rightExpression instanceof Literal){
                checkLiteralIsUnique((Literal) rightExpression,leftExpression);
            }
        }
        return Result.of(hiddenVariables);
    }

    private void sortBiImplies() {
        HashMap<Integer,Integer> rankHidden = new HashMap<>();
        checkingBiImplies.stream().forEach(biImplies -> rankHiddenFeature(biImplies,rankHidden));
        checkingBiImplies =  checkingBiImplies.stream().sorted((o1, o2) ->  Float.compare(rankBiImplies(o1, rankHidden), rankBiImplies(o2, rankHidden))).collect(Collectors.toCollection(LinkedHashSet::new));
    }
    //TODO improve rankSystem, Idea: give every hiddenVariable rank depending on how often it occurs as single Literal at a Biimplies side
    private float rankBiImplies(BiImplies biImplies,HashMap<Integer,Integer> rankHidden){
        IExpression leftExpression = biImplies.getLeftExpression();
        IExpression rightExpression = biImplies.getRightExpression();

        if(leftExpression instanceof Literal && hiddenVariables.contains(unwrapLiteral((Literal) leftExpression,mapping))){
            List<Variable> variables = rightExpression.getVariables();
            return getExpressionRank(variables.stream().mapToInt(variable -> getMapping(variable.getName(),mapping)).filter(hiddenVariables::contains).toArray(),rankHidden);
        } else if (rightExpression instanceof Literal && hiddenVariables.contains(unwrapLiteral((Literal) rightExpression,mapping))) {
            List<Variable> variables = leftExpression.getVariables();
            return getExpressionRank(variables.stream().mapToInt(variable -> getMapping(variable.getName(),mapping)).filter(hiddenVariables::contains).toArray(),rankHidden);
        }
        return Float.MAX_VALUE;
    }
    private float getExpressionRank(int[] featureIds,HashMap<Integer,Integer> rankFeature) {
        float sum = 0;
        for(int featureId: featureIds) {
            Integer value = rankFeature.get(featureId);
            if(value == null) return  Float.MAX_VALUE;
            sum += (float) 1 /value;
        }
        return sum;
    }
    private void rankHiddenFeature(BiImplies biImplies, HashMap<Integer,Integer> rankHidden){
        IExpression leftExpression = biImplies.getLeftExpression();
        IExpression rightExpression = biImplies.getRightExpression();
        if(leftExpression instanceof Literal && hiddenVariables.contains(unwrapLiteral((Literal) leftExpression,mapping))){
            int id =  unwrapLiteral((Literal) leftExpression, mapping);
            Integer value = rankHidden.get(id);
            if(value == null) value = -1;
            rankHidden.put(id,++value);
        }
        if (rightExpression instanceof Literal && hiddenVariables.contains(unwrapLiteral((Literal) rightExpression,mapping))) {
            int id =  unwrapLiteral((Literal) rightExpression, mapping);
            Integer value = rankHidden.get(id);
            if(value == null) value = -1;
            rankHidden.put(id,++value);
        }
    }


    /**
     * check if one side of {@link BiImplies} only have {@link Literal}s which are not hidden or hidden features which aren't indeterminate,
     */
    private void checkLiteralIsUnique(Literal literal, IExpression otherExpression) {
        int id = unwrapLiteral(literal,mapping);
        if (hiddenVariables.contains(id)) {
            List<Variable> variables = otherExpression.getVariables();
            for (Variable variable : variables) {
                if (hiddenVariables.contains(getMapping(variable.getName(),mapping))) {
                    return;
                }
            }
            hiddenVariables = new BooleanAssignment(hiddenVariables.removeAll(id));
        }
    }
}
