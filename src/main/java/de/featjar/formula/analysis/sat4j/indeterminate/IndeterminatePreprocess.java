package de.featjar.formula.analysis.sat4j.indeterminate;

import de.featjar.base.computation.*;
import de.featjar.base.data.Pair;
import de.featjar.base.data.Result;
import de.featjar.base.tree.Trees;
import de.featjar.formula.analysis.VariableMap;
import de.featjar.formula.analysis.bool.BooleanAssignment;
import de.featjar.formula.structure.IExpression;
import de.featjar.formula.structure.formula.IFormula;
import de.featjar.formula.structure.formula.connective.Not;
import de.featjar.formula.structure.formula.connective.Reference;
import de.featjar.formula.structure.formula.predicate.Literal;
import de.featjar.formula.structure.term.value.Variable;
import de.featjar.formula.visitor.CoreDeadSimplifier;

import java.util.Arrays;

/**
 *
 */
abstract public class IndeterminatePreprocess extends AComputation<BooleanAssignment> {

    public static final Dependency<BooleanAssignment> CORE_DEAD_FEATURE =
            Dependency.newDependency(BooleanAssignment.class);

    public static final Dependency<BooleanAssignment> VARIABLES_OF_INTEREST =
            Dependency.newDependency(BooleanAssignment.class);
    public static final Dependency<VariableMap> VARIABLE_MAP =
            Dependency.newDependency(VariableMap.class);

    public static final Dependency<Boolean> PARALLEL =
            Dependency.newDependency(Boolean.class);
    public IndeterminatePreprocess ( Object... computations) {
        super(Computations.of(new BooleanAssignment()),Computations.of(new BooleanAssignment()), Computations.of(new VariableMap()),Computations.of(false), computations);
    }

    protected Variable[] getUnitVariables(IExpression expression){
        return expression.getChildren().stream().filter(exp -> exp instanceof Literal && ((Literal) exp).getChildren().get(0) instanceof Variable).map(l -> (Variable) l.getChildren().get(0)).toArray(Variable[]::new);
    }
    protected BooleanAssignment removeHidden(BooleanAssignment hiddenVariables,VariableMap mapping, Variable... variables){
        return new BooleanAssignment(hiddenVariables.removeAll(Arrays.stream(variables).map(variable -> getMapping(variable.getName(),mapping)).mapToInt(Integer::intValue).toArray()));
    }
    protected int unwrapVariable(Literal literal, VariableMap mapping){
        return literal.getChildren().isEmpty() ? 0 : getMapping(literal.getExpression().getName(),mapping);
    }
    protected int unwrapLiteral(Literal literal, VariableMap mapping){
        int value =literal.getChildren().isEmpty() ? 0 : getMapping(literal.getExpression().getName(),mapping);
        return literal.isPositive() ? value : -value;
    }
    protected int getMapping(String name, VariableMap mapping){
        Result<Integer> integerResult = mapping.get(name);
        return integerResult.isEmpty() ? 0 : integerResult.get();
    }
    protected Literal getLiteral(IExpression expression) {
        if (expression instanceof Literal) {
            return (Literal) expression;
        }else if (expression instanceof Not &&  expression.getChildren().get(0) instanceof Literal) {
            return (Literal) expression.getChildren().get(0);
        }
        return null;
    }

    protected Pair<BooleanAssignment,IFormula> handleDeadAndCore(IFormula formula, BooleanAssignment deadCoreFeatures, BooleanAssignment hiddenVariables, VariableMap mapping){
        if(!deadCoreFeatures.isEmpty()){
            hiddenVariables = new BooleanAssignment(hiddenVariables.stream().filter((hidden ) ->
                    !deadCoreFeatures.containsVariable(hidden)).toArray());
            Result<IFormula> formulaResult = Reference.mutateClone(formula, reference -> Trees.traverse(reference,new CoreDeadSimplifier(deadCoreFeatures.toValueName(mapping))));
            if(formulaResult.isPresent()) formula = formulaResult.get();
            return new Pair<>(hiddenVariables,formula);
        }
        return null;
    }

}
