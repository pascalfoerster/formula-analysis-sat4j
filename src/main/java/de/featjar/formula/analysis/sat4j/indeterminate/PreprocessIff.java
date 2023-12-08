package de.featjar.formula.analysis.sat4j.indeterminate;

import de.featjar.base.computation.Dependency;
import de.featjar.base.computation.IComputation;
import de.featjar.base.computation.Progress;
import de.featjar.base.data.Result;
import de.featjar.formula.analysis.VariableMap;
import de.featjar.formula.analysis.bool.ABooleanAssignment;
import de.featjar.formula.analysis.bool.BooleanAssignment;
import de.featjar.formula.structure.IExpression;
import de.featjar.formula.structure.formula.IFormula;
import de.featjar.formula.structure.formula.connective.And;
import de.featjar.formula.structure.formula.connective.BiImplies;
import de.featjar.formula.structure.formula.predicate.Literal;
import de.featjar.formula.structure.term.value.IValue;
import de.featjar.formula.structure.term.value.Variable;

import java.util.List;

public class PreprocessIff extends IndeterminatePreprocess{
    public static final Dependency<IFormula> FORMULA =
            Dependency.newDependency(IFormula.class);
    public PreprocessIff(IComputation<IFormula> formula, Object... computations) {
        super(formula, computations);
    }

    @Override
    public Result<BooleanAssignment> compute(List<Object> dependencyList, Progress progress) {
        BooleanAssignment hiddenVariables = VARIABLES_OF_INTEREST.get(dependencyList);
        VariableMap mapping = VARIABLE_MAP.get(dependencyList);
        IFormula formula = FORMULA.get(dependencyList);

        // check whether conditions for preprocess are satisfied
        if(hiddenVariables.isEmpty() || mapping.isEmpty() ) return Result.of(hiddenVariables);
        assert(formula  instanceof And);
        for(IExpression child :formula.getChildren()){
            if(child instanceof BiImplies){
                BiImplies implies = (BiImplies) child;
                IExpression leftExpression = implies.getLeftExpression();
                IExpression rightExpression = implies.getRightExpression();
                if(leftExpression instanceof Literal ){
                    hiddenVariables = checkLiteralIsUnique((Literal) leftExpression,hiddenVariables,mapping,rightExpression);
                }
                if( rightExpression instanceof Literal){
                    hiddenVariables = checkLiteralIsUnique((Literal) rightExpression,hiddenVariables,mapping,leftExpression);
                }

            }
            //if a clause is unit clause and  literal is hidden variable remove it from booleanAssignment
            else if(child instanceof Literal){
                Variable unitClause = (Variable) child.getChildren().get(0);
                hiddenVariables = new BooleanAssignment(hiddenVariables.removeAll(mapping.get(unitClause.getName()).get()));
            }
        }
        return Result.of(hiddenVariables);
    }

    /**
     * check if one side of {@link BiImplies} only have {@link Literal}s which are not hidden or hidden features which aren't indeterminate,
     */
    private BooleanAssignment checkLiteralIsUnique(Literal literal, BooleanAssignment hiddenVariables, VariableMap mapping, IExpression otherExpression) {
        IValue value = literal.getChildren().get(0);
        Integer id = mapping.get(value.getName()).get();
        if(hiddenVariables.contains(id)){
            List<Variable> variables = otherExpression.getVariables();
            for (Variable variable : variables){
                if(hiddenVariables.contains(mapping.get(variable.getName()).get())){
                    return hiddenVariables;
                }
            }
            return new BooleanAssignment(hiddenVariables.removeAll(id));


        }
        return hiddenVariables;
    }
}
