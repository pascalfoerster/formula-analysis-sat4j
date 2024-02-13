package de.featjar.formula.analysis.sat4j.indeterminate;

import de.featjar.base.computation.Computations;
import de.featjar.base.computation.Dependency;
import de.featjar.base.computation.IComputation;
import de.featjar.base.computation.Progress;
import de.featjar.base.data.Result;
import de.featjar.base.tree.Trees;
import de.featjar.formula.analysis.VariableMap;
import de.featjar.formula.analysis.bool.BooleanAssignment;
import de.featjar.formula.structure.IExpression;
import de.featjar.formula.structure.formula.IFormula;
import de.featjar.formula.structure.formula.connective.*;
import de.featjar.formula.structure.formula.predicate.Literal;
import de.featjar.formula.structure.term.value.Variable;
import de.featjar.formula.visitor.CoreDeadSimplifier;

import java.util.List;

/**
 * preprocess step, to find not indeterminate hidden features
 */
public class PreprocessIff extends IndeterminatePreprocessFormula{

    public static final Dependency<BooleanAssignment> DEAD_FEATURE =
            Dependency.newDependency(BooleanAssignment.class);
    public static final Dependency<BooleanAssignment> CORE_FEATURE =
            Dependency.newDependency(BooleanAssignment.class);

    private BooleanAssignment hiddenVariables;
    private VariableMap mapping;
    public PreprocessIff(IComputation<IFormula> formula) {
        super(formula, Computations.of(new BooleanAssignment()),Computations.of(new BooleanAssignment()));
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
            BooleanAssignment assignment = coreFeatures.addAll(deadVariables.inverse());
            Result<IFormula> formulaResult = Reference.mutateClone(formula,reference -> Trees.traverse(reference,new CoreDeadSimplifier(assignment.toValueName(mapping))));
            if(formulaResult.isPresent()) formula = formulaResult.get();
        }
        for(IExpression child :formula.getChildren()){
            if(child instanceof BiImplies){
                BiImplies implies = (BiImplies) child;
                IExpression leftExpression = implies.getLeftExpression();
                IExpression rightExpression = implies.getRightExpression();
                Literal leftLiteral = getLiteral(leftExpression);
                Literal rightLiteral = getLiteral(rightExpression);
                if(leftLiteral != null)  checkLiteralIsUnique(leftLiteral,rightExpression);
                if(rightLiteral != null) checkLiteralIsUnique(rightLiteral,leftExpression);
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
        return Result.of(hiddenVariables);
    }

    /**
     * check if one side of {@link BiImplies} only have {@link Literal}s which are not hidden or hidden features which aren't indeterminate,
     */
    private void checkLiteralIsUnique(Literal literal, IExpression otherExpression) {
        int id = unwrapVariable(literal,mapping);
        if(hiddenVariables.contains(id)){
            List<Variable> variables = otherExpression.getVariables();
            for (Variable variable : variables){
                if(hiddenVariables.contains(getMapping(variable.getName(),mapping))){
                    return ;
                }
            }
            hiddenVariables =  new BooleanAssignment(hiddenVariables.removeAll(id));
        }
    }
}
