package de.featjar.formula.analysis.sat4j.indeterminate;

import de.featjar.base.computation.Computations;
import de.featjar.base.computation.Dependency;
import de.featjar.base.computation.IComputation;
import de.featjar.base.computation.Progress;
import de.featjar.base.data.Pair;
import de.featjar.base.data.Result;
import de.featjar.base.tree.Trees;
import de.featjar.formula.analysis.VariableMap;
import de.featjar.formula.analysis.bool.BooleanAssignment;
import de.featjar.formula.structure.ExpressionKind;
import de.featjar.formula.structure.IExpression;
import de.featjar.formula.structure.formula.IFormula;
import de.featjar.formula.structure.formula.connective.*;
import de.featjar.formula.structure.formula.predicate.Literal;
import de.featjar.formula.structure.term.value.Variable;
import de.featjar.formula.visitor.CoreDeadSimplifier;

import java.util.*;
import java.util.stream.Collectors;
import java.util.stream.IntStream;
import java.util.stream.Stream;

/**
 * preprocess step, to find not indeterminate hidden features
 * this technique
 * TODO Discuss, because maybe it to complex
 */
public class PreprocessIffComp extends IndeterminatePreprocess{
    private static final Dependency<IFormula> FORMULA =
            Dependency.newDependency(IFormula.class);
    public static final Dependency<BooleanAssignment> DEAD_FEATURE =
            Dependency.newDependency(BooleanAssignment.class);
    public static final Dependency<BooleanAssignment> CORE_FEATURE =
            Dependency.newDependency(BooleanAssignment.class);

    public static final Dependency<Integer> EXPRESSION_MAX_LENGTH =
            Dependency.newDependency(Integer.class);

    private BooleanAssignment hiddenVariables;
    private VariableMap mapping;
    private ArrayList<Pair<String,List<Integer>>> definedFormula = new ArrayList<>();
    private int expressionMaxLength;
    public PreprocessIffComp(IComputation<IFormula> formula) {
        super(formula, Computations.of(new BooleanAssignment()),Computations.of(new BooleanAssignment()),Computations.of(2));
    }


    @Override
    public Result<BooleanAssignment> compute(List<Object> dependencyList, Progress progress) {
        hiddenVariables = VARIABLES_OF_INTEREST.get(dependencyList);
        mapping = VARIABLE_MAP.get(dependencyList);
        IFormula formula = FORMULA.get(dependencyList);
        BooleanAssignment deadVariables = DEAD_FEATURE.get(dependencyList);
        BooleanAssignment coreFeatures = CORE_FEATURE.get(dependencyList);
        expressionMaxLength = EXPRESSION_MAX_LENGTH.get(dependencyList);
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
                boolean alreadyChecked = false;
                if(leftExpression instanceof Literal ){
                    checkLiteralIsUnique((Literal) leftExpression,rightExpression);
                }else if(leftExpression instanceof  Not && leftExpression.getChildren().get(0) instanceof Literal){
                    checkLiteralIsUnique((Literal) leftExpression.getChildren().get(0),rightExpression);
                }else {
                    Pair<String,List<Integer>> expr = interestingExpr(leftExpression,false);
                    if(expr != null && definedFormula.stream().anyMatch(pair -> expr.getKey().equals(pair.getKey()) && pair.getValue().equals(expr.getValue()))){
                        alreadyChecked = true;
                        checkUniqueExprOtherSide(rightExpression);
                    }
                }
                if( rightExpression instanceof Literal){
                    checkLiteralIsUnique((Literal) rightExpression,leftExpression);
                }else if(rightExpression instanceof  Not && rightExpression.getChildren().get(0) instanceof Literal){
                    checkLiteralIsUnique((Literal) rightExpression.getChildren().get(0),leftExpression);
                }else if(!alreadyChecked){
                    Pair<String,List<Integer>> expr = interestingExpr(rightExpression,false);
                    if(expr != null && definedFormula.stream().anyMatch(pair -> expr.getKey().equals(pair.getKey()) && pair.getValue().equals(expr.getValue()))){
                        checkUniqueExprOtherSide(leftExpression);
                    }
                }
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
        int id = unwrapLiteral(literal,mapping);
        List<Variable> variables = otherExpression.getVariables();

        if(hiddenVariables.contains(id)){

            Pair<String,List<Integer>> expr = interestingExpr(otherExpression,false);
            Set<Integer> removedVariables = new HashSet<>();
            if(expr != null) {
                definedFormula.forEach(pair ->{
                    if(pair.getKey().equals(expr.getKey())){
                        if(pair.getValue().stream().allMatch(ele -> expr.getValue().stream().anyMatch(ele2 -> Objects.equals(ele, ele2)) )){
                            removedVariables.addAll(pair.getValue());
                        }
                    }
                });
                for (int variable :expr.getValue()) {
                    if (hiddenVariables.contains( variable) && !removedVariables.contains(variable)) {
                        return;
                    }
                }
            }else {
                for (Variable variable : variables) {
                    if (hiddenVariables.contains(getMapping(variable.getName(), mapping))) {
                        return;
                    }

                }
            }
            hiddenVariables =  new BooleanAssignment(hiddenVariables.removeAll(id));

        }else if(variables.size() > 1 ){
            Pair<String,List<Integer>> expr = interestingExpr(otherExpression,false);
            if(expr!=null) definedFormula.add(expr);
        }
    }
    private void checkUniqueExprOtherSide(IExpression otherExpression) {
        if(otherExpression instanceof Literal ){
            int id =  unwrapLiteral((Literal) otherExpression, mapping);
            if(hiddenVariables.contains(id)) hiddenVariables =  new BooleanAssignment(hiddenVariables.removeAll(id));
        }else if(otherExpression instanceof  Not && otherExpression.getChildren().get(0) instanceof Literal){
            int id =  unwrapLiteral((Literal) otherExpression.getChild(0).get(), mapping);
            if(hiddenVariables.contains(id))  hiddenVariables =  new BooleanAssignment(hiddenVariables.removeAll(id));
        }else{
            Pair<String,List<Integer>> expr = interestingExpr(otherExpression,false);
            if( expr!= null) definedFormula.add(expr);
        }
    }

    /**
     * Check if Expression is simple enough to be relevant for this algorithm and return as cnf.
     *
     */
    private Pair<String,List<Integer>> interestingExpr(IExpression expression,boolean notAnd){
       List<Integer> result = new ArrayList<>();
        if( expression.getChildrenCount() <= expressionMaxLength ) {
            if ((expression instanceof And && !notAnd) || expression instanceof Or) {
                for (IExpression child : expression.getChildren()) {
                    if (child instanceof Literal) {
                        result.add( unwrapLiteral((Literal) child, mapping));
                    } else if (child instanceof Not && child.getChildren().get(0) instanceof Literal) {
                        result.add( -unwrapLiteral((Literal) child.getChildren().get(0), mapping));
                    }else if(expression instanceof Or){
                        Pair<String,List<Integer>> resultChild = interestingExpr(child,true);
                        if( resultChild == null) return null;
                        result.addAll(resultChild.getValue());
                    }
                }
                if(!notAnd) result = result.stream().sorted().collect(Collectors.toList());
                if(expression instanceof And) return new Pair<>("and",result);
                return new Pair<>("or",result);
            }  else if (expression instanceof Implies) {
                IExpression leftExpression = ((Implies) expression).getLeftExpression();
                IExpression rightExpression = ((Implies) expression).getRightExpression();
                int[] leftSide = null, rightSide = null;
                if(leftExpression instanceof Literal ){
                    result.add( -unwrapLiteral((Literal)leftExpression,mapping ));
                }else if(leftExpression instanceof  Not && leftExpression.getChildren().get(0) instanceof Literal){
                    result.add( unwrapLiteral((Literal)leftExpression.getChildren().get(0),mapping ));
                }else {
                    Pair<String,List<Integer>> resultChild = interestingExpr(leftExpression,true);
                    if( resultChild == null) return null;
                    result.addAll(resultChild.getValue());
                }
                if( rightExpression instanceof Literal){
                    result.add( unwrapLiteral((Literal)rightExpression,mapping ));
                }else if(rightExpression instanceof  Not && rightExpression.getChildren().get(0) instanceof Literal){
                    result.add(-unwrapLiteral((Literal)rightExpression.getChildren().get(0),mapping ));
                }else {
                    Pair<String,List<Integer>> resultChild = interestingExpr(rightExpression,true);
                    if( resultChild == null) return null;
                    result.addAll(resultChild.getValue());
                }

                if(!notAnd) result = result.stream().sorted().collect(Collectors.toList());
                return new Pair<>("or",result);
            }

        }
        return null;
    }


}
