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
import de.featjar.formula.structure.IExpression;
import de.featjar.formula.structure.formula.IFormula;
import de.featjar.formula.structure.formula.connective.*;
import de.featjar.formula.structure.formula.predicate.Literal;
import de.featjar.formula.structure.term.value.Variable;
import de.featjar.formula.visitor.CoreDeadSimplifier;

import java.util.*;
import java.util.stream.Collectors;

/**
 * preprocess step, to find not indeterminate hidden features
 * this technique
 * TODO Discuss, because maybe it to complex
 */
public class PreprocessIffCompSort extends IndeterminatePreprocessFormula{

    public static final Dependency<Integer> EXPRESSION_MAX_LENGTH =
            Dependency.newDependency(Integer.class);

    private BooleanAssignment hiddenVariables;
    private VariableMap mapping;
    private ArrayList<Pair<String,List<Integer>>> definedFormula = new ArrayList<>();

    private ArrayList<BiImplies> checkingBiImplies = new ArrayList<>();
    private int expressionMaxLength;
    public PreprocessIffCompSort(IComputation<IFormula> formula) {
        super(formula,Computations.of(2));
    }


    @Override
    public Result<BooleanAssignment> compute(List<Object> dependencyList, Progress progress) {
        hiddenVariables = VARIABLES_OF_INTEREST.get(dependencyList);
        mapping = VARIABLE_MAP.get(dependencyList);
        IFormula formula = FORMULA.get(dependencyList);
        expressionMaxLength = EXPRESSION_MAX_LENGTH.get(dependencyList);
        // check whether conditions for preprocess are satisfied
        if(hiddenVariables.isEmpty() || mapping.isEmpty() || !(formula instanceof  And)) return Result.of(hiddenVariables);
        BooleanAssignment deadCoreVariables = CORE_DEAD_FEATURE.get(dependencyList);
        Pair<BooleanAssignment, IFormula> updateDeCo = handleDeadAndCore(formula,deadCoreVariables,hiddenVariables,mapping);
        if(updateDeCo != null) {
            hiddenVariables = updateDeCo.getKey();
            formula = updateDeCo.getValue();
        }
        for(IExpression child :formula.getChildren()){
            if(child instanceof BiImplies){
                BiImplies implies = (BiImplies) child;
                checkingBiImplies.add(implies);
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
        sortBiImplies();
        for(BiImplies biImplies: checkingBiImplies){
            IExpression leftExpression = biImplies.getLeftExpression();
            IExpression rightExpression = biImplies.getRightExpression();
            boolean alreadyChecked = false;
            Literal leftLiteral = getLiteral(leftExpression);
            Literal rightLiteral = getLiteral(rightExpression);
            if (leftLiteral != null ) {
                checkLiteralIsUnique(leftLiteral,rightExpression);
            }else {
                Pair<String,List<Integer>> expr = interestingExpr(leftExpression,false,false);
                if(expr != null && definedFormula.stream().anyMatch(pair -> expr.getKey().equals(pair.getKey()) && pair.getValue().equals(expr.getValue()))){
                    alreadyChecked = true;
                    checkUniqueExprOtherSide(rightExpression);
                }
            }
            if (rightLiteral != null) {
                checkLiteralIsUnique(rightLiteral,leftExpression);
            }else if(!alreadyChecked){
                Pair<String,List<Integer>> expr = interestingExpr(rightExpression,false,false);
                if(expr != null && definedFormula.stream().anyMatch(pair -> expr.getKey().equals(pair.getKey()) && pair.getValue().equals(expr.getValue()))){
                    checkUniqueExprOtherSide(leftExpression);
                }
            }
        }
        return Result.of(hiddenVariables);
    }
    private void sortBiImplies() {
        HashMap<Integer,Integer> rankHidden = new HashMap<>();
        HashMap<BiImplies,Float> rankExpression = new HashMap<>();
        checkingBiImplies.forEach(biImplies -> rankHiddenFeature(biImplies,rankHidden));
        checkingBiImplies.forEach(biImplies -> rankExpression.put(biImplies,rankBiImplies(biImplies,rankHidden)) );
        checkingBiImplies =  checkingBiImplies.stream().sorted((o1, o2) ->  Float.compare(rankExpression.get(o1), rankExpression.get(o2))).collect(Collectors.toCollection(ArrayList::new));
    }
    //TODO improve rankSystem, Idea: give every hiddenVariable rank depending on how often it occurs as single Literal at a Biimplies side
    private float rankBiImplies(BiImplies biImplies,HashMap<Integer,Integer> rankHidden){
        IExpression leftExpression = biImplies.getLeftExpression();
        IExpression rightExpression = biImplies.getRightExpression();
        Literal leftLiteral = getLiteral(leftExpression);
        Literal rightLiteral = getLiteral(rightExpression);
        float rank = Float.MAX_VALUE;
        if(leftLiteral != null && hiddenVariables.contains(unwrapVariable(leftLiteral,mapping))){
            List<Variable> variables = rightExpression.getVariables();
            rank =  getExpressionRank(variables.stream().mapToInt(variable -> getMapping(variable.getName(),mapping)).filter(hiddenVariables::contains).toArray(),rankHidden);
            if(rank == Float.MAX_VALUE ) return rank;
        }
        if (rightLiteral != null && hiddenVariables.contains(unwrapVariable(rightLiteral,mapping))) {
            List<Variable> variables = leftExpression.getVariables();
            float value = getExpressionRank(variables.stream().mapToInt(variable -> getMapping(variable.getName(),mapping)).filter(hiddenVariables::contains).toArray(),rankHidden);
            if(rank != Float.MAX_VALUE)rank= value*rank;
            else rank = value;
            if(rank == Float.MAX_VALUE) return  rank;
        }
        if(rank == Float.MAX_VALUE) {
            if (leftLiteral != null) {
                if (rightExpression.getVariables().stream().anyMatch(variable -> hiddenVariables.contains(getMapping(variable.getName(), mapping)))) {
                    return 0.0000001f;
                }
            } else if (rightLiteral != null) {
                if (leftExpression.getVariables().stream().anyMatch(variable -> hiddenVariables.contains(getMapping(variable.getName(), mapping)))) {
                    return 0.0000001f;
                }
            } else if (rightExpression.getVariables().stream().anyMatch(variable -> hiddenVariables.contains(getMapping(variable.getName(), mapping)))
                    && leftExpression.getVariables().stream().anyMatch(variable -> hiddenVariables.contains(getMapping(variable.getName(), mapping)))) {
                return 0.000001f;
            }
        }
        return rank;
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
        Literal leftLiteral = getLiteral(leftExpression);
        Literal rightLiteral = getLiteral(rightExpression);
        if(leftLiteral != null && hiddenVariables.contains(unwrapVariable(leftLiteral,mapping))){
            int id =  unwrapVariable(leftLiteral, mapping);
            Integer value = rankHidden.get(id);
            if(value == null) value = 0;
            rankHidden.put(id,++value);
        }
        if (rightLiteral != null && hiddenVariables.contains(unwrapVariable(rightLiteral,mapping))) {
            int id =  unwrapVariable(rightLiteral, mapping);
            Integer value = rankHidden.get(id);
            if(value == null) value = 0;
            rankHidden.put(id,++value);
        }
    }

    /**
     * check if one side of {@link BiImplies} only have {@link Literal}s which are not hidden or hidden features which aren't indeterminate,
     */
    private void checkLiteralIsUnique(Literal literal, IExpression otherExpression) {
        int id = unwrapVariable(literal,mapping);
        List<Variable> variables = otherExpression.getVariables();

        if(hiddenVariables.contains(id)){

            Pair<String,List<Integer>> expr = interestingExpr(otherExpression,false,false);
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
                    if (hiddenVariables.contains( Math.abs( variable)) && !removedVariables.contains(variable)) {
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
            Pair<String,List<Integer>> expr = interestingExpr(otherExpression,false,false);
            if(expr!=null) definedFormula.add(expr);
        }
    }
    private void checkUniqueExprOtherSide(IExpression otherExpression) {
        Literal literal = getLiteral(otherExpression);
        if(literal != null){
            int id =  unwrapVariable(literal, mapping);
            if(hiddenVariables.contains(id)) hiddenVariables =  new BooleanAssignment(hiddenVariables.removeAll(id));
        }else{
            Pair<String,List<Integer>> expr = interestingExpr(otherExpression,false,false);
            if( expr!= null) definedFormula.add(expr);
        }
    }

    /**
     * Check if Expression is simple enough to be relevant for this algorithm and return as cnf.
     * @param notAnd If Expression is  and return null
     * @param onlyAnd If Expression is not and return null
     *
     *
     */
    private Pair<String,List<Integer>> interestingExpr(IExpression expression,boolean notAnd, boolean onlyAnd){
        List<Integer> result = new ArrayList<>();
        if( expression.getVariables().size() <= expressionMaxLength ) {
            if ((expression instanceof And && !notAnd) || (expression instanceof Or && !onlyAnd)) {
                for (IExpression child : expression.getChildren()) {
                    if (child instanceof Literal) {
                        result.add( unwrapLiteral((Literal) child, mapping));
                    } else if (child instanceof Not && child.getChildren().get(0) instanceof Literal) {
                        result.add( -unwrapLiteral((Literal) child.getChildren().get(0), mapping));
                    }else if(expression instanceof Or){
                        Pair<String,List<Integer>> resultChild = interestingExpr(child,true,false);
                        if( resultChild == null) return null;
                        result.addAll(resultChild.getValue());
                    }else {
                        Pair<String,List<Integer>> resultChild = interestingExpr(child,false,true);
                        if( resultChild == null) return null;
                        result.addAll(resultChild.getValue());
                    }
                }
                if(!notAnd && !onlyAnd) result = result.stream().sorted().collect(Collectors.toList());
                if(expression instanceof And) return new Pair<>("and",result);
                return new Pair<>("or",result);
            }  else if (expression instanceof Implies && !onlyAnd) {
                IExpression leftExpression = ((Implies) expression).getLeftExpression();
                IExpression rightExpression = ((Implies) expression).getRightExpression();
                if(leftExpression instanceof Literal ){
                    result.add( -unwrapLiteral((Literal)leftExpression,mapping ));
                }else if(leftExpression instanceof  Not && leftExpression.getChildren().get(0) instanceof Literal){
                    result.add( unwrapLiteral((Literal)leftExpression.getChildren().get(0),mapping ));
                }else {
                    Pair<String,List<Integer>> resultChild = interestingExpr(leftExpression,false,true);
                    if( resultChild == null) return null;
                    result.addAll(resultChild.getValue().stream().map(x-> -x).collect(Collectors.toList()));
                }
                if( rightExpression instanceof Literal){
                    result.add( unwrapLiteral((Literal)rightExpression,mapping ));
                }else if(rightExpression instanceof  Not && rightExpression.getChildren().get(0) instanceof Literal){
                    result.add(-unwrapLiteral((Literal)rightExpression.getChildren().get(0),mapping ));
                }else {
                    Pair<String,List<Integer>> resultChild = interestingExpr(rightExpression,true,false);
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
