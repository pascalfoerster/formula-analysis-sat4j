package de.featjar.formula.analysis.sat4j.indeterminate;

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
import de.featjar.formula.structure.formula.predicate.Literal;
import de.featjar.formula.structure.term.value.IValue;
import de.featjar.formula.structure.term.value.Variable;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;

public class PreprocessIffStore extends IndeterminatePreprocess{

    public static final Dependency<IFormula> FORMULA =
            Dependency.newDependency(IFormula.class);
    public PreprocessIffStore(IComputation<IFormula> formula, Object... computations) {
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
        DependencyCache cache = new DependencyCache(hiddenVariables);

        for(IExpression child :formula.getChildren()){
            if(child instanceof BiImplies){
                BiImplies implies = (BiImplies) child;
                IExpression leftExpression = implies.getLeftExpression();
                IExpression rightExpression = implies.getRightExpression();
                if(leftExpression instanceof Literal ){
                    checkLiteralIsUnique((Literal) leftExpression,hiddenVariables,mapping,rightExpression,cache);
                }
                if( rightExpression instanceof Literal){
                    checkLiteralIsUnique((Literal) rightExpression,hiddenVariables,mapping,leftExpression,cache);
                }

            }
            //if a clause is unit clause and  literal is hidden variable remove it from booleanAssignment
            else if(child instanceof Literal){
                Variable unitClause = (Variable) child.getChildren().get(0);
                //TODO safe info in DependencyCache
                hiddenVariables = new BooleanAssignment(hiddenVariables.removeAll(mapping.get(unitClause.getName()).get()));
            }
        }
        BooleanAssignment finalHiddenVariables = hiddenVariables;
        ArrayList<Integer> removeHiddenFeatures = new ArrayList<>();
        //TODO use Info from dependencyCache to remove not indeterminate hidden features
        hiddenVariables = new BooleanAssignment(hiddenVariables.stream().toArray());
        return Result.of(hiddenVariables);
    }
    /**
     * check if one side of {@link BiImplies} only have {@link Literal}s which are not hidden or hidden features which aren't indeterminate,
     */
    private void checkLiteralIsUnique(Literal literal, BooleanAssignment hiddenVariables, VariableMap mapping, IExpression otherExpression, DependencyCache cache ) {
        IValue value = literal.getChildren().get(0);
        Integer id = mapping.get(value.getName()).get();
        if(hiddenVariables.contains(id)){
            List<Variable> variables = otherExpression.getVariables();
            for (Variable variable : variables){
                if(hiddenVariables.contains(mapping.get(variable.getName()).get())){
                    //TODO put Info in ArrayList
                }
            }
            //TODO safe Dependency in DependencyCache

        }
    }

    /**
     * help to cache unique assignments and not yet unique assignments
     */
    private class DependencyCache{
        private HashMap<Integer,Boolean[]> unique;
        private HashMap<Integer, ArrayList<ArrayList<Boolean[]>>> notYetUnique;

        public DependencyCache (BooleanAssignment hiddenVariable) {
            unique = new HashMap<>();
            notYetUnique = new HashMap<>();
            hiddenVariable.stream().forEach((hidden) -> {
                unique.put(hidden,new Boolean[] {false});
                notYetUnique.put(hidden,new ArrayList<>());
            });
        }
        public void setUnique(Integer hiddenId) {
            unique.get(hiddenId)[0] = true;
        }
        public Boolean[] getUnique(Integer hiddenId) {
            return unique.get(hiddenId);
        }
        public void setNotYetUnique(Integer hiddenId,ArrayList<Boolean[]> newDependency){
            notYetUnique.get(hiddenId).add(newDependency);
        }
        public BooleanAssignment removeHiddenVariables(BooleanAssignment hiddenVariables){
            ArrayList<Integer> hiddenNotIndeterminate = new ArrayList<>();
            unique.forEach((hidden, info) ->{
                if(info != null && info.length == 1  ){
                    if(info[0]){
                        hiddenNotIndeterminate.add(hidden);
                    }else {
                        ArrayList<ArrayList<Boolean[]>> allDep = notYetUnique.get(hidden);
                        for(ArrayList<Boolean[]> dep : allDep ) {
                            boolean notIndeterminate = true;
                            for( Boolean[] otherHidden: dep) {
                                if(otherHidden == null || otherHidden.length != 1 || !otherHidden[0]){
                                    notIndeterminate = false;
                                    break;
                                }
                            }
                            if(notIndeterminate){
                                hiddenNotIndeterminate.add(hidden);
                                break;
                            }
                        }
                    }
                }
            });
            return new BooleanAssignment(hiddenVariables.removeAll(hiddenNotIndeterminate.stream().mapToInt(Integer::intValue).toArray()));
        }
    }
}
