package de.featjar.formula.analysis.sat4j.indeterminate;

import de.featjar.base.computation.*;
import de.featjar.base.data.Result;
import de.featjar.formula.analysis.VariableMap;
import de.featjar.formula.structure.IExpression;
import de.featjar.formula.structure.formula.IFormula;
import de.featjar.formula.structure.formula.connective.BiImplies;
import de.featjar.formula.structure.formula.connective.Or;
import de.featjar.formula.structure.formula.predicate.Literal;
import de.featjar.formula.structure.term.value.Variable;
import de.featjar.formula.transformer.ComputeCNFFormula;
import de.featjar.formula.transformer.ComputeNNFFormula;

import java.util.*;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

/**
 * Computation find BiImplikation which  are relevant for Indeterminate Analysis
 */
public class ComputeBiImplicationFormula extends AComputation<List<BiImplies>> {
    private static final Dependency<IFormula> CNF_FORMULA = Dependency.newDependency(IFormula.class);
    private static final Dependency<VariableMap> VARIABLE_MAP = Dependency.newDependency(VariableMap.class);
    @SuppressWarnings("unchecked")
    public static final Dependency<List<BiImplies>> ALREADY_EXISTING_BI_IMPL = Dependency.newDependency((Class<List<BiImplies>>)(Object)List.class);
    /**
     * Determines the maximum size of the clauses to be considered.
     * Default value is 2  and maximum 3
     */

    private ArrayList<int[]> twoClauses;
    private IFormula cnf;
    private int max_clause_size;
    private List<BiImplies> existing_BiImplies;
    private HashMap<int[],HashMap<Integer,ArrayList<int[]>>> possibleBiImplications = new HashMap<>();
    private VariableMap variableMap;
    public static final Dependency<Integer> MAXIMUM_CLAUSE_SIZE = Dependency.newDependency(Integer.class);

    /**
     * Creates a new CNF with Bi Impliakations formula computation.
     *
     * @param cnfFormula the input NNF formula computation
     */
    public ComputeBiImplicationFormula(IFormula cnfFormula,VariableMap map) {
        super(
                Computations.of(cnfFormula), //
                Computations.of(map),
                Computations.of(new ArrayList<>()),
                Computations.of(2));
    }

    @Override
    public Result<List<BiImplies>> compute(List<Object> dependencyList, Progress progress) {
        cnf =   CNF_FORMULA.get(dependencyList);
        max_clause_size = MAXIMUM_CLAUSE_SIZE.get(dependencyList);
        existing_BiImplies = ALREADY_EXISTING_BI_IMPL.get(dependencyList);
        variableMap = VARIABLE_MAP.get(dependencyList);
        twoClauses = new ArrayList<>();
        ArrayList<BiImplies> result = new ArrayList<>();
        if (!cnf.isCNF()) {
            throw new IllegalArgumentException("Formula is not in CNF");
        }
        if (max_clause_size < 2){
            return Result.of(result);
        }
        for (IExpression expression :cnf.getChildren()){
            List<Literal> variables = (List<Literal>) expression.getChildren();
            int[] clause = rewriteClause(variables);
            if(expression.getChildrenCount() == 2) {
                if (twoClauses.stream().noneMatch(exClause -> eqClause(exClause, clause))) {
                    twoClauses.add(clause);
                    if (twoClauses.stream().anyMatch((c1) -> findMatch(c1, clause))) {
                        result.add(createBiImplies(clause, 0));
                    }
                    possibleBiImplications.keySet().stream().filter(c1 -> findMatch(clause, c1)).forEach(longClause -> {
                        HashMap<Integer, ArrayList<int[]>> matches = possibleBiImplications.get(longClause);
                        addPossibleBiImplMatches(matches, clause);
                    });
                }
            }else if (expression.getVariables().size() <= max_clause_size && expression.getVariables().size() > 2) {
                if(possibleBiImplications.keySet().stream().noneMatch(exClause -> eqClause(exClause, clause))) {
                    HashMap<Integer, ArrayList<int[]>> matches = new HashMap<>();
                    twoClauses.stream().filter(twoClause -> findMatch(twoClause, clause)).collect(Collectors.toList()).forEach(twoClausesMatch -> {
                        addPossibleBiImplMatches(matches, twoClausesMatch);
                    });
                    possibleBiImplications.put(clause, matches);
                }
            }
        }
        ArrayList<BiImplies> finalResult = result;
        possibleBiImplications.forEach((clause, matches) -> {
            matches.forEach((value,match) -> {
                if(match.size() + 1 == clause.length ){
                    finalResult.add(createBiImplies(clause, IntStream.range(0, clause.length).filter(i -> clause[i] == value).findFirst().orElse(-1)));
                }
            });
        });
        result = (ArrayList<BiImplies>) result.stream().filter((biIm) -> existing_BiImplies.stream().noneMatch(biImEx -> equalsBiImplies(biImEx,biIm))).collect(Collectors.toList());
        return Result.of(result);
    }

    private void addPossibleBiImplMatches(HashMap<Integer,ArrayList<int[]>> matches, int[] twoClause){
        ArrayList<int[]> input = new ArrayList<>();
        if(matches.containsKey(-twoClause[0])){
            input = matches.get(-twoClause[0]);
            input.add(twoClause);
        }else{
            input.add(twoClause);
            matches.put(-twoClause[0],input);
        }
        ArrayList<int[]> input2 = new ArrayList<>();
        if(matches.containsKey(-twoClause[1])){
            input2 = matches.get(-twoClause[1]);
            input2.add(twoClause);
        }else{
            input2.add(twoClause);
            matches.put(-twoClause[1],input2);
        }
    }
    private boolean findMatch(int[] c1, int[] c2){
        return Arrays.stream(c1).allMatch((value -> Arrays.stream(c2).anyMatch(value2 ->-value == value2 )));
    }
    private boolean eqClause(int[] c1, int[] c2){
        if(c1.length != c2.length) return false;
        int[] c1sorted = Arrays.stream(c1).sorted().toArray();
        int[] c2sorted = Arrays.stream(c2).sorted().toArray();
        return IntStream.range(0,c1sorted.length).allMatch(index -> c1sorted[index] == c2sorted[index]);
    }
    private int[] rewriteClause(List<Literal> clause){
        int [] temp = new int [clause.size()];
        for(int index = 0; index < clause.size() ; index++){
            Literal literal = clause.get(index);
            Result<Integer> intValue = variableMap.get(literal.getExpression().getName());
            if(intValue.isPresent()) {
                temp[index] = literal.isPositive() ? intValue.get() : -intValue.get();
            }
        }
        return temp;
    }
    private BiImplies createBiImplies(int[] clause, int leftSideIndex){
        IFormula leftExpression = new Literal(true,new Variable(""));
        IFormula rightExpression;
        if ( clause.length == 2){
            int v1 = clause[0];
            int v2 = clause[1];
            Variable variable1 = new Variable(variableMap.get(Math.abs(v1)).get());
            Variable variable2 = new Variable(variableMap.get(Math.abs(v2)).get());
            leftExpression = new Literal(true,variable1);
            rightExpression = new Literal(v1 > 0 ? v2 < 0: v2 > 0,variable2);
        }else {
            rightExpression = new Or();
            for(int index = 0 ; index < clause.length; index ++ ) {
                int value = clause[index];
                Variable variable = new Variable(variableMap.get(Math.abs(value)).get());
                if(index == leftSideIndex) {
                    leftExpression = new Literal(value < 0, variable);
                } else{
                    rightExpression.addChild(new Literal(value > 0,variable));
                }
            }

        }
        return new BiImplies(leftExpression,rightExpression);
    }

    private boolean equalsBiImplies(BiImplies biIm1, BiImplies biIm2) {
        IFormula cnf1 = Computations.of((IFormula) biIm1).map(ComputeNNFFormula::new).map(ComputeCNFFormula::new).compute();
        IFormula cnf2 = Computations.of((IFormula) biIm2).map(ComputeNNFFormula::new).map(ComputeCNFFormula::new).compute();
        Comparator<IExpression> comparator = (formula1, formula2) -> {
            String exp1String = formula1.toString();
            String exp2String = formula2.toString();
            if (formula1 instanceof Or && formula2 instanceof Or) {
                Optional<String> exp1Result = formula1.getChildren().stream().map(x -> x.getChildren().get(0).getName()).reduce((y1, y2) -> y1 + y2);
                Optional<String> exp2Result = formula2.getChildren().stream().map(x -> x.getChildren().get(0).getName()).reduce((y1, y2) -> y1 + y2);
                if (exp1Result.isPresent() && exp2Result.isPresent()) {
                    exp1String = exp1Result.get();
                    exp2String = exp2Result.get();
                }
            }
            return exp1String.compareTo(exp2String);
        };
        cnf1.sort(comparator);
        cnf2.sort(comparator);
        return cnf1.equalsTree(cnf2);

    }



}
