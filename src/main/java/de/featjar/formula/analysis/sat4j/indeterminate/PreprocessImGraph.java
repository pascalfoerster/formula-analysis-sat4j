package de.featjar.formula.analysis.sat4j.indeterminate;

import de.featjar.base.computation.Dependency;
import de.featjar.base.computation.IComputation;
import de.featjar.base.computation.Progress;
import de.featjar.base.data.Result;
import de.featjar.formula.analysis.VariableMap;
import de.featjar.formula.analysis.bool.BooleanAssignment;
import de.featjar.formula.analysis.mig.solver.ModalImplicationGraph;
import de.featjar.formula.structure.formula.IFormula;

import java.util.Arrays;
import java.util.List;

public class PreprocessImGraph extends IndeterminatePreprocess{

    private static final Dependency<ModalImplicationGraph> IMPLICATION_GRAPH =
            Dependency.newDependency(ModalImplicationGraph.class);
    public PreprocessImGraph(IComputation<ModalImplicationGraph> booleanClauseList) {
        super(booleanClauseList);
    }

    @Override
    public Result<BooleanAssignment> compute(List<Object> dependencyList, Progress progress) {
        BooleanAssignment hiddenVariables = VARIABLES_OF_INTEREST.get(dependencyList);
        ModalImplicationGraph implicationGraph = IMPLICATION_GRAPH.get(dependencyList);
        ModalImplicationGraph.Visitor visitor = implicationGraph.getVisitor();
        hiddenVariables = new BooleanAssignment(hiddenVariables.removeAll(Arrays.stream(implicationGraph.getCore()).map(Math::abs).toArray()));
        BooleanAssignment finalHiddenVariables = hiddenVariables;
        hiddenVariables = new BooleanAssignment(hiddenVariables.stream().filter((hidden) ->{
            int[] strongLinkPositive =  implicationGraph.getStrong()[ModalImplicationGraph.getVertexIndex(hidden)];
            for(int check :strongLinkPositive){
                int posCheck = Math.abs(check);
                if(!finalHiddenVariables.containsVariable(posCheck) && visitor.strongLink(hidden,posCheck)){
                    return false;
                }
            }
            return true;
        }).toArray());
        return Result.of(hiddenVariables);
    }
}
