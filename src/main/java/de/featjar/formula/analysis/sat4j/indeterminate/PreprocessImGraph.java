package de.featjar.formula.analysis.sat4j.indeterminate;

import de.featjar.base.computation.Dependency;
import de.featjar.base.computation.IComputation;
import de.featjar.base.computation.Progress;
import de.featjar.base.data.Result;
import de.featjar.formula.analysis.bool.BooleanAssignment;
import de.featjar.formula.analysis.mig.solver.ModalImplicationGraph;
import de.featjar.formula.structure.formula.IFormula;

import java.util.List;

public class PreprocessImGraph extends IndeterminatePreprocess{

    public static final Dependency<ModalImplicationGraph> IMPLICATION_GRAPH =
            Dependency.newDependency(ModalImplicationGraph.class);
    public PreprocessImGraph(IComputation<ModalImplicationGraph> booleanClauseList, Object... computations) {
        super(booleanClauseList, computations);
    }

    @Override
    public Result<BooleanAssignment> compute(List<Object> dependencyList, Progress progress) {
        return null;
    }
}
