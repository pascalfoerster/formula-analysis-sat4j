package de.featjar.formula.analysis.sat4j.indeterminate;

import de.featjar.base.computation.Dependency;
import de.featjar.base.computation.IComputation;
import de.featjar.base.computation.Progress;
import de.featjar.base.data.Result;
import de.featjar.formula.analysis.bool.BooleanAssignment;
import de.featjar.formula.structure.formula.IFormula;

import java.util.List;

public class PreprocessIff extends IndeterminatePreprocess{
    public static final Dependency<IFormula> FORMULA =
            Dependency.newDependency(IFormula.class);
    public PreprocessIff(IComputation<IFormula> formula, Object... computations) {
        super(formula, computations);
    }

    @Override
    public Result<BooleanAssignment> compute(List<Object> dependencyList, Progress progress) {
        return null;
    }
}
