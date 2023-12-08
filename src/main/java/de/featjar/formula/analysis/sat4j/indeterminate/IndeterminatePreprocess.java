package de.featjar.formula.analysis.sat4j.indeterminate;

import de.featjar.base.computation.*;
import de.featjar.formula.analysis.VariableMap;
import de.featjar.formula.analysis.bool.BooleanAssignment;

abstract public class IndeterminatePreprocess extends AComputation<BooleanAssignment> {

    public static final Dependency<BooleanAssignment> VARIABLES_OF_INTEREST =
            Dependency.newDependency(BooleanAssignment.class);
    public static final Dependency<VariableMap> VARIABLE_MAP =
            Dependency.newDependency(VariableMap.class);

    public IndeterminatePreprocess ( Object... computations) {
        super(Computations.of(new BooleanAssignment()), Computations.of(new VariableMap()), computations);
    }
}
