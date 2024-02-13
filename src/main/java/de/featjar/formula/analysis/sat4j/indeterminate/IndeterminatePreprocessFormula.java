package de.featjar.formula.analysis.sat4j.indeterminate;

import de.featjar.base.computation.Computations;
import de.featjar.base.computation.Dependency;
import de.featjar.base.computation.IComputation;
import de.featjar.formula.analysis.VariableMap;
import de.featjar.formula.analysis.bool.BooleanAssignment;
import de.featjar.formula.structure.formula.IFormula;
import de.featjar.formula.structure.formula.connective.BiImplies;

import java.util.List;

public abstract class IndeterminatePreprocessFormula extends  IndeterminatePreprocess{
    protected static final Dependency<IFormula> FORMULA =
            Dependency.newDependency(IFormula.class);
    private IFormula formula;

    public IndeterminatePreprocessFormula (IComputation<IFormula> formula, Object... computations) {
        super(formula, computations);
        this.formula = formula.compute();
    }

    public IndeterminatePreprocess addBiImplies(List<BiImplies> biImplies) {
        biImplies.forEach(formula::addChild);
        return this;
    }

}
