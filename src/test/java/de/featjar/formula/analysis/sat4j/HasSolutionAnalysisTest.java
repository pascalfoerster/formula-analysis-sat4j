package de.featjar.formula.analysis.sat4j;

import de.featjar.base.data.Computation;
import de.featjar.formula.assignment.VariableAssignment;
import de.featjar.formula.clauses.ToCNF;
import de.featjar.formula.structure.formula.Formula;
import org.junit.jupiter.api.Test;

import static de.featjar.formula.structure.Expressions.*;
import static org.junit.jupiter.api.Assertions.*;

public class HasSolutionAnalysisTest {
    @Test
    void hasSolution() {
        assertTrue(Computation.of((Formula) and(literal("x"), not(literal("y"))))
                .then(ToCNF.analysis)
                .then(c -> new HasSolutionAnalysis(c, new VariableAssignment(), 1000, 1000)) // todo: timeout 0 is not interpreted correctly
                .computeResult()
                .get());
        assertFalse(Computation.of(and(literal("x"), not(literal("x"))))
                .then(ToCNF.class)
                .then(c -> new HasSolutionAnalysis(c, new VariableAssignment(), 1000, 1000))
                .computeResult()
                .get());
    }
}