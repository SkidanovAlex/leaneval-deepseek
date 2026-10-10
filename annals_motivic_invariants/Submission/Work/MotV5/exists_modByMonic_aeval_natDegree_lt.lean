import Mathlib

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotV5

theorem exists_modByMonic_aeval_natDegree_lt {K L : Type*} [Field K] [Field L] [Algebra K L]
    (α x : L) (hα : IsIntegral K α) (hx : x ∈ IntermediateField.adjoin K {α}) :
    ∃ r : Polynomial K, Polynomial.aeval α r = x ∧ r.natDegree < (minpoly K α).natDegree := by
  have hαa : IsAlgebraic K α := hα.isAlgebraic
  -- The intermediate field `K⟮α⟯` coincides with the ring `K[α]` because `α` is algebraic.
  have hsub : (IntermediateField.adjoin K {α}).toSubalgebra = Algebra.adjoin K {α} :=
    IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hαa
  have hmem : x ∈ Algebra.adjoin K {α} := by
    rw [← hsub]
    exact hx
  -- `K[α]` is the range of the evaluation map at `α`.
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hmem
  obtain ⟨p, hp⟩ := hmem
  -- Reduce `p` modulo the minimal polynomial of `α`.
  refine ⟨p %ₘ minpoly K α, ?_, ?_⟩
  · rw [minpoly.aeval_modByMonic_minpoly]
    exact hp
  · exact Polynomial.natDegree_modByMonic_lt p (minpoly.monic hα) (by
      intro h
      have := minpoly.natDegree_pos hα
      rw [h] at this
      simp at this)

end Work.MotV5
