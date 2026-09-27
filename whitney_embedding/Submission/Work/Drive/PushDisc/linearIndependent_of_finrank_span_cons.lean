import Mathlib

namespace Work.Drive.PushDisc

/-- If the span of `{b} ∪ range V` (for `V : Fin k → E`) has dimension `k + 1`, then `V` is
linearly independent and `b` is not in the span of `V`. -/
theorem linearIndependent_of_finrank_span_cons {E : Type*} [AddCommGroup E] [Module ℝ E]
    [Module.Finite ℝ E] {k : ℕ} {V : Fin k → E} {b : E}
    (h : Module.finrank ℝ (Submodule.span ℝ (Set.range (Fin.cons b V))) = k + 1) :
    LinearIndependent ℝ V ∧ b ∉ Submodule.span ℝ (Set.range V) := by
  -- The family `Fin.cons b V` spans a space of dimension `k + 1`, i.e. of dimension equal to the
  -- number of its terms; hence it is linearly independent.
  have hLI : LinearIndependent ℝ (Fin.cons b V) := by
    rw [linearIndependent_iff_card_eq_finrank_span, Fintype.card_fin]
    exact h.symm
  exact linearIndependent_finCons.mp hLI

end Work.Drive.PushDisc
