import Mathlib.Analysis.Calculus.MeanValue
import Submission.Work.Stability.Cutoff

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Stability

/-- A differentiable function with bounded derivative is Lipschitz (the mean value inequality
`lipschitzWith_of_nnnorm_fderiv_le`, applied to a bound extracted from `IsBoundedFun`). -/
theorem LipschitzOfBoundedFderiv {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F}
    (hf : Differentiable ℝ f) (hb : IsBoundedFun (fderiv ℝ f)) :
    ∃ K : NNReal, LipschitzWith K f := by
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.1 hb
  refine ⟨⟨max C 0, le_max_right _ _⟩, ?_⟩
  apply lipschitzWith_of_nnnorm_fderiv_le hf
  intro x
  exact (hC (fderiv ℝ f x) ⟨x, Set.mem_univ x, rfl⟩).trans (le_max_left _ _)

end Work.Stability
