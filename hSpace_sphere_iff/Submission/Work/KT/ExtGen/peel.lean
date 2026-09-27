import Mathlib
import Submission.Work.KT.ExtGen.Basic

namespace Work.KT.ExtGen

/-- ROUTE (node `ext_generator`, its dependency): splitting off a two-dimensional factor.

For a finite-dimensional real normed space `W` of dimension `2k` with `k ≥ 1` there is a linear
isomorphism `W ≃ₗ[ℝ] (Std (2*(k-1)) × R2)`; here `Std n = Fin n → ℝ` (sup norm) and
`R2 = ℝ × ℝ` (maximum norm).  No isometry is required: the node `ext_generator` transports the pair
structure across an arbitrary linear isomorphism via the "change of norm" homeomorphism, so it
suffices to match dimensions.

Simplest route: both sides have the same finite `finrank` over `ℝ` (use
`Module.finrank_fin_fun`-style lemmas, `Module.finrank_prod`, and `2*k = 2*(k-1) + 2` for `k ≥ 1`),
so `LinearEquiv.ofFinrankEq` applies.  Alternative: `Module.finBasis ℝ W` composed with a
reindexing `Fin (2*k) ≃ Fin (2*(k-1)) ⊕ Fin 2` (`finSumFinEquiv` plus arithmetic) and
`LinearEquiv.sumArrowLequivProdArrow`, then `Fin 2 → ℝ ≃ₗ ℝ × ℝ`. -/
theorem peel (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W]
    [FiniteDimensional ℝ W] (k : ℕ) (hk : 1 ≤ k) (hWd : Module.finrank ℝ W = 2 * k) :
    Nonempty (W ≃ₗ[ℝ] (Std (2 * (k - 1)) × R2)) := by
  rw [FiniteDimensional.nonempty_linearEquiv_iff_finrank_eq]
  rw [hWd, Module.finrank_prod, Module.finrank_fin_fun]
  have h2 : Module.finrank ℝ R2 = 2 := by
    show Module.finrank ℝ (ℝ × ℝ) = 2
    rw [Module.finrank_prod, Module.finrank_self]
  rw [h2]
  omega

end Work.KT.ExtGen
