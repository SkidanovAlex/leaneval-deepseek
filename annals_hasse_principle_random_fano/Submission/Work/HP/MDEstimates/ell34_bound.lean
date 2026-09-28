import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.Sig2.num_lattices_of
import Submission.Work.HP.Sig2.ellXY_pair_le
import Submission.Work.HP.Q44Child.ballCount_le

namespace Work.HP.MDEstimates

/-- The rank-3 pair count with `X = Y = Z` at `n = 4`, obtained from the general
pair-count estimate `Work.HP.Sig2.ellXY_pair_le`. -/
theorem ell34_bound :
    ∃ K : ℝ, 0 < K ∧ ∀ Z Δ : ℝ, 1 ≤ Z → 1 ≤ Δ →
      (ellXY 4 3 Z Z Δ : ℝ) ≤ K * Z ^ 6 * Δ ^ 3 * Real.log (2 * Δ) ^ 2 := by
  obtain ⟨K, hK, hK'⟩ := Work.HP.Sig2.ellXY_pair_le 4 (by norm_num) 3 (by norm_num) (by omega)
  refine ⟨K, hK, fun Z Δ hZ hΔ => ?_⟩
  have h := hK' Z Δ hZ hΔ
  simpa using h

end Work.HP.MDEstimates
