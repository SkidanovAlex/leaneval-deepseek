import Mathlib.Analysis.Normed.Ring.Lemmas

namespace Commons.Analysis.Normed

theorem intVec_coord_norm_le_norm {σ : Type*} [Fintype σ] (x : σ → ℤ) (i : σ) :
    (‖x i‖ : ℝ) ≤ ‖x‖ := by
  exact norm_le_pi_norm x i

end Commons.Analysis.Normed