import Mathlib.Analysis.Calculus.ContDiff.Operations
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Commons.Analysis.Calculus

/-- The map `w ↦ Function.update x i w` (which replaces the `i`-th coordinate of the
tuple `x` by `w`) is smooth of every order `k`. -/
theorem contDiff_update_apply {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (k : ℕ) (x : Fin n → E) (i : Fin n) : ContDiff ℝ k (fun w : E => Function.update x i w) := by
  exact contDiff_update (𝕜 := ℝ) k x i

end Commons.Analysis.Calculus