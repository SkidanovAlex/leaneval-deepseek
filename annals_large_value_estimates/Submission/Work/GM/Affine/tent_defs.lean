import Mathlib
import Submission.Work.GM.Affine.setup

/-!
# The triangular ("tent") weight

For `T : ℝ` we define the tent function `tent T u = max 0 (T - |u|)`: nonnegative, continuous,
supported in `[-T, T]`, with maximum `T` and integral `T ^ 2` over the real line.

This is the weight used in `Work.GM.Affine.Tent_core`: the Fourier (cosine) coefficients
`∫ tent T u * cos (2 π d u) du` are nonnegative, which turns the (positive definite) quadratic form
`∫ tent T u * ‖∑ a_ℓ e (ℓ u)‖ ^ 2 du` into a lower bound `T ^ 2 * ∑ a_ℓ ^ 2`.
-/

open MeasureTheory

set_option autoImplicit false

namespace Work.GM.Affine

noncomputable section

/-- The triangular weight of height `T` supported on `[-T, T]`. -/
noncomputable def tent (T : ℝ) (u : ℝ) : ℝ := max 0 (T - |u|)

lemma tent_nonneg (T u : ℝ) : 0 ≤ tent T u := le_max_left _ _

lemma tent_apply (T u : ℝ) : tent T u = max 0 (T - |u|) := rfl

lemma tent_eq_zero_of_le {T u : ℝ} (h : T ≤ |u|) : tent T u = 0 := by
  rw [tent, max_eq_left (sub_nonpos.mpr h)]

lemma tent_le_of_nonneg {T : ℝ} (hT : 0 ≤ T) (u : ℝ) : tent T u ≤ T :=
  max_le hT (sub_le_self _ (abs_nonneg u))

lemma tent_le_self (T u : ℝ) : tent T u ≤ max 0 T :=
  max_le_max le_rfl (sub_le_self _ (abs_nonneg u))

lemma tent_continuous (T : ℝ) : Continuous (tent T) := by
  unfold tent
  fun_prop

lemma tent_eq_of_mem {T u : ℝ} (hu : |u| ≤ T) : tent T u = T - |u| := by
  rw [tent, max_eq_right]
  linarith

end

end Work.GM.Affine
