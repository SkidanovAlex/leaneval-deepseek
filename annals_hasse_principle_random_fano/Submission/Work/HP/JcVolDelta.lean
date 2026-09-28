import Mathlib
import Submission.Work.HP.JcVolDefs

/-!
# Positivity of `δ_{w,z} = ‖w‖²‖z‖² - ⟪w,z⟫²`

For linearly independent `w z` the Gram determinant `deltaV w z` is strictly positive.
This is the strict form of the Cauchy--Schwarz inequality: equality in
`|⟪w,z⟫| ≤ ‖w‖‖z‖` forces `w` and `z` to be proportional (`abs_real_inner_div_norm_mul_norm_eq_one_iff`),
which linear independence forbids.
-/

set_option autoImplicit false
noncomputable section

open Filter Finset MeasureTheory
open scoped RealInnerProductSpace

namespace Work.HP

theorem JcVolDelta {ι : Type*} [Fintype ι] {w z : EuclideanSpace ℝ ι} (h : IsIndep w z) :
    0 < deltaV w z := by
  have h' : LinearIndependent ℝ ![w, z] := h
  have hw : w ≠ 0 := by simpa using LinearIndependent.ne_zero (0 : Fin 2) h'
  have hz : z ≠ 0 := by simpa using LinearIndependent.ne_zero (1 : Fin 2) h'
  -- `z` is not a multiple of `w`
  have hzn : ∀ a : ℝ, a • w ≠ z := (LinearIndependent.pair_iff' hw).mp h'
  have hnorm : 0 < ‖w‖ * ‖z‖ :=
    mul_pos (norm_pos_iff.mpr hw) (norm_pos_iff.mpr hz)
  -- strict Cauchy--Schwarz
  have hab : |inner ℝ w z / (‖w‖ * ‖z‖)| ≠ 1 := by
    intro h1
    obtain ⟨_, r, _, hrz⟩ := (abs_real_inner_div_norm_mul_norm_eq_one_iff w z).mp h1
    exact hzn r hrz.symm
  have hle : |inner ℝ w z / (‖w‖ * ‖z‖)| ≤ 1 := abs_real_inner_div_norm_mul_norm_le_one w z
  have hlt1 : |inner ℝ w z / (‖w‖ * ‖z‖)| < 1 := lt_of_le_of_ne hle hab
  have habs : |inner ℝ w z| < ‖w‖ * ‖z‖ := by
    rw [abs_div, abs_of_nonneg (le_of_lt hnorm), div_lt_one hnorm] at hlt1
    exact hlt1
  -- factor the Gram determinant
  have hd : deltaV w z =
      (‖w‖ * ‖z‖ - |inner ℝ w z|) * (‖w‖ * ‖z‖ + |inner ℝ w z|) := by
    rw [deltaV, ← sq_abs (inner ℝ w z), ← mul_pow]
    ring
  rw [hd]
  exact mul_pos (by linarith) (by linarith [abs_nonneg (inner ℝ w z), hnorm])

end Work.HP
