import Mathlib
import Submission.Work.BMF.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.N8

theorem poly_le_exp (A deg η s : ℝ) (hA : 0 ≤ A) (hη : 0 < η) (hs : 0 < s) :
    ∃ N : ℝ, 1 ≤ N ∧ ∀ X : ℝ, N ≤ X → A * X ^ deg ≤ Real.exp (η * X ^ s) := by
  rcases eq_or_lt_of_le hA with hA0 | hApos
  · -- trivial case A = 0
    refine ⟨1, le_refl 1, fun X _ => ?_⟩
    rw [← hA0, zero_mul]
    exact (Real.exp_pos _).le
  have hη2 : 0 < η / 2 := by linarith
  -- eventually: log A ≤ η/2 * X^s
  have htend : Filter.Tendsto (fun X : ℝ => η / 2 * X ^ s) Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop hs).const_mul_atTop hη2
  have h1 : ∀ᶠ X in Filter.atTop, Real.log A ≤ η / 2 * X ^ s :=
    htend.eventually_ge_atTop (Real.log A)
  -- eventually: (max deg 0) * log X ≤ η/2 * X^s
  have h2 : ∀ᶠ X in Filter.atTop, max deg 0 * Real.log X ≤ η / 2 * X ^ s := by
    rcases eq_or_lt_of_le (le_max_right deg 0) with hD0 | hDpos
    · filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with X hX
      rw [← hD0, zero_mul]
      exact mul_nonneg hη2.le (Real.rpow_nonneg hX s)
    · have hb : ∀ᶠ X in Filter.atTop,
          ‖Real.log X‖ ≤ (η / 2 / max deg 0) * ‖X ^ s‖ :=
        (isLittleO_log_rpow_atTop hs).bound (div_pos hη2 hDpos)
      filter_upwards [hb, Filter.eventually_ge_atTop (1 : ℝ)] with X hbX hX
      have hXpos : 0 < X := lt_of_lt_of_le zero_lt_one hX
      rw [Real.norm_of_nonneg (Real.log_nonneg hX),
        Real.norm_of_nonneg (Real.rpow_nonneg hXpos.le s)] at hbX
      have hstep := mul_le_mul_of_nonneg_left hbX hDpos.le
      rw [← mul_assoc, mul_div_cancel₀ (η / 2) hDpos.ne'] at hstep
      exact hstep
  -- combine into the desired eventual inequality
  have hmain : ∀ᶠ X in Filter.atTop, A * X ^ deg ≤ Real.exp (η * X ^ s) := by
    filter_upwards [h1, h2, Filter.eventually_ge_atTop (1 : ℝ)] with X h1X h2X hX
    have hXpos : 0 < X := lt_of_lt_of_le zero_lt_one hX
    have hdle : deg * Real.log X ≤ max deg 0 * Real.log X :=
      mul_le_mul_of_nonneg_right (le_max_left deg 0) (Real.log_nonneg hX)
    have hsum : Real.log A + deg * Real.log X ≤ η * X ^ s := by
      have h := add_le_add h1X (le_trans hdle h2X)
      have heq : η / 2 * X ^ s + η / 2 * X ^ s = η * X ^ s := by ring
      rw [← heq]
      exact h
    have hpos : 0 < A * X ^ deg := mul_pos hApos (Real.rpow_pos_of_pos hXpos deg)
    refine (Real.log_le_iff_le_exp hpos).mp ?_
    rw [Real.log_mul hApos.ne' (Real.rpow_pos_of_pos hXpos deg).ne', Real.log_rpow hXpos]
    exact hsum
  rcases Filter.eventually_atTop.1 hmain with ⟨a, ha⟩
  exact ⟨max a 1, le_max_right a 1, fun X hX => ha X (le_trans (le_max_left a 1) hX)⟩

end Work.N8
