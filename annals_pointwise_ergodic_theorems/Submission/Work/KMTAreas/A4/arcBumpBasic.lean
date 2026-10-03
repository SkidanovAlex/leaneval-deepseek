/-
# Elementary facts about the rescaled bump `arcBump0` of `Work.KMTAreas.A4.lip2ArcDefs`

`arcBump0 u = lipSchChi (4u/3)` is the bump `1` for `|u| ≤ 3/8` and `0` for `|u| ≥ 3/4`.  This
file collects the elementary facts about it that the theory of the tiling bump `arcChi` needs:

* `arcBump0_eq_ofReal : arcBump0 u = (arcBumpR u : ℂ)` with `arcBumpR u = lipSchBump (4u/3) : ℝ`
  -- so `arcBump0` is a *nonnegative real* function;
* `arcBump0_eq_zero u (hu : 3/4 ≤ |u|) : arcBump0 u = 0` (its support);
* `arcBump0_zero : arcBump0 0 = 1`, `arcBumpR_pos` (strict positivity on `(-3/4,3/4)`),
  `arcBump0_contDiff`.

The available names are exactly
`arcBumpR`, `arcBump0_eq_ofReal`, `arcBumpR_nonneg`, `arcBumpR_le_one`, `arcBumpR_pos`,
`arcBumpR_eq_zero`, `arcBump0_eq_zero`, `arcBump0_eq_zero_of_one_le`, `arcBumpR_zero`,
`arcBump0_zero`, `arcBumpR_contDiff`, `arcBump0_contDiff`.
-/
import Mathlib
import Submission.Work.KMTAreas.A4.lip2ArcDefs

set_option autoImplicit false

open scoped BigOperators FourierTransform
open MeasureTheory

namespace Work.KMTAreas.A4

/-- The real-valued version of the rescaled bump `arcBump0`: `arcBumpR u = lipSchBump (4u/3)`. -/
noncomputable def arcBumpR (u : ℝ) : ℝ := lipSchBump (u * (4 / 3))

theorem arcBump0_eq_ofReal (u : ℝ) : arcBump0 u = (arcBumpR u : ℂ) := rfl

theorem arcBumpR_nonneg (u : ℝ) : 0 ≤ arcBumpR u := lipSchBump.nonneg

theorem arcBumpR_le_one (u : ℝ) : arcBumpR u ≤ 1 := lipSchBump.le_one

/-- `arcBumpR` is strictly positive on the interior `(-3/4, 3/4)` of its support. -/
theorem arcBumpR_pos (u : ℝ) (hu : |u| < 3 / 4) : 0 < arcBumpR u := by
  apply lipSchBump.pos_of_mem_ball
  rw [Metric.mem_ball, dist_eq_norm, sub_zero, Real.norm_eq_abs, abs_mul,
    abs_of_pos (by norm_num : (0 : ℝ) < 4 / 3), lipSchBump_rOut]
  linarith

/-- `arcBumpR` vanishes off `(-3/4, 3/4)`. -/
theorem arcBumpR_eq_zero (u : ℝ) (hu : 3 / 4 ≤ |u|) : arcBumpR u = 0 := by
  apply lipSchBump.zero_of_le_dist
  rw [dist_eq_norm, sub_zero, Real.norm_eq_abs, abs_mul,
    abs_of_pos (by norm_num : (0 : ℝ) < 4 / 3), lipSchBump_rOut]
  linarith

theorem arcBump0_eq_zero (u : ℝ) (hu : 3 / 4 ≤ |u|) : arcBump0 u = 0 := by
  rw [arcBump0_eq_ofReal, arcBumpR_eq_zero u hu, Complex.ofReal_zero]

theorem arcBump0_eq_zero_of_one_le (u : ℝ) (hu : 1 ≤ |u|) : arcBump0 u = 0 :=
  arcBump0_eq_zero u (by linarith)

theorem arcBumpR_zero : arcBumpR 0 = 1 := by
  apply lipSchBump.one_of_mem_closedBall
  rw [Metric.mem_closedBall, dist_eq_norm, sub_zero, Real.norm_eq_abs, zero_mul, abs_zero,
    lipSchBump_rIn]
  norm_num

theorem arcBump0_zero : arcBump0 0 = 1 := by
  rw [arcBump0_eq_ofReal, arcBumpR_zero, Complex.ofReal_one]

theorem arcBumpR_contDiff : ContDiff ℝ (⊤ : ℕ∞) arcBumpR := by
  have h : ContDiff ℝ (⊤ : ℕ∞) (fun u : ℝ => u * (4 / 3)) :=
    contDiff_id.mul contDiff_const
  exact (lipSchBump.contDiff (n := ⊤)).comp h

theorem arcBump0_contDiff : ContDiff ℝ (⊤ : ℕ∞) arcBump0 := by
  have h : ContDiff ℝ (⊤ : ℕ∞) (fun u : ℝ => u * (4 / 3)) :=
    contDiff_id.mul contDiff_const
  have h2 : ContDiff ℝ (⊤ : ℕ∞) arcBumpR := (lipSchBump.contDiff (n := ⊤)).comp h
  exact Complex.ofRealCLM.contDiff.comp h2

end Work.KMTAreas.A4
