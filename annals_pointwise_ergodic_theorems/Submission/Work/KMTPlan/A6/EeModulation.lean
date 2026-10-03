/-
# The character `ee (x) = exp (2πi x)` and the compact-support vanishing bound

Elementary facts about the exponential character `Work.KMTAreas.A7.ee` used by the
`ℓ¹`-bound `Work.KMTPlan.A6.TmKernel_l1_modulated` for the kernel of the modulated
Ionescu--Wainger projections.
-/
import Mathlib
import Submission.Work.KMTAreas.A7.Large.Defs

set_option autoImplicit false

namespace Work.KMTPlan.A6

open scoped FourierTransform

/-- `Work.KMTAreas.A7.ee x = exp (2πi x)` is the complex character underlying Mathlib's
`Real.fourierChar`. -/
lemma ee_eq_fourierChar (x : ℝ) : Work.KMTAreas.A7.ee x = (Real.fourierChar x : ℂ) := by
  rw [Work.KMTAreas.A7.ee, Real.fourierChar_apply]
  congr 1
  push_cast
  ring_nf

/-- `ee` is continuous. -/
lemma continuous_ee : Continuous Work.KMTAreas.A7.ee := by
  unfold Work.KMTAreas.A7.ee
  fun_prop

/-- `ee` is unimodular. -/
lemma norm_ee (x : ℝ) : ‖Work.KMTAreas.A7.ee x‖ = 1 := by
  rw [ee_eq_fourierChar]
  exact Circle.norm_coe _

/-- `ee` is a character. -/
lemma ee_add (x y : ℝ) :
    Work.KMTAreas.A7.ee (x + y) = Work.KMTAreas.A7.ee x * Work.KMTAreas.A7.ee y := by
  rw [ee_eq_fourierChar, ee_eq_fourierChar, ee_eq_fourierChar, ← Circle.coe_mul,
    AddChar.map_add_eq_mul]

/-- A compactly supported function on `ℝ` vanishes outside a symmetric interval `[-R,R]`. -/
lemma exists_abs_bound_of_hasCompactSupport {χ : ℝ → ℂ} (h : HasCompactSupport χ) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ y : ℝ, R ≤ |y| → χ y = 0 := by
  obtain ⟨r, hr⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℝ)).mp h.isCompact.isBounded
  refine ⟨|r| + 1, by positivity, fun y hy => ?_⟩
  by_contra hne
  have hy' : y ∈ Metric.closedBall (0 : ℝ) r := hr (subset_tsupport χ hne)
  rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at hy'
  linarith [le_abs_self r]

end Work.KMTPlan.A6
