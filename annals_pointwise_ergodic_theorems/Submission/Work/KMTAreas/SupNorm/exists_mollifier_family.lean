import Mathlib

/-!
# A family of smooth mollifiers with shrinking supports

This file provides the approximate identity used in the smoothing arguments of the `KMTAreas`
development: a sequence of non-negative `C²` functions of total mass `1` whose support shrinks to
the origin, `supp (ρ n) ⊆ [-1/(n+1), 1/(n+1)]`.

The construction is the standard one: take a single normalised bump function `mollBump`
(equal to `1` on `[-1/2,1/2]`, supported in the open unit ball, non-negative, of integral `1`,
obtained from `ContDiffBump.normed`), and set `ρ n b = (n+1) * mollBump ((n+1) * b)`.  The
scaling by the factor `n+1` preserves the total mass and shrinks the support by exactly that
factor.

## Main result

* `Work.KMTAreas.SupNorm.exists_mollifier_family`
-/

namespace Work.KMTAreas.SupNorm

open MeasureTheory

/-- A fixed smooth bump: it equals `1` on the closed ball of radius `1/2`, its support is the
open unit ball, it is non-negative, and after normalisation it has total mass `1`. -/
noncomputable def mollBumpStruct : ContDiffBump (0 : ℝ) :=
  ⟨1 / 2, 1, by norm_num, by norm_num⟩

/-- The normalised bump function attached to `mollBumpStruct`: a non-negative `C^∞` function
with `∫ b, mollBump b = 1` whose support is the open unit ball. -/
noncomputable def mollBump : ℝ → ℝ := mollBumpStruct.normed volume

lemma mollBump_contDiff : ContDiff ℝ 2 mollBump :=
  ContDiffBump.contDiff_normed mollBumpStruct

lemma mollBump_hasCompactSupport : HasCompactSupport mollBump :=
  ContDiffBump.hasCompactSupport_normed mollBumpStruct

lemma mollBump_nonneg (b : ℝ) : 0 ≤ mollBump b :=
  ContDiffBump.nonneg_normed mollBumpStruct b

lemma mollBump_integral : ∫ b, mollBump b = 1 :=
  ContDiffBump.integral_normed mollBumpStruct

/-- The support of the normalised bump is the open unit ball. -/
lemma mollBump_support {b : ℝ} (hb : mollBump b ≠ 0) : |b| < 1 := by
  have h : b ∈ Function.support mollBump := hb
  rw [mollBump, ContDiffBump.support_normed_eq] at h
  simp only [Metric.mem_ball, Real.dist_eq, sub_zero] at h
  exact h

theorem exists_mollifier_family :
    ∃ ρ : ℕ → ℝ → ℝ,
      (∀ n, ContDiff ℝ 2 (ρ n)) ∧ (∀ n, HasCompactSupport (ρ n)) ∧
      (∀ n b, 0 ≤ ρ n b) ∧ (∀ n, ∫ b, ρ n b = 1) ∧
      (∀ n b, ρ n b ≠ 0 → |b| ≤ (1 : ℝ) / (n + 1)) := by
  refine ⟨fun n b => ((n : ℝ) + 1) * mollBump (((n : ℝ) + 1) * b), ?_, ?_, ?_, ?_, ?_⟩
  · -- Smoothness: composition with the linear map `b ↦ (n+1) * b`, times the constant `n+1`.
    intro n
    show ContDiff ℝ 2 (fun b : ℝ => ((n : ℝ) + 1) * mollBump (((n : ℝ) + 1) * b))
    have hlin : ContDiff ℝ 2 (fun b : ℝ => ((n : ℝ) + 1) * b) :=
      contDiff_const.mul contDiff_id
    exact contDiff_const.mul (mollBump_contDiff.comp hlin)
  · -- Compact support: rescale the compactly supported bump and multiply by a constant.
    intro n
    show HasCompactSupport (fun b : ℝ => ((n : ℝ) + 1) * mollBump (((n : ℝ) + 1) * b))
    have h1 : HasCompactSupport (fun b : ℝ => mollBump (((n : ℝ) + 1) * b)) :=
      mollBump_hasCompactSupport.comp_smul (c := ((n : ℝ) + 1)) (by positivity)
    have heq : ((fun _ : ℝ => ((n : ℝ) + 1)) •
          (fun b : ℝ => mollBump (((n : ℝ) + 1) * b)))
        = (fun b : ℝ => ((n : ℝ) + 1) * mollBump (((n : ℝ) + 1) * b)) := by
      funext b; simp [smul_eq_mul]
    rw [← heq]
    exact h1.smul_left (f := fun _ : ℝ => ((n : ℝ) + 1))
  · -- Non-negativity.
    intro n b
    show 0 ≤ ((n : ℝ) + 1) * mollBump (((n : ℝ) + 1) * b)
    exact mul_nonneg (by positivity) (mollBump_nonneg _)
  · -- Total mass one: the scaling factor is compensated by the change of variables.
    intro n
    show ∫ b : ℝ, ((n : ℝ) + 1) * mollBump (((n : ℝ) + 1) * b) = 1
    have hscale : ∫ b : ℝ, mollBump (((n : ℝ) + 1) * b) = ((n : ℝ) + 1)⁻¹ := by
      have habs : |((n : ℝ) + 1)⁻¹| = ((n : ℝ) + 1)⁻¹ := abs_of_pos (by positivity)
      rw [Measure.integral_comp_mul_left, mollBump_integral, habs]
      simp
    rw [integral_const_mul, hscale]
    exact mul_inv_cancel₀ (by positivity)
  · -- The support shrinks like `1/(n+1)`.
    intro n b hb
    show |b| ≤ (1 : ℝ) / (n + 1)
    have hb' : mollBump (((n : ℝ) + 1) * b) ≠ 0 := by
      intro h
      apply hb
      show ((n : ℝ) + 1) * mollBump (((n : ℝ) + 1) * b) = 0
      rw [h, mul_zero]
    have h1 : |((n : ℝ) + 1) * b| < 1 := mollBump_support hb'
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < ((n : ℝ) + 1))] at h1
    have h2 : |b| < 1 / ((n : ℝ) + 1) := by
      rw [lt_div_iff₀ (by positivity : (0 : ℝ) < ((n : ℝ) + 1))]
      linarith
    exact le_of_lt h2

end Work.KMTAreas.SupNorm
