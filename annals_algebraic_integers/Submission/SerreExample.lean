import Mathlib.Data.Real.Sqrt

/-!
# The constants of Serre's example

The parameters used in Smith's Annals 2024 example:

    a = 0.087353,  b = 4.411076,  γ = 0.215485.

Serre's measure on `[a,b]` is `μ = γ·ν + (1−γ)·μ_eq`; its first moment is
`γ·√(a·b) + (1−γ)·(a+b)/2`, which lies in `(1.898303, 1.898304)`, hence is
`< 1.89831`.  This module records those constants and proves the moment bound
by exact rational arithmetic (the only transcendental ingredient, `√(a·b)`, is
bracketed by rationals whose squares bracket `a·b`).
-/

noncomputable section

open scoped Real

namespace Submission.SerreExample

/-- Left endpoint of Serre's interval. -/
noncomputable def aSerre : ℝ := 0.087353

/-- Right endpoint of Serre's interval. -/
noncomputable def bSerre : ℝ := 4.411076

/-- Weight of the reciprocal part in Serre's measure. -/
noncomputable def gSerre : ℝ := 0.215485

lemma aSerre_pos : 0 < aSerre := by norm_num [aSerre]
lemma bSerre_pos : 0 < bSerre := by norm_num [bSerre]
lemma gSerre_pos : 0 < gSerre := by norm_num [gSerre]
lemma gSerre_le_one : gSerre ≤ 1 := by norm_num [gSerre]

/-- `√(a·b)` is bracketed by the rationals `0.620742` and `0.620743`. -/
lemma sqrt_ab_bracketed :
    0.620742 < Real.sqrt (aSerre * bSerre) ∧
      Real.sqrt (aSerre * bSerre) < 0.620743 := by
  constructor
  · -- (0.620742)² < a·b
    rw [Real.lt_sqrt]
    · norm_num [aSerre, bSerre]
    · norm_num
  · -- a·b < (0.620743)²
    rw [Real.sqrt_lt']
    · norm_num [aSerre, bSerre]
    · norm_num [aSerre, bSerre]

/-- The first moment of Serre's measure on `[a,b]` lies in `(1.898303, 1.898304)`. -/
lemma serre_moment_bounds :
    1.898303 < gSerre * Real.sqrt (aSerre * bSerre) + (1 - gSerre) * (aSerre + bSerre) / 2 ∧
      gSerre * Real.sqrt (aSerre * bSerre) + (1 - gSerre) * (aSerre + bSerre) / 2 < 1.898304 := by
  have hb := sqrt_ab_bracketed
  -- monotonicity of the affine map in the sqrt variable
  have hlo : 1.898303 < gSerre * 0.620742 + (1 - gSerre) * (aSerre + bSerre) / 2 := by
    norm_num [aSerre, bSerre, gSerre]
  have hhi : gSerre * 0.620743 + (1 - gSerre) * (aSerre + bSerre) / 2 < 1.898304 := by
    norm_num [aSerre, bSerre, gSerre]
  constructor
  · -- E(p) < E(s)
    have hmono1 : gSerre * 0.620742 + (1 - gSerre) * (aSerre + bSerre) / 2 <
        gSerre * Real.sqrt (aSerre * bSerre) + (1 - gSerre) * (aSerre + bSerre) / 2 := by
      have hstep : 0.620742 < Real.sqrt (aSerre * bSerre) := hb.1
      nlinarith [mul_lt_mul_of_pos_left hstep gSerre_pos]
    exact lt_trans hlo hmono1
  · have hmono2 : gSerre * Real.sqrt (aSerre * bSerre) + (1 - gSerre) * (aSerre + bSerre) / 2 <
        gSerre * 0.620743 + (1 - gSerre) * (aSerre + bSerre) / 2 := by
      have hstep : Real.sqrt (aSerre * bSerre) < 0.620743 := hb.2
      nlinarith [mul_lt_mul_of_pos_left hstep gSerre_pos]
    exact lt_trans hmono2 hhi

/-- Serre's moment is below `1.89831`. -/
lemma serre_moment_lt_189831 :
    gSerre * Real.sqrt (aSerre * bSerre) + (1 - gSerre) * (aSerre + bSerre) / 2 < 1.89831 := by
  have h := serre_moment_bounds.2
  norm_num at h ⊢
  linarith


/-- The interval has length greater than 4: capacity `(b−a)/4 > 1`. -/
lemma cap_gt_one : 4 < bSerre - aSerre := by norm_num [aSerre, bSerre]

/-- The interval endpoints are ordered. -/
lemma a_lt_b : aSerre < bSerre := by norm_num [aSerre, bSerre]
lemma a_le_b : aSerre ≤ bSerre := le_of_lt a_lt_b

/-- Serre's interval is contained in the positive reals. -/
lemma interval_pos : ∀ x : ℝ, x ∈ Set.Icc aSerre bSerre → 0 < x := by
  intro x hx
  linarith [aSerre_pos, hx.1]

end Submission.SerreExample
