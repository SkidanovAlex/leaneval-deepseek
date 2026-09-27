import Mathlib
import Submission.Work.Mostow.BaryBase
import Submission.Work.Mostow.BusemannRay

/-!
# The explicit formula for the Busemann function

For `ξ ∈ Sph n` (a unit vector) and `y ≠ 0` we prove the closed formula

`busemann ξ y = -hdist 0 y + log (1 + (1 - ⟪ŷ, ξ⟫) * ((exp (2 * hdist 0 y) - 1) / 2))`,
where `ŷ = (‖y‖)⁻¹ • y`,

together with the elementary lower bound `-hdist 0 y ≤ busemann ξ y`.

## Proof

Write `d = hdist 0 y` and `c = ⟪ŷ, ξ⟫`.  From `BaryBase` we have `tpart y = cosh d`,
`‖y‖ = sinh d` and `inner ℝ y ξ = ‖y‖ * c` (because `y ≠ 0`).  Hence

`tpart y - inner ℝ y ξ = cosh d - sinh d * c = exp (-d) + (1 - c) * sinh d`.

Since `c ≤ 1` (Cauchy–Schwarz, as `‖ŷ‖ = ‖ξ‖ = 1`) and `d ≥ 0`, the right hand side is
positive, and multiplying by `exp d` (using `exp d * sinh d = (exp (2d) - 1)/2`) gives

`exp d * (tpart y - inner ℝ y ξ) = 1 + (1 - c) * ((exp (2d) - 1)/2)`.

Taking logarithms and using `exp d * (tpart y - inner ℝ y ξ) = exp (d + busemann ξ y)`
yields the formula.  The inequality is `Work.Mostow.neg_hdist_zero_le_busemann`.
-/

namespace Work.Mostow

open Submission.Mostow

variable {n : ℕ}

lemma exp_mul_sinh_eq (d : ℝ) :
    Real.exp d * Real.sinh d = (Real.exp (2 * d) - 1) / 2 := by
  have h1 : Real.exp d * Real.exp (-d) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  have h2 : Real.exp (2 * d) = Real.exp d * Real.exp d := by
    rw [show (2 : ℝ) * d = d + d by ring, Real.exp_add]
  have key : Real.exp d * ((Real.exp d - Real.exp (-d)) / 2)
      = (Real.exp d * Real.exp d - Real.exp d * Real.exp (-d)) / 2 := by ring
  rw [Real.sinh_eq, key, h1, h2]

lemma cosh_sub_sinh_mul_eq (d c : ℝ) :
    Real.cosh d - Real.sinh d * c = Real.exp (-d) + (1 - c) * Real.sinh d := by
  have h := Real.cosh_sub_sinh d
  rw [show Real.cosh d - Real.sinh d * c
      = (Real.cosh d - Real.sinh d) + (1 - c) * Real.sinh d by ring, h]

lemma one_add_exp_formula (d c : ℝ) :
    1 + (1 - c) * ((Real.exp (2 * d) - 1) / 2)
      = Real.exp d * (Real.cosh d - Real.sinh d * c) := by
  have h1 : Real.exp d * Real.exp (-d) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  rw [← exp_mul_sinh_eq d, cosh_sub_sinh_mul_eq d c,
    show Real.exp d * (Real.exp (-d) + (1 - c) * Real.sinh d)
      = Real.exp d * Real.exp (-d) + (1 - c) * (Real.exp d * Real.sinh d) by ring, h1]

theorem BusemannFormula (n : ℕ) (y ξ : Submission.Mostow.E n) (hy : y ≠ 0)
    (hξ : ξ ∈ Submission.Mostow.Sph n) :
    Submission.Mostow.busemann ξ y =
      -(Submission.Mostow.hdist 0 y) + Real.log (1 + (1 - inner ℝ ((‖y‖)⁻¹ • y) ξ) *
        ((Real.exp (2 * Submission.Mostow.hdist 0 y) - 1) / 2)) ∧
    -(Submission.Mostow.hdist 0 y) ≤ Submission.Mostow.busemann ξ y := by
  have hyn : ‖y‖ ≠ 0 := norm_ne_zero_iff.mpr hy
  set d : ℝ := hdist 0 y with hd_def
  set c : ℝ := inner ℝ ((‖y‖)⁻¹ • y) ξ with hc_def
  have hinner : inner ℝ y ξ = ‖y‖ * c := by
    rw [hc_def, real_inner_smul_left, ← mul_assoc, mul_inv_cancel₀ hyn, one_mul]
  have htp : tpart y = Real.cosh d := by
    rw [hd_def]; exact (cosh_hdist_zero y).symm
  have hnorm : ‖y‖ = Real.sinh d := by
    rw [hd_def]; exact (sinh_hdist_zero y).symm
  have hcle : c ≤ 1 := by
    have hu : ‖(‖y‖)⁻¹ • y‖ = 1 := by
      rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg y),
        inv_mul_cancel₀ hyn]
    have hξn : ‖ξ‖ = 1 := (mem_Sph_iff ξ).mp hξ
    have h := real_inner_le_norm ((‖y‖)⁻¹ • y) ξ
    rw [hu, hξn, mul_one] at h
    rw [hc_def]; exact h
  have harg : tpart y - inner ℝ y ξ = Real.cosh d - Real.sinh d * c := by
    rw [htp, hinner, hnorm]
  have hargpos : 0 < tpart y - inner ℝ y ξ := busemann_arg_pos ξ hξ y
  constructor
  · have hlog : Real.log (1 + (1 - c) * ((Real.exp (2 * d) - 1) / 2))
        = d + busemann ξ y := by
      have h1 : 1 + (1 - c) * ((Real.exp (2 * d) - 1) / 2)
          = Real.exp d * (tpart y - inner ℝ y ξ) := by
        rw [one_add_exp_formula d c, harg]
      rw [h1, Real.log_mul (Real.exp_ne_zero d) (ne_of_gt hargpos), Real.log_exp,
        busemann_eq_log]
    have hmain : busemann ξ y
        = -d + Real.log (1 + (1 - c) * ((Real.exp (2 * d) - 1) / 2)) := by
      rw [hlog]; ring
    rw [hd_def, hc_def] at hmain
    exact hmain
  · rw [hd_def]; exact neg_hdist_zero_le_busemann ξ hξ y

end Work.Mostow
