import Mathlib
import Submission.Commons.Analysis.SpecialFunctions.Gamma.gamma_one_add_mul_I_prod_norm
import Submission.Commons.Analysis.SpecialFunctions.Gamma.gamma_vertical_exp_decay

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open Complex
open scoped Real

set_option autoImplicit false

namespace Commons.Analysis.SpecialFunctions.Gamma

/-- `sinh x ≤ x · exp x` for all nonnegative real `x`. -/
private lemma sinh_le_mul_exp (x : ℝ) (_hx : 0 ≤ x) : Real.sinh x ≤ x * Real.exp x := by
  rw [Real.sinh_eq]
  have hineq : 1 - Real.exp (-(2 * x)) ≤ 2 * x := by
    have h := Real.add_one_le_exp (-(2 * x))
    nlinarith
  have hm : Real.exp (2 * x) - 1 ≤ 2 * x * Real.exp (2 * x) := by
    have he2 : 0 < Real.exp (2 * x) := Real.exp_pos (2 * x)
    have hstep := mul_le_mul_of_nonneg_right hineq he2.le
    have hL : (1 - Real.exp (-(2 * x))) * Real.exp (2 * x) =
        Real.exp (2 * x) - 1 := by
      calc
        (1 - Real.exp (-(2 * x))) * Real.exp (2 * x)
            = Real.exp (2 * x) - Real.exp (-(2 * x)) * Real.exp (2 * x) := by ring
        _ = Real.exp (2 * x) - 1 := by
          rw [← Real.exp_add]
          have hz : -(2 * x) + 2 * x = 0 := by ring
          rw [hz, Real.exp_zero]
    calc
      Real.exp (2 * x) - 1 = (1 - Real.exp (-(2 * x))) * Real.exp (2 * x) := hL.symm
      _ ≤ 2 * x * Real.exp (2 * x) := hstep
  have hA : Real.exp x - Real.exp (-x) ≤ 2 * x * Real.exp x := by
    have h1 : Real.exp (-x) * (Real.exp (2 * x) - 1) = Real.exp x - Real.exp (-x) := by
      calc
        Real.exp (-x) * (Real.exp (2 * x) - 1)
            = Real.exp (-x) * Real.exp (2 * x) - Real.exp (-x) * 1 := by ring
        _ = Real.exp x - Real.exp (-x) := by
          rw [← Real.exp_add]
          have hz : -x + 2 * x = x := by ring
          rw [hz, mul_one]
    have h2 : Real.exp (-x) * (2 * x * Real.exp (2 * x)) = 2 * x * Real.exp x := by
      calc
        Real.exp (-x) * (2 * x * Real.exp (2 * x))
            = 2 * x * (Real.exp (-x) * Real.exp (2 * x)) := by ring
        _ = 2 * x * Real.exp x := by
          rw [← Real.exp_add]
          have hz : -x + 2 * x = x := by ring
          rw [hz]
    calc
      Real.exp x - Real.exp (-x) = Real.exp (-x) * (Real.exp (2 * x) - 1) := h1.symm
      _ ≤ Real.exp (-x) * (2 * x * Real.exp (2 * x)) := by
        exact mul_le_mul_of_nonneg_left hm (Real.exp_pos (-x)).le
      _ = 2 * x * Real.exp x := h2
  calc
    (Real.exp x - Real.exp (-x)) / 2 ≤ (2 * x * Real.exp x) / 2 := by
      exact div_le_div_of_nonneg_right hA (by positivity)
    _ = x * Real.exp x := by ring

/-- Conjugate symmetry of the modulus of `Γ` on the vertical line `Re = 1`:
`‖Γ(1 - iτ)‖ = ‖Γ(1 + iτ)‖` for real `τ`. -/
private lemma norm_Gamma_one_sub_mul_I (τ : ℝ) :
    ‖Complex.Gamma ((1 : ℂ) - I * (τ : ℂ))‖ = ‖Complex.Gamma ((1 : ℂ) + I * (τ : ℂ))‖ := by
  have hconj : (starRingEnd ℂ) ((1 : ℂ) + I * (τ : ℂ)) = (1 : ℂ) - I * (τ : ℂ) := by
    apply Complex.ext <;> simp
  calc
    ‖Complex.Gamma ((1 : ℂ) - I * (τ : ℂ))‖
        = ‖Complex.Gamma ((starRingEnd ℂ) ((1 : ℂ) + I * (τ : ℂ)))‖ := by rw [hconj]
    _ = ‖Complex.Gamma ((1 : ℂ) + I * (τ : ℂ))‖ := by
        rw [Complex.Gamma_conj]
        exact Complex.norm_conj _

/-- Strong form of the requested bound, valid with constant `c = 1`:
`exp (-(π/2)·|τ|) ≤ ‖Γ(1 + iτ)‖` for all real `τ`.

Proof: for `τ ≠ 0` the Euler reflection formula gives
`‖Γ(1 + iτ)‖² = π·|τ| / sinh (π·|τ|)` (conjugating `1 + iτ` maps it to `1 - iτ`,
so both moduli on the left of the product formula are equal), and this is at least
`exp (-π·|τ|)` because `sinh x ≤ x·exp x`.  The point `τ = 0` is handled directly. -/
private lemma gamma_one_vertical_lower_full (τ : ℝ) :
    Real.exp (-(Real.pi / 2) * |τ|) ≤ ‖Complex.Gamma ((1 : ℂ) + I * (τ : ℂ))‖ := by
  by_cases hτ : τ = 0
  · subst τ
    simp [Complex.Gamma_one]
  · let A : ℝ := ‖Complex.Gamma ((1 : ℂ) + I * (τ : ℂ))‖
    let B : ℝ := ‖Complex.Gamma ((1 : ℂ) - I * (τ : ℂ))‖
    have hB : B = A := by
      dsimp [A, B]
      exact norm_Gamma_one_sub_mul_I τ
    have hprod : A * B = Real.pi * |τ| / Real.sinh (Real.pi * |τ|) := by
      dsimp [A, B]
      exact gamma_one_add_mul_I_prod_norm τ hτ
    have hsq : A ^ 2 = Real.pi * |τ| / Real.sinh (Real.pi * |τ|) := by
      calc
        A ^ 2 = A * A := by rw [pow_two]
        _ = A * B := by rw [hB]
        _ = Real.pi * |τ| / Real.sinh (Real.pi * |τ|) := hprod
    have hxpos : 0 < Real.pi * |τ| := mul_pos Real.pi_pos (abs_pos.mpr hτ)
    have hAe : Real.exp (-(Real.pi * |τ|)) ≤
        Real.pi * |τ| / Real.sinh (Real.pi * |τ|) := by
      have hx : 0 ≤ Real.pi * |τ| := le_of_lt hxpos
      have hsl := sinh_le_mul_exp (Real.pi * |τ|) hx
      have hsinpos : 0 < Real.sinh (Real.pi * |τ|) := (Real.sinh_pos_iff).2 hxpos
      have hrec : ((Real.pi * |τ|) * Real.exp (Real.pi * |τ|))⁻¹ ≤
          (Real.sinh (Real.pi * |τ|))⁻¹ := by
        simpa using (one_div_le_one_div_of_le hsinpos hsl)
      calc
        Real.exp (-(Real.pi * |τ|))
            = Real.pi * |τ| * (((Real.pi * |τ|) * Real.exp (Real.pi * |τ|))⁻¹) := by
              rw [Real.exp_neg]
              field_simp [ne_of_gt hxpos, ne_of_gt (Real.exp_pos (Real.pi * |τ|))]
        _ ≤ Real.pi * |τ| * (Real.sinh (Real.pi * |τ|))⁻¹ := by
              exact mul_le_mul_of_nonneg_left hrec (le_of_lt hxpos)
        _ = Real.pi * |τ| / Real.sinh (Real.pi * |τ|) := by ring
    have hsqle : (Real.exp (-(Real.pi / 2) * |τ|)) ^ 2 ≤ A ^ 2 := by
      rw [hsq]
      have htwo : (Real.exp (-(Real.pi / 2) * |τ|)) ^ 2 = Real.exp (-(Real.pi * |τ|)) := by
        rw [pow_two, ← Real.exp_add]
        congr 1
        ring
      rw [htwo]
      exact hAe
    have habs := sq_le_sq.mp hsqle
    have h1 : |Real.exp (-(Real.pi / 2) * |τ|)| = Real.exp (-(Real.pi / 2) * |τ|) :=
      abs_of_pos (Real.exp_pos _)
    have h2 : |A| = A := abs_of_nonneg (norm_nonneg _)
    have hfin : Real.exp (-(Real.pi / 2) * |τ|) ≤ A := by
      simpa [h1, h2] using habs
    simpa [A] using hfin

theorem gamma_one_lower :
    ∃ c : ℝ, 0 < c ∧ ∀ τ : ℝ,
      c * Real.exp (-(Real.pi / 2) * |τ|) ≤ ‖Complex.Gamma ((1 : ℂ) + Complex.I * (τ : ℂ))‖ := by
  refine ⟨1, zero_lt_one, ?_⟩
  intro τ
  calc
    (1 : ℝ) * Real.exp (-(Real.pi / 2) * |τ|) = Real.exp (-(Real.pi / 2) * |τ|) := by ring
    _ ≤ ‖Complex.Gamma ((1 : ℂ) + I * (τ : ℂ))‖ := gamma_one_vertical_lower_full τ

end Commons.Analysis.SpecialFunctions.Gamma
