import Mathlib
import Submission.Commons.Analysis.SpecialFunctions.Gamma.gamma_vertical_exp_decay_lower
import Submission.Commons.Analysis.SpecialFunctions.Gamma.norm_gammaR_le_norm_gammaR_re

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open Complex
open scoped Real

set_option autoImplicit false

namespace Commons.Analysis.SpecialFunctions.Gamma

/-- Modulus of Deligne's real Gamma factor at `a + i·t`, expanded in terms of `Γ` at
half the argument:
`‖Gammaℝ (a + i t)‖ = π^(-a/2) · ‖Γ (a/2 + i·t/2)‖`. -/
lemma norm_gammaR_vertical_eq (a t : ℝ) :
    ‖Complex.Gammaℝ ((a : ℂ) + I * (t : ℂ))‖ =
      (Real.pi : ℝ) ^ (-(a / 2)) *
        ‖Complex.Gamma (((a / 2 : ℝ) : ℂ) + I * ((t / 2 : ℝ) : ℂ))‖ := by
  have hsre : (((a : ℂ) + I * (t : ℂ))).re = a := by simp
  have hpi : ‖(Real.pi : ℂ) ^ (-((a : ℂ) + I * (t : ℂ)) / 2)‖ =
      (Real.pi : ℝ) ^ (-(a / 2)) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
    congr 1
    rw [re_of_half]
    simp
    ring
  have hs2 : (((a : ℂ) + I * (t : ℂ)) / 2) =
      (((a / 2 : ℝ) : ℂ) + I * ((t / 2 : ℝ) : ℂ)) := by
    apply Complex.ext <;> simp
  rw [Complex.Gammaℝ_def, norm_mul, hpi]
  exact congrArg (fun w : ℝ => (Real.pi : ℝ) ^ (-(a / 2)) * w) (by rw [hs2])

/-- Since the exponent `a/2 - 1` is negative (for `a < 2`), the power is antitone in the
base, giving `(1 + |t|)^(a/2-1) ≤ (1 + |t|/2)^(a/2-1)`. -/
lemma pow_half_ge (a t : ℝ) (ha2 : a < 2) :
    (1 + |t|) ^ (a / 2 - 1) ≤ (1 + |t| / 2) ^ (a / 2 - 1) := by
  have hP0 : 0 ≤ 1 + |t| := by positivity
  have hQ0 : 0 ≤ 1 + |t| / 2 := by positivity
  have hPpos : 0 < 1 + |t| := by positivity
  have hQpos : 0 < 1 + |t| / 2 := by positivity
  have hPQ : 1 + |t| / 2 ≤ 1 + |t| := by
    have ht0 : 0 ≤ |t| := abs_nonneg t
    nlinarith
  have hr : 0 < 1 - a / 2 := by nlinarith
  rw [show a / 2 - 1 = -(1 - a / 2) by ring]
  rw [Real.rpow_neg hP0, Real.rpow_neg hQ0]
  rw [inv_le_inv₀ (Real.rpow_pos_of_pos hPpos (1 - a / 2))
    (Real.rpow_pos_of_pos hQpos (1 - a / 2))]
  exact Real.rpow_le_rpow hQ0 hPQ (le_of_lt hr)

/-- Lower bound for Deligne's real Gamma factor with polynomial decay, for `0 < a < 2`:
there is `c > 0` with
`c · (1+|t|)^(a/2-1) · e^{-π|t|/4} ≤ ‖Gammaℝ (a + i·t)‖` for all real `t`. -/
theorem gammaR_vertical_poly_lower (a : ℝ) (ha0 : 0 < a) (ha2 : a < 2) :
    ∃ c : ℝ, 0 < c ∧ ∀ t : ℝ,
      c * (1 + |t|) ^ (a / 2 - 1) * Real.exp (-(Real.pi / 4) * |t|) ≤
        ‖Complex.Gammaℝ ((a : ℂ) + I * (t : ℂ))‖ := by
  have hσ0 : 0 < a / 2 := by positivity
  have hσ1 : a / 2 < 1 := by nlinarith
  obtain ⟨c0, hc0pos, hc0⟩ := gamma_vertical_exp_decay_lower (a / 2) hσ0 hσ1
  let c : ℝ := (Real.pi : ℝ) ^ (-(a / 2)) * c0
  refine ⟨c, ?_, ?_⟩
  · dsimp [c]
    exact mul_pos (Real.rpow_pos_of_pos Real.pi_pos (-(a / 2))) hc0pos
  · intro t
    let P : ℝ := 1 + |t|
    let Q : ℝ := 1 + |t| / 2
    let F : ℝ := Real.exp (-(Real.pi / 4) * |t|)
    have hFpos : 0 < F := by dsimp [F]; positivity
    have hc0nonneg : 0 ≤ c0 := le_of_lt hc0pos
    have hpi_nonneg : 0 ≤ (Real.pi : ℝ) ^ (-(a / 2)) :=
      le_of_lt (Real.rpow_pos_of_pos Real.pi_pos (-(a / 2)))
    -- |t/2| = |t|/2 :
    have habs : |t / 2| = |t| / 2 := by
      rw [abs_div]
      norm_num
    -- exponential factor agrees :
    have hexp : Real.exp (-(Real.pi / 2) * (|t| / 2)) = F := by
      dsimp [F]
      congr 1
      ring
    -- power comparison : P^(a/2-1) ≤ Q^(a/2-1)
    have hpow : P ^ (a / 2 - 1) ≤ Q ^ (a / 2 - 1) := by
      dsimp [P, Q]
      exact pow_half_ge a t ha2
    -- lower bound on Γ(a/2 + i t/2), from the σ∈(0,1) exponential-decay lower bound :
    have hΓ : c0 * Q ^ (a / 2 - 1) * F ≤
        ‖Complex.Gamma (((a / 2 : ℝ) : ℂ) + I * ((t / 2 : ℝ) : ℂ))‖ := by
      have hu := hc0 (t / 2)
      rw [habs] at hu
      rw [hexp] at hu
      simpa [Q] using hu
    -- norm identity for Gammaℝ :
    have hnorm := norm_gammaR_vertical_eq a t
    -- chain of inequalities :
    have hmain : c * P ^ (a / 2 - 1) * F ≤
        ‖Complex.Gammaℝ ((a : ℂ) + I * (t : ℂ))‖ := by
      calc
        c * P ^ (a / 2 - 1) * F
            = ((Real.pi : ℝ) ^ (-(a / 2)) * c0) * P ^ (a / 2 - 1) * F := by
              dsimp [c]
            _ ≤ ((Real.pi : ℝ) ^ (-(a / 2)) * c0) * Q ^ (a / 2 - 1) * F := by
              exact mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left hpow (mul_nonneg hpi_nonneg hc0nonneg))
                (le_of_lt hFpos)
            _ = (Real.pi : ℝ) ^ (-(a / 2)) * (c0 * Q ^ (a / 2 - 1) * F) := by ring
            _ ≤ (Real.pi : ℝ) ^ (-(a / 2)) *
                ‖Complex.Gamma (((a / 2 : ℝ) : ℂ) + I * ((t / 2 : ℝ) : ℂ))‖ := by
              exact mul_le_mul_of_nonneg_left hΓ hpi_nonneg
            _ = ‖Complex.Gammaℝ ((a : ℂ) + I * (t : ℂ))‖ := hnorm.symm
    simpa [c, P, F] using hmain

end Commons.Analysis.SpecialFunctions.Gamma
