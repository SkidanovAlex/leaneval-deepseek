import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixR.LatGreen

open MeasureTheory

/-!
# The tail bound `heatK3_tail_bound`

Undoing the substitution `u = a / t`, the tail `∫_{t > η} (4πt)^{-3/2} e^{-a/t} dt` of the heat
kernel `heatK3` is, up to the constant `(4π)^{-3/2} a^{-1/2}`, the elementary integral
`∫_{u > a/η} u^{-1/2} e^{-u} du`.

On `(a/η, ∞)` the weight `u^{-1/2}` is dominated by the constant `(a/η)^{-1/2}`, so that integral is
at most `(a/η)^{-1/2} e^{-a/η} = (a/η)^{-1/2} ∫_{u>a/η} e^{-u} du`; multiplying by the constant
`(4π)^{-3/2} a^{-1/2} = a^{-1/2} / (8 π^{3/2})` gives the stated bound
`√η e^{-a/η} / (8 π^{3/2} a)`.
-/

/-- `(4π)^{-3/2} = 1 / (8 π^{3/2})`. -/
theorem four_pi_rpow_neg_three_halves :
    (4 * Real.pi) ^ (-(3 / 2 : ℝ)) = 1 / (8 * Real.pi ^ (3 / 2 : ℝ)) := by
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) Real.pi_pos.le]
  have h4 : (4 : ℝ) ^ (-(3 / 2 : ℝ)) = 1 / 8 := by
    rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 4),
      show (3 / 2 : ℝ) = (1 / 2) * 3 by norm_num,
      Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 4)]
    norm_num [Real.sqrt_eq_rpow]
  rw [h4, Real.rpow_neg Real.pi_pos.le, one_div, one_div, mul_inv]

/-- `a^{-1/2} (a/η)^{-1/2} = √η / a` for `a, η > 0`. -/
theorem rpow_neg_half_mul_div_rpow_neg_half {a η : ℝ} (ha : 0 < a) (hη : 0 < η) :
    a ^ (-(1 / 2 : ℝ)) * (a / η) ^ (-(1 / 2 : ℝ)) = Real.sqrt η / a := by
  rw [Real.div_rpow ha.le hη.le, Real.rpow_neg hη.le, div_inv_eq_mul]
  rw [← mul_assoc, ← Real.rpow_add ha,
    show (-(1 / 2 : ℝ)) + (-(1 / 2)) = -1 by norm_num, Real.rpow_neg_one,
    ← Real.sqrt_eq_rpow, div_eq_mul_inv]
  ring

/-- `∫_{u > A} u^{-1/2} e^{-u} du ≤ A^{-1/2} e^{-A}` for `A > 0`: on `(A, ∞)` the weight
`u^{-1/2}` is at most the constant `A^{-1/2}`. -/
theorem integral_rpow_neg_half_mul_exp_neg_tail_le {A : ℝ} (hA : 0 < A) :
    ∫ u in Set.Ioi A, u ^ (-(1 / 2 : ℝ)) * Real.exp (-u)
      ≤ A ^ (-(1 / 2 : ℝ)) * Real.exp (-A) := by
  have hf_int : IntegrableOn (fun u : ℝ => u ^ (-(1 / 2 : ℝ)) * Real.exp (-u))
      (Set.Ioi A) := by
    have h1 : IntegrableOn (fun x : ℝ => x ^ (-(1 / 2 : ℝ)) * Real.exp (-x)) (Set.Ioi 0) := by
      have h := integrableOn_rpow_mul_exp_neg_rpow (p := 1) (s := -(1 / 2)) (by norm_num)
        (by norm_num)
      simpa [Real.rpow_one] using h
    exact h1.mono_set (fun x hx => Set.mem_Ioi.mpr (hA.trans (Set.mem_Ioi.mp hx)))
  have hmaj_int : IntegrableOn (fun u : ℝ => A ^ (-(1 / 2 : ℝ)) * Real.exp (-u))
      (Set.Ioi A) :=
    (integrableOn_exp_neg_Ioi A).const_mul _
  have hmono : ∫ u in Set.Ioi A, (u ^ (-(1 / 2 : ℝ)) * Real.exp (-u))
      ≤ ∫ u in Set.Ioi A, (A ^ (-(1 / 2 : ℝ)) * Real.exp (-u)) := by
    refine setIntegral_mono_on hf_int hmaj_int measurableSet_Ioi ?_
    intro u hu
    have hAu : A ≤ u := le_of_lt (Set.mem_Ioi.mp hu)
    have hpow : u ^ (-(1 / 2 : ℝ)) ≤ A ^ (-(1 / 2 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos hA hAu (by norm_num)
    exact mul_le_mul_of_nonneg_right hpow (Real.exp_pos _).le
  calc ∫ u in Set.Ioi A, (u ^ (-(1 / 2 : ℝ)) * Real.exp (-u))
      ≤ ∫ u in Set.Ioi A, (A ^ (-(1 / 2 : ℝ)) * Real.exp (-u)) := hmono
    _ = A ^ (-(1 / 2 : ℝ)) * ∫ u in Set.Ioi A, Real.exp (-u) := by
          rw [MeasureTheory.integral_const_mul]
    _ = A ^ (-(1 / 2 : ℝ)) * Real.exp (-A) := by rw [integral_exp_neg_Ioi]

theorem heatK3_tail_bound {a η : ℝ} (ha : 0 < a) (hη : 0 < η) :
    ∫ u in Set.Ioi (a / η),
        (4 * Real.pi) ^ (-(3 / 2 : ℝ)) * a ^ (-(1 / 2 : ℝ))
          * (u ^ (-(1 / 2 : ℝ)) * Real.exp (-u))
      ≤ Real.sqrt η * Real.exp (-(a / η)) / (8 * Real.pi ^ (3 / 2 : ℝ) * a) := by
  have hA : 0 < a / η := div_pos ha hη
  have hc : 0 < (4 * Real.pi) ^ (-(3 / 2 : ℝ)) * a ^ (-(1 / 2 : ℝ)) := by positivity
  calc ∫ u in Set.Ioi (a / η),
          (4 * Real.pi) ^ (-(3 / 2 : ℝ)) * a ^ (-(1 / 2 : ℝ))
            * (u ^ (-(1 / 2 : ℝ)) * Real.exp (-u))
      = ((4 * Real.pi) ^ (-(3 / 2 : ℝ)) * a ^ (-(1 / 2 : ℝ)))
          * ∫ u in Set.Ioi (a / η), (u ^ (-(1 / 2 : ℝ)) * Real.exp (-u)) := by
          rw [MeasureTheory.integral_const_mul]
    _ ≤ ((4 * Real.pi) ^ (-(3 / 2 : ℝ)) * a ^ (-(1 / 2 : ℝ)))
          * ((a / η) ^ (-(1 / 2 : ℝ)) * Real.exp (-(a / η))) :=
          mul_le_mul_of_nonneg_left (integral_rpow_neg_half_mul_exp_neg_tail_le hA) hc.le
    _ = Real.sqrt η * Real.exp (-(a / η)) / (8 * Real.pi ^ (3 / 2 : ℝ) * a) := by
          rw [four_pi_rpow_neg_three_halves]
          rw [show (1 / (8 * Real.pi ^ (3 / 2 : ℝ)) * a ^ (-(1 / 2 : ℝ)))
                * ((a / η) ^ (-(1 / 2 : ℝ)) * Real.exp (-(a / η)))
              = 1 / (8 * Real.pi ^ (3 / 2 : ℝ))
                * (a ^ (-(1 / 2 : ℝ)) * (a / η) ^ (-(1 / 2 : ℝ)))
                * Real.exp (-(a / η)) by ring]
          rw [rpow_neg_half_mul_div_rpow_neg_half ha hη]
          rw [div_eq_mul_inv, div_eq_mul_inv, mul_inv]
          ring

end Work.BoseFixR.LatGreen
