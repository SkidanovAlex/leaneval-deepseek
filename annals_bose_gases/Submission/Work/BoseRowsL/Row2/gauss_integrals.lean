import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseRowsL.Row2.gauss_integrals`

The two Gaussian-type integrals needed in the row-2 bookkeeping of the lattice Coulomb chapter
(`theorem gauss_integrals`):

* `∫_{t>0} (4πt)^{-3/2} e^{-a/t} dt = 1/(8π√a)`  (`a > 0`),
* `∫_{p ∈ ℝ³} e^{-t‖p‖²} dp = (π/t)^{3/2}`  (`t > 0`).

The second is Mathlib's `GaussianFourier.integral_rexp_neg_mul_sq_norm` at
`V = EuclideanSpace ℝ (Fin 3)` (with `Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3`).

The first is the Green's-function / subordination identity.  The substitution `t ↦ 1/t` on
`(0,∞)` (`MeasureTheory.integral_comp_rpow_Ioi` with `p = -1`, whose change of variables is
`x ↦ x⁻¹` with derivative `-x⁻²`) converts it into the Gamma integral
`∫_{s>0} s^{-1/2} e^{-a s} ds = √π/√a` (`Real.integral_rpow_mul_exp_neg_mul_Ioi` together with
`Real.Gamma_one_half_eq`); the remaining constant is elementary.
-/

open MeasureTheory Set

namespace Work.BoseRowsL.Row2

/-- **The substitution `t ↦ 1/t` in the form needed here.**
`∫_{t>0} t^{-3/2} e^{-a/t} dt = ∫_{s>0} s^{-1/2} e^{-a s} ds`.

It is `MeasureTheory.integral_comp_rpow_Ioi` at `p = -1` applied to `s ↦ s^{-1/2} e^{-a s}`
(whose `x ↦ x⁻¹`-transform is `x^{1/2} e^{-a/x}`, to be multiplied by the Jacobian `x^{-2}`). -/
lemma integral_inv_rpow_three_half (a : ℝ) :
    ∫ t in Set.Ioi (0 : ℝ), t ^ (-(3 : ℝ) / 2) * Real.exp (-(a / t))
      = ∫ s in Set.Ioi (0 : ℝ), s ^ (-(1 : ℝ) / 2) * Real.exp (-(a * s)) := by
  have h := MeasureTheory.integral_comp_rpow_Ioi
    (g := fun s : ℝ => s ^ (-(1 : ℝ) / 2) * Real.exp (-(a * s))) (p := -1) (by norm_num)
  rw [← h]
  refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
  have hx0 : 0 < x := hx
  have hxnn : 0 ≤ x := hx.le
  simp only [abs_neg, abs_one, one_mul, smul_eq_mul]
  rw [show a / x = a * x⁻¹ by rw [div_eq_mul_inv]]
  simp only [Real.rpow_neg_one]
  have h1 : x ^ (-1 - 1 : ℝ) = x ^ (-2 : ℝ) := by norm_num
  have h2 : x⁻¹ ^ (-(1 : ℝ) / 2) = x ^ ((1 : ℝ) / 2) := by
    rw [Real.inv_rpow hxnn]
    rw [show (-(1 : ℝ) / 2) = -(1 / 2) by norm_num]
    rw [Real.rpow_neg hxnn, inv_inv]
  have h3 : x ^ (-2 : ℝ) * x ^ ((1 : ℝ) / 2) = x ^ (-(3 : ℝ) / 2) := by
    rw [← Real.rpow_add hx0]
    congr 1
    norm_num
  rw [h1, h2, ← h3]
  ring

/-- **The Gamma integral** `∫_{s>0} s^{-1/2} e^{-a s} ds = √π/√a` for `a > 0`.
This is `Real.integral_rpow_mul_exp_neg_mul_Ioi` at `a = 1/2` together with
`Real.Gamma_one_half_eq` and `(1/a)^{1/2} = 1/√a`. -/
lemma integral_rpow_neg_half_exp (a : ℝ) (ha : 0 < a) :
    ∫ s in Set.Ioi (0 : ℝ), s ^ (-(1 : ℝ) / 2) * Real.exp (-(a * s))
      = Real.sqrt Real.pi / Real.sqrt a := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := (1 : ℝ) / 2) (r := a) (by norm_num) ha
  rw [Real.Gamma_one_half_eq] at h
  rw [show (1 : ℝ) / 2 - 1 = -(1 : ℝ) / 2 by norm_num] at h
  have h2 : (1 / a) ^ ((1 : ℝ) / 2) * Real.sqrt Real.pi = Real.sqrt Real.pi / Real.sqrt a := by
    rw [one_div, ← Real.sqrt_eq_rpow, Real.sqrt_inv, div_eq_mul_inv, mul_comm]
  rwa [h2] at h

/-- The numerical constant: `(4π)^{-3/2} · √π/√a = 1/(8π√a)` for `a > 0`. -/
lemma four_pi_rpow_neg_three_half_mul_sqrt (a : ℝ) (ha : 0 < a) :
    (4 * Real.pi) ^ (-(3 : ℝ) / 2) * (Real.sqrt Real.pi / Real.sqrt a)
      = 1 / (8 * Real.pi * Real.sqrt a) := by
  have hA : (4 * Real.pi) ^ (-(3 : ℝ) / 2) = ((4 * Real.pi) ^ ((3 : ℝ) / 2))⁻¹ := by
    rw [show (-(3 : ℝ) / 2 : ℝ) = -(3 / 2) by norm_num]
    exact Real.rpow_neg (show (0 : ℝ) ≤ 4 * Real.pi by positivity) (3 / 2)
  have hB : (4 * Real.pi) ^ ((3 : ℝ) / 2) = 8 * Real.pi * Real.sqrt Real.pi := by
    rw [show ((3 : ℝ) / 2) = (1 / 2 + 1) by norm_num]
    rw [Real.rpow_add (show (0 : ℝ) < 4 * Real.pi by positivity), Real.rpow_one,
      ← Real.sqrt_eq_rpow, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4),
      show Real.sqrt (4 : ℝ) = 2 by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    ring
  rw [hA, hB]
  field_simp

theorem gauss_integrals :
    (∀ a : ℝ, 0 < a → ∫ t in Set.Ioi (0 : ℝ), (4 * Real.pi * t) ^ (-(3 : ℝ) / 2) * Real.exp (-(a / t))
        = 1 / (8 * Real.pi * Real.sqrt a))
      ∧ (∀ t : ℝ, 0 < t → ∫ p : EuclideanSpace ℝ (Fin 3), Real.exp (-(t * ‖p‖ ^ 2))
          = (Real.pi / t) ^ (3 / 2 : ℝ)) := by
  constructor
  · intro a ha
    -- factor the constant `(4π)^{-3/2}` out of the integrand, using `(4πt)^r = (4π)^r t^r`
    have hstep : ∫ t in Set.Ioi (0 : ℝ), (4 * Real.pi * t) ^ (-(3 : ℝ) / 2) * Real.exp (-(a / t))
        = (4 * Real.pi) ^ (-(3 : ℝ) / 2) *
            ∫ t in Set.Ioi (0 : ℝ), t ^ (-(3 : ℝ) / 2) * Real.exp (-(a / t)) := by
      rw [← integral_const_mul]
      refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
      rw [Real.mul_rpow (show (0 : ℝ) ≤ 4 * Real.pi by positivity) ht.le]
      ring
    rw [hstep, integral_inv_rpow_three_half a, integral_rpow_neg_half_exp a ha,
      four_pi_rpow_neg_three_half_mul_sqrt a ha]
  · intro t ht
    have h := GaussianFourier.integral_rexp_neg_mul_sq_norm (V := EuclideanSpace ℝ (Fin 3)) ht
    simpa [finrank_euclideanSpace_fin, neg_mul] using h

end Work.BoseRowsL.Row2
