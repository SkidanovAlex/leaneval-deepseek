import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Submission.Work.BoseB4.Coherent
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB4.Gauss_integrable`

The Gaussian (coherent-state) measure on `ℂ`,

    `gauss = volume.withDensity (fun z => exp (-‖z‖²) / π)`   (see `Coherent.lean`),

is a probability measure with super-exponentially decaying density, so every polynomial in
`z` and `z̄` is integrable against it:

    `Integrable (fun z : ℂ => z ^ A * (starRingEnd ℂ z) ^ B) gauss`.

This is the *integrability* half of the Gaussian moment computation (`Gauss_moment`); it is
needed to justify the anti-Wick substitution
`⟨Ψ, (a₀†)^q (a₀)^p Ψ'⟩ = ∫ z^p z̄^q ⟨ΦΨz, ΦΨ'z⟩ dν(z)` of FS §8.3 (`eq:subst-z`).

## Proof

Unfolding the `withDensity` via `integrable_withDensity_iff_integrable_smul`, the claim is the
integrability of `z ↦ (exp (-‖z‖²)/π) • (z^A z̄^B)` against Lebesgue measure on `ℂ`.  Since
`‖(exp (-‖z‖²)/π) • (z^A z̄^B)‖ = exp (-‖z‖²)/π * ‖z‖^{A+B}`, it suffices to dominate

    `exp (-t)/π * t^{k/2}`,   `t = ‖z‖²`,  `k = A + B`,

by `C * exp (-t/2)`.  Two elementary facts are used:

* `t^k exp (-t) ≤ ((2k)/e)^k exp (-t/2)` for `t ≥ 0` (`Real.mul_exp_neg_le_exp_neg_one` applied
  to `t/(2k)` and raised to the `k`-th power);
* `t^{k/2} ≤ 1 + t^k` because `exp (-‖z‖²) ≤ exp (-‖z‖²/2)`.

The dominating function `exp (-‖z‖²/2)` is integrable against Lebesgue measure on `ℂ`, which is
the `b = 1/2`, `c = 0`, `w = 0` case of `GaussianFourier.integrable_cexp_neg_mul_sq_norm_add`.
-/

noncomputable section

open MeasureTheory
open scoped NNReal ENNReal

namespace Work.BoseB4

set_option autoImplicit false

/-- The Gaussian density `e^{-|z|²}/π` as a real number. -/
lemma gaussWeight_coe (z : ℂ) : (gaussWeight z : ℝ) = Real.exp (-(‖z‖ ^ 2)) / Real.pi := rfl

namespace GaussAux

/-- Elementary comparison of a power with `1 +` a higher even power, for nonnegative `t`:
`t^k ≤ 1 + t ^ (2k)`. -/
lemma pow_le_one_add_pow_two_mul (k : ℕ) (t : ℝ) (ht : 0 ≤ t) : t ^ k ≤ 1 + t ^ (2 * k) := by
  by_cases h : t ≤ 1
  · exact le_trans (pow_le_one₀ ht h) (le_add_of_nonneg_right (pow_nonneg ht _))
  · push Not at h
    have hkk : k ≤ 2 * k := by omega
    exact le_trans (pow_le_pow_right₀ (le_of_lt h) hkk) (le_add_of_nonneg_left (by positivity))

/-- For `k : ℕ` and `t ≥ 0`, `t ^ k * exp (-t) ≤ ((2k)/e) ^ k * exp (-(t/2))`.

The constant `(2k/e)^k` is the maximum of `x ↦ x^k exp (-(x/2))` on `[0,∞)`; the bound is the
standard way of trading the full exponential decay against the half decay at polynomial cost.
It is obtained from the single-variable inequality `y * exp (-y) ≤ exp (-1)`
(`Real.mul_exp_neg_le_exp_neg_one`) applied at `y = t/(2k)` and raised to the `k`-th power. -/
lemma pow_mul_exp_neg_le_exp_neg_half (k : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    t ^ k * Real.exp (-t) ≤ ((2 * (k : ℝ)) / Real.exp 1) ^ k * Real.exp (-(t / 2)) := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    simp only [pow_zero, one_mul, Nat.cast_zero, mul_zero, zero_div]
    exact Real.exp_le_exp.mpr (by linarith)
  · have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
    -- the single-variable bound `t * exp (-(t/(2k))) ≤ (2k)/e`
    have hkey : t * Real.exp (-(t / (2 * (k : ℝ)))) ≤ 2 * (k : ℝ) / Real.exp 1 := by
      have h1 := Real.mul_exp_neg_le_exp_neg_one (t / (2 * (k : ℝ)))
      have h2 : (2 * (k : ℝ)) * ((t / (2 * (k : ℝ))) * Real.exp (-(t / (2 * (k : ℝ)))))
          ≤ (2 * (k : ℝ)) * Real.exp (-1) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
      have h3 : (2 * (k : ℝ)) * ((t / (2 * (k : ℝ))) * Real.exp (-(t / (2 * (k : ℝ)))))
          = t * Real.exp (-(t / (2 * (k : ℝ)))) := by
        field_simp
      rw [h3] at h2
      have h4 : (2 * (k : ℝ)) * Real.exp (-1) = 2 * (k : ℝ) / Real.exp 1 := by
        rw [Real.exp_neg, div_eq_mul_inv, mul_comm]
      rwa [h4] at h2
    -- raise to the `k`-th power
    have hnonneg : 0 ≤ t * Real.exp (-(t / (2 * (k : ℝ)))) := by positivity
    have hpow : (t * Real.exp (-(t / (2 * (k : ℝ))))) ^ k ≤ (2 * (k : ℝ) / Real.exp 1) ^ k :=
      pow_le_pow_left₀ hnonneg hkey k
    -- `(t * exp (-(t/(2k))))^k = t^k * exp (-(t/2))`
    have hL : (t * Real.exp (-(t / (2 * (k : ℝ))))) ^ k * Real.exp (-(t / 2))
        = t ^ k * Real.exp (-t) := by
      rw [mul_pow, ← Real.exp_nat_mul]
      have hexp : (k : ℝ) * (-(t / (2 * (k : ℝ)))) = -(t / 2) := by field_simp
      rw [hexp, mul_assoc, ← Real.exp_add, show -(t / 2) + -(t / 2) = -t by ring]
    rw [← hL]
    exact mul_le_mul_of_nonneg_right hpow (Real.exp_pos _).le

/-- The half-decayed Gaussian `z ↦ exp (-‖z‖²/2)` is integrable on `ℂ` against Lebesgue measure.

This is the `b = 1/2`, `c = 0`, `w = 0` case of
`GaussianFourier.integrable_cexp_neg_mul_sq_norm_add`. -/
lemma integrable_exp_neg_half_norm_sq :
    Integrable (fun z : ℂ => Real.exp (-(‖z‖ ^ 2) / 2)) (volume : Measure ℂ) := by
  have h := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
    (V := ℂ) (b := (1 / 2 : ℂ)) (by norm_num) 0 0
  have h2 : Integrable
      (fun v : ℂ =>
        (Complex.exp (-(1 / 2 : ℂ) * ((‖v‖ : ℝ) : ℂ) ^ 2
          + 0 * ((inner ℝ (0 : ℂ) v : ℝ) : ℂ))).re) (volume : Measure ℂ) := h.re
  refine h2.congr ?_
  filter_upwards with v
  have harg : -(1 / 2 : ℂ) * ((‖v‖ : ℝ) : ℂ) ^ 2 + 0 * ((inner ℝ (0 : ℂ) v : ℝ) : ℂ)
      = ((-(‖v‖ ^ 2) / 2 : ℝ) : ℂ) := by push_cast; ring
  rw [harg, Complex.exp_ofReal_re]

/-- Pointwise domination of the Gaussian moment integrand: for every `k : ℕ` and `z : ℂ`,

    `‖z‖^k * exp (-‖z‖²) ≤ (1 + ((2k)/e)^k) * exp (-‖z‖²/2)`.

Writing `t = ‖z‖²`, this combines `t^{k/2} ≤ 1 + t^k`
(`pow_le_one_add_pow_two_mul`), `exp (-t) ≤ exp (-t/2)` and the moment bound
`t^k exp (-t) ≤ ((2k)/e)^k exp (-t/2)` (`pow_mul_exp_neg_le_exp_neg_half`). -/
lemma norm_pow_mul_exp_neg_le (k : ℕ) (z : ℂ) :
    (‖z‖ : ℝ) ^ k * Real.exp (-(1 * ‖z‖ ^ 2))
      ≤ (1 + ((2 * (k : ℝ)) / Real.exp 1) ^ k) * Real.exp (-(‖z‖ ^ 2) / 2) := by
  have hz : (0 : ℝ) ≤ ‖z‖ := norm_nonneg z
  have hsq : (0 : ℝ) ≤ ‖z‖ ^ 2 := by positivity
  have hexp1 : Real.exp (-(1 * ‖z‖ ^ 2)) = Real.exp (-(‖z‖ ^ 2)) := by ring_nf
  rw [hexp1]
  have h1 : (‖z‖ : ℝ) ^ k ≤ 1 + (‖z‖ ^ 2) ^ k := by
    have h := pow_le_one_add_pow_two_mul k (‖z‖) hz
    rwa [pow_mul] at h
  have h2 : (‖z‖ ^ 2) ^ k * Real.exp (-(‖z‖ ^ 2))
      ≤ ((2 * (k : ℝ)) / Real.exp 1) ^ k * Real.exp (-(‖z‖ ^ 2) / 2) := by
    have h := pow_mul_exp_neg_le_exp_neg_half k (‖z‖ ^ 2) hsq
    rwa [show -(‖z‖ ^ 2 / 2) = -(‖z‖ ^ 2) / 2 by ring] at h
  have hexp2 : Real.exp (-(‖z‖ ^ 2)) ≤ Real.exp (-(‖z‖ ^ 2) / 2) :=
    Real.exp_le_exp.mpr (by linarith)
  calc (‖z‖ : ℝ) ^ k * Real.exp (-(‖z‖ ^ 2))
      ≤ (1 + (‖z‖ ^ 2) ^ k) * Real.exp (-(‖z‖ ^ 2)) :=
        mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
    _ = Real.exp (-(‖z‖ ^ 2)) + (‖z‖ ^ 2) ^ k * Real.exp (-(‖z‖ ^ 2)) := by ring
    _ ≤ Real.exp (-(‖z‖ ^ 2) / 2)
          + ((2 * (k : ℝ)) / Real.exp 1) ^ k * Real.exp (-(‖z‖ ^ 2) / 2) :=
        add_le_add hexp2 h2
    _ = (1 + ((2 * (k : ℝ)) / Real.exp 1) ^ k) * Real.exp (-(‖z‖ ^ 2) / 2) := by ring

/-- The `b = 1` case of the radial Gaussian moment integrability: `z ↦ ‖z‖^k e^{-‖z‖²}` is
integrable on `ℂ` against Lebesgue measure.  Obtained by dominating with the integrable
function `(1 + ((2k)/e)^k) * exp (-‖z‖²/2)` and applying `Integrable.mono'`. -/
lemma integrable_norm_pow_mul_exp_neg_one (k : ℕ) :
    Integrable (fun z : ℂ => (‖z‖ : ℝ) ^ k * Real.exp (-(1 * ‖z‖ ^ 2)))
      (volume : Measure ℂ) := by
  have hbase := integrable_exp_neg_half_norm_sq
  refine Integrable.mono' (hbase.const_mul (1 + ((2 * (k : ℝ)) / Real.exp 1) ^ k)) ?_ ?_
  · exact (by fun_prop : Continuous
      (fun z : ℂ => (‖z‖ : ℝ) ^ k * Real.exp (-(1 * ‖z‖ ^ 2)))).aestronglyMeasurable
  · filter_upwards with z
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact norm_pow_mul_exp_neg_le k z

end GaussAux

/-- **Polynomials are integrable against the Gaussian measure.**  For all `A B : ℕ`,
`z ↦ z^A z̄^B` is integrable with respect to `gauss = volume.withDensity (e^{-‖z‖²}/π)`.

Reduced to Lebesgue integrability of `z ↦ (e^{-‖z‖²}/π) • (z^A z̄^B)` by
`integrable_withDensity_iff_integrable_smul`, whose norm is
`e^{-‖z‖²}/π * ‖z‖^{A+B}`, dominated by the integrable
`π⁻¹ (1 + (2k/e)^k) e^{-‖z‖²/2}`. -/
theorem Gauss_integrable (A B : ℕ) :
    MeasureTheory.Integrable (fun z : ℂ => z ^ A * (starRingEnd ℂ z) ^ B) Work.BoseB4.gauss := by
  rw [gauss, integrable_withDensity_iff_integrable_smul measurable_gaussWeight]
  have hk : Integrable (fun z : ℂ => (‖z‖ : ℝ) ^ (A + B) * Real.exp (-(1 * ‖z‖ ^ 2)))
      (volume : Measure ℂ) := GaussAux.integrable_norm_pow_mul_exp_neg_one (A + B)
  refine Integrable.mono' (hk.const_mul (Real.pi)⁻¹) ?_ ?_
  · exact (measurable_gaussWeight.smul
      (by fun_prop : Measurable fun z : ℂ => z ^ A * (starRingEnd ℂ z) ^ B)).aestronglyMeasurable
  · filter_upwards with z
    have h1 : ‖gaussWeight z • (z ^ A * (starRingEnd ℂ z) ^ B)‖
        = (gaussWeight z : ℝ) * ‖z‖ ^ (A + B) := by
      rw [NNReal.smul_def, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ (gaussWeight z : ℝ)), norm_mul, norm_pow, norm_pow,
        Complex.norm_conj, ← pow_add]
    rw [h1, gaussWeight_coe]
    have hexp : Real.exp (-(1 * ‖z‖ ^ 2)) = Real.exp (-(‖z‖ ^ 2)) := by ring_nf
    rw [hexp]
    apply le_of_eq
    ring

end Work.BoseB4
