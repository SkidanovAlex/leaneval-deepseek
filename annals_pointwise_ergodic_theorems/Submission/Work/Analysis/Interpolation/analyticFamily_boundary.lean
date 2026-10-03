import Mathlib
import Submission.Work.Analysis.Interpolation.Basic
import Submission.Port.Aesm

/-!
# Boundary estimates for the analytic family, with `L^∞` endpoints

The companion module `eLpNorm_analyticFamily_re_zero` / `_re_one` evaluates the `L^{p₀}`-seminorm
of the analytic family of a simple function on the two boundary lines of the interpolation strip
when the endpoint exponent `p₀` is **finite**.  For the exponent arithmetic of extended
nonnegative reals -- `p⁻¹ = (1 - θ) p₀⁻¹ + θ p₁⁻¹` -- one also needs the case `p₀ = ⊤`, i.e. an
endpoint exponent that is *infinite*, where the corresponding exponent `t = p / p₀` of the family
*drops to* `0` and the endpoint seminorm is the essential supremum.

This module provides the boundary estimates in the form needed by that argument.  With

* `P > 0` the exponent of the target seminorm (`P` stands for the *finite* exponent `p`),
* `s ∈ [1, ⊤]` an endpoint exponent,
* `t = P · s⁻¹ = P / s ∈ [0, P]` the (real) exponent that the family takes on the boundary line,

the family `z ↦ analyticFamily f ((1-z) t + z t₁)` of any function `f : α → ℂ` satisfies

`‖analyticFamily f t t₁ z‖_{L^s} ≤ ‖f‖_{L^P}^t`

on the boundary line `re z = 0` (and the analogous statement on `re z = 1` with `t` in the
second slot).  For finite `s` this is an equality; for `s = ⊤` we have `t = 0`, the family is
bounded pointwise by `1` (the exponent has real part `0`), and the essential supremum is `≤ 1`.

## Main results

* `Work.Analysis.Interpolation.eLpNorm_analyticFamily_re_of`;
* `Work.Analysis.Interpolation.eLpNorm_analyticFamily_re_zero_of`,
  `Work.Analysis.Interpolation.eLpNorm_analyticFamily_re_one_of`;
* `Work.Analysis.Interpolation.ofReal_toReal_const_eq_nonneg`.
-/

namespace Work.Analysis.Interpolation

open MeasureTheory
open scoped ENNReal NNReal

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- **Boundary estimate for the analytic family.**  Let `P > 0` and let `s ∈ [1, ∞]` be an
endpoint exponent.  Put `t = P · s⁻¹ = P / s` (with the convention `⊤⁻¹ = 0`), so that `t > 0`
when `s` is finite and `t = 0` when `s = ⊤`.  If at the parameter `z` the exponent family
`z ↦ (1 - z) t₀ + z t₁` has real part `t`, then the analytic family built from `f` has
`L^s`-seminorm at most `‖f‖_{L^P}^t`.

For finite `s` this is an identity, coming from the pointwise identity
`‖phasePow (f x) τ‖ₑ = ‖f x‖ₑ ^ τ.re` and the computation of the two `ℒˢ`-integrals; for
`s = ⊤` the exponent `t` vanishes and the pointwise bound `‖phasePow c τ‖ₑ ≤ 1`
(valid when `re τ = 0`) gives the claim. -/
theorem eLpNorm_analyticFamily_re_of {f : α → ℂ} {P t₀ t₁ t : ℝ} {s : ℝ≥0∞} {z : ℂ}
    (hP : 0 < P) (hs : 1 ≤ s) (ht : t = P * (s⁻¹).toReal)
    (hre : (expFamily ((t₀ : ℝ) : ℂ) ((t₁ : ℝ) : ℂ) z).re = t)
    (hF : AEStronglyMeasurable (analyticFamily f ((t₀ : ℝ) : ℂ) ((t₁ : ℝ) : ℂ) z) μ := by pw_aesm)
    (hf : AEStronglyMeasurable f μ := by pw_aesm) :
    eLpNorm (analyticFamily f ((t₀ : ℝ) : ℂ) ((t₁ : ℝ) : ℂ) z) s μ
      ≤ (eLpNorm f (ENNReal.ofReal P) μ) ^ t := by
  by_cases htop : s = ⊤
  · -- the `L^∞` endpoint: `t = 0` and the family is bounded pointwise by `1`
    have ht0 : t = 0 := by rw [ht, htop, ENNReal.inv_top, ENNReal.toReal_zero, mul_zero]
    subst ht0
    rw [htop, ENNReal.rpow_zero, eLpNorm_exponent_top hF]
    refine eLpNormEssSup_le_of_ae_enorm_bound (C := 1) ?_
    filter_upwards with x
    rw [analyticFamily]
    by_cases hx : f x = 0
    · rw [hx, phasePow_zero_left]
      simp
    · rw [enorm_phasePow hx, hre, ENNReal.rpow_zero]
  · -- a finite endpoint exponent: the boundary seminorm is a power of `‖f‖_{L^P}`
    have hs0 : s ≠ 0 := by rintro rfl; simp at hs
    have hspos : 0 < s.toReal := ENNReal.toReal_pos hs0 htop
    have htpos : 0 < t := by
      rw [ht, ENNReal.toReal_inv]
      exact mul_pos hP (inv_pos.mpr hspos)
    have hkey : t * s.toReal = P := by
      rw [ht, ENNReal.toReal_inv, mul_assoc, inv_mul_cancel₀ (ne_of_gt hspos), mul_one]
    have hcast : (1 / P) * t = 1 / s.toReal := by
      rw [ht, ENNReal.toReal_inv]
      field_simp
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (hf := hF) hs0 htop,
      lintegral_enorm_analyticFamily_rpow μ htpos hre,
      show s.toReal * t = P by rw [mul_comm]; exact hkey,
      eLpNorm_eq_lintegral_rpow_enorm_toReal (hf := hf) (p := ENNReal.ofReal P)
        (ENNReal.ofReal_ne_zero_iff.mpr hP) ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal hP.le,
      ← ENNReal.rpow_mul, hcast]

/-- Boundary estimate on the line `re z = 0`, where the exponent of the family is `t`. -/
theorem eLpNorm_analyticFamily_re_zero_of {f : α → ℂ} {P t t₁ : ℝ} {s : ℝ≥0∞} {z : ℂ}
    (hP : 0 < P) (hs : 1 ≤ s) (ht : t = P * (s⁻¹).toReal) (hz : z.re = 0)
    (hF : AEStronglyMeasurable (analyticFamily f ((t : ℝ) : ℂ) ((t₁ : ℝ) : ℂ) z) μ := by pw_aesm)
    (hf : AEStronglyMeasurable f μ := by pw_aesm) :
    eLpNorm (analyticFamily f ((t : ℝ) : ℂ) ((t₁ : ℝ) : ℂ) z) s μ
      ≤ (eLpNorm f (ENNReal.ofReal P) μ) ^ t :=
  eLpNorm_analyticFamily_re_of hP hs ht (by rw [expFamily_ofReal_re, hz]; ring) hF hf

/-- Boundary estimate on the line `re z = 1`, where the exponent of the family is `t`. -/
theorem eLpNorm_analyticFamily_re_one_of {f : α → ℂ} {P t₀ t : ℝ} {s : ℝ≥0∞} {z : ℂ}
    (hP : 0 < P) (hs : 1 ≤ s) (ht : t = P * (s⁻¹).toReal) (hz : z.re = 1)
    (hF : AEStronglyMeasurable (analyticFamily f ((t₀ : ℝ) : ℂ) ((t : ℝ) : ℂ) z) μ := by pw_aesm)
    (hf : AEStronglyMeasurable f μ := by pw_aesm) :
    eLpNorm (analyticFamily f ((t₀ : ℝ) : ℂ) ((t : ℝ) : ℂ) z) s μ
      ≤ (eLpNorm f (ENNReal.ofReal P) μ) ^ t :=
  eLpNorm_analyticFamily_re_of hP hs ht (by rw [expFamily_ofReal_re, hz]; ring) hF hf

/-- The `ofReal`/`toReal` conversion of a two-factor monomial: for a finite extended
nonnegative real `U` (resp. `V`) and a nonnegative exponent `ρ` (resp. `σ`),

`ofReal (m * U.toReal^ρ * V.toReal^σ) = ofReal m * U^ρ * V^σ`  (`m ≥ 0`).

This is the variant of `ofReal_toReal_const_eq` in which the exponents are only assumed
nonnegative -- the exponents of the analytic family are `P / s`, which vanishes at an infinite
endpoint exponent. -/
lemma ofReal_toReal_const_eq_nonneg {m : ℝ} (hm : 0 ≤ m) {U V : ℝ≥0∞} (hU : U < ⊤) (hV : V < ⊤)
    {ρ σ : ℝ} (hρ : 0 ≤ ρ) (hσ : 0 ≤ σ) :
    ENNReal.ofReal (m * U.toReal ^ ρ * V.toReal ^ σ) = ENNReal.ofReal m * U ^ ρ * V ^ σ := by
  have hUρ : ENNReal.ofReal (U.toReal ^ ρ) = U ^ ρ := by
    rw [← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg hρ,
      ENNReal.ofReal_toReal (ne_top_of_lt hU)]
  have hVσ : ENNReal.ofReal (V.toReal ^ σ) = V ^ σ := by
    rw [← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg hσ,
      ENNReal.ofReal_toReal (ne_top_of_lt hV)]
  rw [show m * U.toReal ^ ρ * V.toReal ^ σ = m * (U.toReal ^ ρ * V.toReal ^ σ) by ring,
    ENNReal.ofReal_mul hm, ENNReal.ofReal_mul (Real.rpow_nonneg ENNReal.toReal_nonneg ρ),
    hUρ, hVσ, mul_assoc]

end Work.Analysis.Interpolation
