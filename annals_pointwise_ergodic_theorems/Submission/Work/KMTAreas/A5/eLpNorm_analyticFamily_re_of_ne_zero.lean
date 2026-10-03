import Mathlib
import Submission.Work.Analysis.Interpolation.analyticFamily_boundary
import Submission.Port.Aesm

/-!
# The boundary estimate for the analytic family with a single hypothesis `s ≠ 0`

The module `Work.Analysis.Interpolation.analyticFamily_boundary` proves the boundary estimate

`‖analyticFamily f t₀ t₁ z‖_{L^s} ≤ ‖f‖_{L^P}^t`,  where `t = P · s⁻¹` and
`(expFamily t₀ t₁ z).re = t`,

under the hypothesis `1 ≤ s`.  The present lemma records the same estimate with the *weaker*
hypothesis `s ≠ 0` only: on the boundary line the assertion is an **identity** for a finite
endpoint exponent `s`, and the computation below (`eLpNorm` as the `1/s`-th power of the `ℒˢ`
integral, then the pointwise identity for the analytic family) never uses `1 ≤ s`; only
`0 < s.toReal`, i.e. `s ≠ 0` and `s ≠ ⊤`, is needed.  The remaining case `s = ⊤` forces
`t = 0`, and there the family is bounded pointwise by `1` because the real part of its exponent
vanishes.

## Main result

* `Work.KMTAreas.A5.eLpNorm_analyticFamily_re_of_ne_zero`.
-/

namespace Work.KMTAreas.A5

open MeasureTheory
open scoped ENNReal NNReal

/-- **Boundary estimate for the analytic family, with `s ≠ 0`.**  Let `P > 0`, let `s ≠ 0` be an
endpoint exponent (possibly `⊤`), put `t = P · s⁻¹` and suppose that at the parameter `z` the
exponent family `z ↦ (1 - z) t₀ + z t₁` has real part `t`.  Then the analytic family built from
`f` has `L^s`-seminorm at most `‖f‖_{L^P}^t`.

For a finite `s` this is an identity: expanding `eLpNorm` as the `(1/s.toReal)`-th power of the
`ℒˢ` integral, the pointwise identity `‖phasePow (f x) τ‖ₑ = ‖f x‖ₑ ^ τ.re` turns that integral
into the `P`-th power integral of `f`, and the exponent arithmetic `(1/P) · t = 1/s.toReal`
finishes.  No lower bound on `s` is used.  For `s = ⊤` we have `t = 0`, and the family is bounded
pointwise by `1` because the real part of its exponent vanishes, so the essential supremum is
`≤ 1 = ‖f‖_{L^P}^0`. -/
theorem eLpNorm_analyticFamily_re_of_ne_zero {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α} {f : α → ℂ} {P t₀ t₁ t : ℝ} {s : ENNReal} {z : ℂ} (hP : 0 < P) (hs : s ≠ 0) (ht : t = P * (s⁻¹).toReal) (hre : (Work.Analysis.Interpolation.expFamily ((t₀ : ℝ) : ℂ) ((t₁ : ℝ) : ℂ) z).re = t)
    (hF : AEStronglyMeasurable (Work.Analysis.Interpolation.analyticFamily f ((t₀ : ℝ) : ℂ) ((t₁ : ℝ) : ℂ) z) μ := by pw_aesm)
    (hf : AEStronglyMeasurable f μ := by pw_aesm) : MeasureTheory.eLpNorm (Work.Analysis.Interpolation.analyticFamily f ((t₀ : ℝ) : ℂ) ((t₁ : ℝ) : ℂ) z) s μ ≤ (MeasureTheory.eLpNorm f (ENNReal.ofReal P) μ) ^ t := by
  by_cases htop : s = ⊤
  · -- the `L^∞` endpoint: `t = 0` and the family is bounded pointwise by `1`
    have ht0 : t = 0 := by rw [ht, htop, ENNReal.inv_top, ENNReal.toReal_zero, mul_zero]
    subst ht0
    rw [htop, ENNReal.rpow_zero, eLpNorm_exponent_top hF]
    refine eLpNormEssSup_le_of_ae_enorm_bound (C := 1) ?_
    filter_upwards with x
    rw [Work.Analysis.Interpolation.analyticFamily]
    by_cases hx : f x = 0
    · rw [hx, Work.Analysis.Interpolation.phasePow_zero_left]
      simp
    · rw [Work.Analysis.Interpolation.enorm_phasePow hx, hre, ENNReal.rpow_zero]
  · -- a finite, nonzero endpoint exponent: the boundary seminorm is a power of `‖f‖_{L^P}`
    have hs0 : s ≠ 0 := hs
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
      Work.Analysis.Interpolation.lintegral_enorm_analyticFamily_rpow μ htpos hre,
      show s.toReal * t = P by rw [mul_comm]; exact hkey,
      eLpNorm_eq_lintegral_rpow_enorm_toReal (hf := hf) (p := ENNReal.ofReal P)
        (ENNReal.ofReal_ne_zero_iff.mpr hP) ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal hP.le,
      ← ENNReal.rpow_mul, hcast]

end Work.KMTAreas.A5
