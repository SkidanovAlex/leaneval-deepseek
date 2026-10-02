import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option linter.unusedVariables false

namespace Work.MRMT.Found

open MeasureTheory ENNReal
open scoped ENNReal

/-- **Markov-Chebyshev style `L²`-bound.**  If the `L²`-norm of `f` over `t` is at most `B`
and `s ⊆ t` carries finite volume, then whenever `B ^ 2 < c ^ 2 * vol s` there is a point of
`s` at which `‖f‖ ≤ c`.

Indeed, were `‖f w‖ > c` at every `w ∈ s`, then on `s` the constant function `c` would be
bounded by `‖f‖` pointwise, so
`ofReal c * (vol s) ^ (1/2) ≤ eLpNorm f 2 (volume.restrict t) ≤ ofReal B`,
and taking real parts and squaring gives `c ^ 2 * (vol s).toReal ≤ B ^ 2`, contradicting the
assumed reverse strict inequality. -/
theorem exists_norm_le_of_eLpNorm_two_le {f : ℂ → ℂ} {s t : Set ℂ} (hst : s ⊆ t)
    (hs : MeasurableSet s) (hvol : (MeasureTheory.volume : MeasureTheory.Measure ℂ) s ≠ ⊤)
    (hae : MeasureTheory.AEStronglyMeasurable f MeasureTheory.volume)
    {B c : ℝ} (hB : 0 ≤ B) (hc : 0 < c)
    (hle : MeasureTheory.eLpNorm f 2 (MeasureTheory.volume.restrict t) ≤ ENNReal.ofReal B)
    (hlt : B ^ 2 < c ^ 2 * ((MeasureTheory.volume : MeasureTheory.Measure ℂ) s).toReal) :
    ∃ w ∈ s, ‖f w‖ ≤ c := by
  by_contra hcon
  push Not at hcon
  set μ : Measure ℂ := (MeasureTheory.volume : MeasureTheory.Measure ℂ) with hμ
  -- The `L²`-norm over `s` is still bounded by `ofReal B` since `s ⊆ t`.
  have h1 : eLpNorm f 2 (μ.restrict s) ≤ ENNReal.ofReal B :=
    (eLpNorm_mono_measure f (Measure.restrict_mono_set μ hst)).trans hle
  -- The constant `c` is pointwise dominated by `‖f‖` a.e. on `s`.
  have h2 : eLpNorm (fun _ : ℂ => (c : ℂ)) 2 (μ.restrict s)
      ≤ eLpNorm f 2 (μ.restrict s) := by
    apply eLpNorm_mono_ae aestronglyMeasurable_const
    rw [ae_restrict_iff' hs]
    filter_upwards with x hx
    have hxc : ‖((fun _ : ℂ => (c : ℂ)) x)‖ = c := by
      rw [Complex.norm_real, Real.norm_of_nonneg hc.le]
    rw [hxc]
    exact le_of_lt (hcon x hx)
  -- Value of the `L²`-norm of a constant: `ofReal c * (vol s) ^ (1/2)`.
  have hval : eLpNorm (fun _ : ℂ => (c : ℂ)) 2 (μ.restrict s)
      = ENNReal.ofReal c * (μ s) ^ (1 / 2 : ℝ) := by
    rw [eLpNorm_const' (c : ℂ) (by norm_num) (by norm_num)]
    rw [ENNReal.toReal_ofNat, Measure.restrict_apply_univ]
    have h1' : ‖(c : ℂ)‖ₑ = ENNReal.ofReal c := by
      rw [← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg hc.le]
    rw [h1']
  have h3 : ENNReal.ofReal c * (μ s) ^ (1 / 2 : ℝ) ≤ ENNReal.ofReal B := by
    rw [← hval]
    exact h2.trans h1
  -- Pass to real numbers and extract `c * sqrt(vol s) ≤ B`.
  have hreal : c * Real.sqrt ((μ s).toReal) ≤ B := by
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top h3
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hc.le,
      ← ENNReal.toReal_rpow, ← Real.sqrt_eq_rpow, ENNReal.toReal_ofReal hB] at h
  -- Squaring gives `c ^ 2 * (vol s).toReal ≤ B ^ 2`.
  have hv : 0 ≤ (μ s).toReal := ENNReal.toReal_nonneg
  have hsq : (c * Real.sqrt ((μ s).toReal)) ^ 2 ≤ B ^ 2 :=
    pow_le_pow_left₀ (by positivity) hreal 2
  have hcs : (c * Real.sqrt ((μ s).toReal)) ^ 2 = c ^ 2 * (μ s).toReal := by
    rw [mul_pow, Real.sq_sqrt hv]
  rw [hcs] at hsq
  exact (not_le.mpr hlt) hsq

end Work.MRMT.Found
