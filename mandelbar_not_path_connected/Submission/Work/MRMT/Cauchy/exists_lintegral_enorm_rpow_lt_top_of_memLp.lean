import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# A finite-exponent `L^r` bound for compactly supported `L^p` functions

If `ν : ℂ → ℂ` lies in `L^p` for some `p > 2` and has compact support, then some exponent
`s` with `2 < s ≤ p` and `s < ∞` has finite `L^s`-type integral `∫ ‖ν w‖ₑ ^ s`.

When `p` is finite one may take `s = p` and read the integral bound directly off `MemLp`.
When `p = ∞` this fails on the infinite-measure space `ℂ`, but compact support restores it:
`ν` is essentially bounded and supported in a compact (finite measure) set.
-/

namespace Work.MRMT.Cauchy

open MeasureTheory ENNReal Function
open scoped ENNReal Topology

/-- An essentially bounded function on `ℂ` with compact support has finite `L^r`-type
integral for every real `r > 0`. -/
theorem lintegral_enorm_rpow_lt_top_of_memLp_top_of_hasCompactSupport
    {ν : ℂ → ℂ} (hν : MeasureTheory.MemLp ν ⊤ (MeasureTheory.volume : MeasureTheory.Measure ℂ))
    (hs : HasCompactSupport ν) {r : ℝ} (hr : 0 < r) :
    (∫⁻ w, ‖ν w‖ₑ ^ r) < ⊤ := by
  have hae : AEStronglyMeasurable ν (MeasureTheory.volume : MeasureTheory.Measure ℂ) :=
    hν.aestronglyMeasurable
  have hess : eLpNormEssSup ν (MeasureTheory.volume : MeasureTheory.Measure ℂ) < ⊤ := by
    rw [← eLpNorm_exponent_top hae]
    exact hν.eLpNorm_lt_top
  rw [eLpNormEssSup_lt_top_iff_isBoundedUnder, Filter.IsBoundedUnder] at hess
  obtain ⟨C, hC⟩ := hess
  have hC0 : ∀ᵐ w ∂(MeasureTheory.volume : MeasureTheory.Measure ℂ), ‖ν w‖₊ ≤ C :=
    Filter.eventually_map.mp hC
  have hC' : ∀ᵐ w ∂(MeasureTheory.volume : MeasureTheory.Measure ℂ),
      ‖ν w‖ₑ ≤ (C : ℝ≥0∞) :=
    hC0.mono fun w hw => by simpa using hw
  have hmono : (fun w => ‖ν w‖ₑ ^ r) ≤ᵐ[(MeasureTheory.volume : MeasureTheory.Measure ℂ)]
      (tsupport ν).indicator (fun _ => (C : ℝ≥0∞) ^ r) := by
    filter_upwards [hC'] with w hw
    by_cases hwK : w ∈ tsupport ν
    · rw [Set.indicator_of_mem hwK]
      exact ENNReal.rpow_le_rpow hw (le_of_lt hr)
    · rw [Set.indicator_of_notMem hwK, image_eq_zero_of_notMem_tsupport hwK, enorm_zero,
        ENNReal.zero_rpow_of_pos hr]
  calc (∫⁻ w, ‖ν w‖ₑ ^ r)
      ≤ ∫⁻ w, (tsupport ν).indicator (fun _ => (C : ℝ≥0∞) ^ r) w := lintegral_mono_ae hmono
    _ = (C : ℝ≥0∞) ^ r * (MeasureTheory.volume : MeasureTheory.Measure ℂ) (tsupport ν) :=
        lintegral_indicator_const hs.isCompact.measurableSet _
    _ < ⊤ := ENNReal.mul_lt_top
        (ENNReal.rpow_lt_top_of_nonneg (le_of_lt hr) ENNReal.coe_ne_top)
        hs.isCompact.measure_lt_top

theorem exists_lintegral_enorm_rpow_lt_top_of_memLp {ν : ℂ → ℂ} {p : ENNReal} (hp : 2 < p)
    (hν : MeasureTheory.MemLp ν p (MeasureTheory.volume : MeasureTheory.Measure ℂ))
    (hs : HasCompactSupport ν) :
    ∃ s : ENNReal, 2 < s ∧ s ≤ p ∧ s < ⊤ ∧ (∫⁻ w, ‖ν w‖ₑ ^ (s.toReal)) < ⊤ := by
  by_cases hptop : p = ⊤
  · subst hptop
    refine ⟨3, by norm_num, le_top, by norm_num, ?_⟩
    have h : ((3 : ENNReal).toReal) = (3 : ℝ) := by norm_num
    rw [h]
    exact lintegral_enorm_rpow_lt_top_of_memLp_top_of_hasCompactSupport hν hs (by norm_num)
  · refine ⟨p, hp, le_rfl, lt_top_iff_ne_top.mpr hptop, ?_⟩
    have hp0 : p ≠ 0 := by
      intro h
      rw [h] at hp
      exact absurd hp (by norm_num)
    exact lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top hp0 hptop hν.eLpNorm_lt_top

end Work.MRMT.Cauchy
