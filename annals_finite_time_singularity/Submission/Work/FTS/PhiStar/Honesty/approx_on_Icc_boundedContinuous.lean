import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Honesty

/-- On a compact interval `Icc a b`, every `L²` (a.e.-measurable, square-integrable) function
can be approximated in `L²` by a bounded continuous function. -/
theorem approx_on_Icc_boundedContinuous {f : ℝ → ℝ} {a b : ℝ}
    (hfmeas : AEMeasurable f)
    (hfsq : MeasureTheory.IntegrableOn (fun t : ℝ => (f t) ^ 2) (Set.Icc a b))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ G : ℝ → ℝ, Continuous G ∧ (∃ M : ℝ, ∀ t : ℝ, |G t| ≤ M) ∧
      MeasureTheory.IntegrableOn (fun t : ℝ => (f t - G t) ^ 2) (Set.Icc a b) ∧
      (∫ t in Set.Icc a b, (f t - G t) ^ 2) ≤ ε := by
  -- We work with the restricted measure `volume.restrict (Icc a b)`, which is weakly
  -- regular (it is a finite measure on a pseudometrizable space), and in which `f` is `L²`
  -- by `hfsq`.  Mathlib's density of bounded continuous functions in `Lᵖ` (`p < ∞`) then
  -- produces a bounded continuous `g` with `∫ ‖f - g‖ ^ 2 ≤ ε`.
  have hwreg : (MeasureTheory.volume.restrict (Set.Icc a b)).WeaklyRegular :=
    MeasureTheory.Measure.WeaklyRegular.restrict_of_measure_ne_top (by
      rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
  have h_ae : AEMeasurable f (MeasureTheory.volume.restrict (Set.Icc a b)) :=
    hfmeas.mono_measure MeasureTheory.Measure.restrict_le_self
  have haesm : MeasureTheory.AEStronglyMeasurable f
      (MeasureTheory.volume.restrict (Set.Icc a b)) :=
    aestronglyMeasurable_iff_aemeasurable.mpr h_ae
  have hmem' : MeasureTheory.MemLp f 2 (MeasureTheory.volume.restrict (Set.Icc a b)) :=
    (MeasureTheory.memLp_two_iff_integrable_sq haesm).mpr hfsq
  have hmem : MeasureTheory.MemLp f (ENNReal.ofReal 2)
      (MeasureTheory.volume.restrict (Set.Icc a b)) := by
    rwa [show ENNReal.ofReal (2:ℝ) = (2 : ENNReal) from by norm_num]
  obtain ⟨g, hgint, hgmem⟩ :=
    hmem.exists_boundedContinuous_integral_rpow_sub_le (by norm_num : (0:ℝ) < 2) hε
  refine ⟨fun t => g t, g.continuous, ⟨‖g‖, fun t => ?_⟩, ?_, ?_⟩
  · simpa [Real.norm_eq_abs] using g.norm_coe_le_norm t
  · -- integrability of `(f - G)²`, from `MemLp` of the difference
    have hsub : MeasureTheory.MemLp (f - ⇑g) (ENNReal.ofReal 2)
        (MeasureTheory.volume.restrict (Set.Icc a b)) :=
      hmem.sub hgmem
    have hsub' : MeasureTheory.MemLp (f - ⇑g) 2
        (MeasureTheory.volume.restrict (Set.Icc a b)) := by
      rwa [show ENNReal.ofReal (2:ℝ) = (2 : ENNReal) from by norm_num] at hsub
    exact hsub'.integrable_sq
  · -- the `L²` bound, after rewriting `‖·‖ ^ (2 : ℝ)` as a square
    have hpt : ∀ t : ℝ, (f t - ⇑g t) ^ 2 = ‖f t - ⇑g t‖ ^ (2:ℝ) := fun t => by
      rw [Real.norm_eq_abs, Real.rpow_two, sq_abs]
    have h1 : (∫ t, (f t - ⇑g t) ^ 2
        ∂(MeasureTheory.volume.restrict (Set.Icc a b))) ≤ ε := by
      rw [show (∫ t, (f t - ⇑g t) ^ 2
              ∂(MeasureTheory.volume.restrict (Set.Icc a b)))
            = ∫ t, ‖f t - ⇑g t‖ ^ (2:ℝ)
              ∂(MeasureTheory.volume.restrict (Set.Icc a b)) from
          MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpt)]
      exact hgint
    simpa using h1

end Work.FTS.PhiStar.Honesty
