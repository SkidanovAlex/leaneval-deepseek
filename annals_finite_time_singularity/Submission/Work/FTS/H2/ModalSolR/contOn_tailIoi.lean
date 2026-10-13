import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Separation.CompletelyRegular
import Submission.Work.FTS.EllipticEst.remov.Ebs.abs_integral_mul_le_sqrt

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Filter
open scoped Topology

namespace Work.FTS.H2.ModalSolR

/-- **Continuity of the tail integral at a fixed lower limit.**  If `f` is integrable on the
tail `Set.Ioi a`, then the map `z ↦ ∫ t in Set.Ioi z, f t` is continuous at every point of
`Set.Ioi a`.

Proof: fix `z₀ ∈ Ioi a` and let `μ = volume.restrict (Ioi a)`.  For `z ∈ Ioi a` one has
`∫ t in Ioi z, f t = ∫ t, (Set.Ioi z).indicator f t ∂μ` (`MeasureTheory.integral_indicator`
together with `Measure.restrict_restrict_of_subset`), so the claim follows from Lebesgue's
dominated convergence theorem for filters (`MeasureTheory.tendsto_integral_filter_of_dominated_convergence`),
with dominating function `t ↦ ‖f t‖` (integrable on `Ioi a`) and pointwise limit
`(Set.Ioi z).indicator f t → (Set.Ioi z₀).indicator f t` for every `t ≠ z₀`; the exceptional
point `z₀` is null.  The limit function integrates to `∫ t in Set.Ioi z₀, f t`, again by
`MeasureTheory.integral_indicator` and `Measure.restrict_restrict_of_subset`. -/
theorem continuousOn_integral_Ioi {f : ℝ → ℝ} {a : ℝ}
    (hf : MeasureTheory.IntegrableOn f (Set.Ioi a)) :
    ContinuousOn (fun z => ∫ t in Set.Ioi z, f t) (Set.Ioi a) := by
  intro z₀ hz₀
  -- the a.e. pointwise convergence of the indicator functions
  have hlim : ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Ioi a)),
      Tendsto (fun z => (Set.Ioi z).indicator f t) (𝓝[Set.Ioi a] z₀)
        (𝓝 ((Set.Ioi z₀).indicator f t)) := by
    have h1 : (MeasureTheory.volume.restrict (Set.Ioi a)) {z₀} = 0 := by
      rw [Measure.restrict_apply (measurableSet_singleton z₀)]
      exact measure_mono_null Set.inter_subset_left Real.volume_singleton
    have h2 : ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Ioi a)), t ∈ ({z₀} : Set ℝ)ᶜ :=
      MeasureTheory.compl_mem_ae_iff.2 h1
    filter_upwards [h2] with t ht
    rcases lt_trichotomy t z₀ with h | h | h
    · -- `t < z₀`: eventually `z > t`, so both indicator functions vanish at `t`
      have hev : ∀ᶠ z in 𝓝[Set.Ioi a] z₀, t < z := by
        rw [eventually_nhdsWithin_iff]
        filter_upwards [Ioi_mem_nhds h] with z hz _
        exact hz
      refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
      filter_upwards [hev] with z hz
      rw [Set.indicator_of_notMem (s := Set.Ioi z₀) (by rw [Set.mem_Ioi]; exact not_lt.mpr h.le),
        Set.indicator_of_notMem (s := Set.Ioi z) (by rw [Set.mem_Ioi]; exact not_lt.mpr hz.le)]
    · -- `t = z₀`, excluded by the a.e. statement
      exact absurd h ht
    · -- `z₀ < t`: eventually `z < t`, so both indicator functions are `f t`
      have hev : ∀ᶠ z in 𝓝[Set.Ioi a] z₀, z < t := by
        rw [eventually_nhdsWithin_iff]
        filter_upwards [Iio_mem_nhds h] with z hz _
        exact hz
      refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
      filter_upwards [hev] with z hz
      rw [Set.indicator_of_mem (s := Set.Ioi z₀) (by rw [Set.mem_Ioi]; exact h),
        Set.indicator_of_mem (s := Set.Ioi z) (by rw [Set.mem_Ioi]; exact hz)]
  -- dominated convergence
  have hDCT := MeasureTheory.tendsto_integral_filter_of_dominated_convergence
    (μ := MeasureTheory.volume.restrict (Set.Ioi a))
    (l := 𝓝[Set.Ioi a] z₀)
    (F := fun z t => (Set.Ioi z).indicator f t)
    (f := fun t => (Set.Ioi z₀).indicator f t)
    (bound := fun t => ‖f t‖)
    (Filter.Eventually.of_forall fun z => hf.aestronglyMeasurable.indicator measurableSet_Ioi)
    (Filter.Eventually.of_forall fun z =>
      Filter.Eventually.of_forall fun t => norm_indicator_le_norm_self (s := Set.Ioi z) f t)
    hf.norm
    hlim
  -- the limit value
  have hcod : (∫ t, (Set.Ioi z₀).indicator f t ∂(MeasureTheory.volume.restrict (Set.Ioi a)))
      = ∫ t in Set.Ioi z₀, f t := by
    rw [MeasureTheory.integral_indicator measurableSet_Ioi,
      Measure.restrict_restrict_of_subset (Set.Ioi_subset_Ioi hz₀.le)]
  -- the function whose integral the DCT controls is `z ↦ ∫ t in Ioi z, f t` on `Ioi a`
  have hdom : (fun z => ∫ t, (Set.Ioi z).indicator f t ∂(MeasureTheory.volume.restrict (Set.Ioi a)))
      =ᶠ[𝓝[Set.Ioi a] z₀] (fun z => ∫ t in Set.Ioi z, f t) :=
    eventually_nhdsWithin_of_forall fun z hz => by
      show (∫ t, (Set.Ioi z).indicator f t ∂(MeasureTheory.volume.restrict (Set.Ioi a)))
        = ∫ t in Set.Ioi z, f t
      rw [MeasureTheory.integral_indicator measurableSet_Ioi,
        Measure.restrict_restrict_of_subset (Set.Ioi_subset_Ioi hz.le)]
  have hres := Filter.Tendsto.congr' hdom hDCT
  rw [hcod] at hres
  exact hres

set_option linter.unusedVariables false

/-- Continuity on `(0,∞)` of the tail integral `z ↦ ∫ t in Set.Ioi z, c t · w t`, under the same
hypotheses as `contOn_primitive_Ioc` except that the integrability of `c · w` is assumed on the
tail `Set.Ioi z` for every `z > 0`.  Route: for `z₀ > 0` and `z` near `z₀`, write the difference
with `intervalIntegral.integral_Ioi_sub_Ioi'` (which gives `∫_{Ioi z₀} - ∫_{Ioi z} = ∫_{z₀}^{z}`,
and `∫_{Ioi z} - ∫_{Ioi z₀} = ∫_z^{z₀}` in the other direction) and bound
`|∫_{(z₀,z)} c w| ≤ M·√(∫_{(z₀,z)} c²)·√|z - z₀|` with `M` a bound for `w` on the compact
`[z₀/2, 3z₀/2]`. -/
theorem contOn_tailIoi {c w : ℝ → ℝ}
    (hc : MeasureTheory.IntegrableOn (fun t => c t ^ 2) (Set.Ioi 0))
    (hcm : MeasureTheory.AEStronglyMeasurable c (MeasureTheory.volume.restrict (Set.Ioi 0)))
    (hw : ContinuousOn w (Set.Ioi 0))
    (hint : ∀ z ∈ Set.Ioi 0,
      MeasureTheory.IntegrableOn (fun t => c t * w t) (Set.Ioi z)) :
    ContinuousOn (fun z => ∫ t in Set.Ioi z, c t * w t) (Set.Ioi 0) := by
  -- `Continuity on (0,∞)` is a local statement: at `z₀ > 0` it is continuity of the tail
  -- integral with lower limit `z₀/2`, which is a genuine tail (so `c * w` is integrable on it)
  -- and, being an open neighbourhood of `z₀`, has the same neighbourhood filter.
  intro z₀ hz₀
  have hhalf : (0 : ℝ) < z₀ / 2 := by linarith [show (0 : ℝ) < z₀ from hz₀]
  have hlt : z₀ / 2 < z₀ := by linarith
  have hcont : ContinuousWithinAt (fun z => ∫ t in Set.Ioi z, c t * w t) (Set.Ioi (z₀ / 2)) z₀ :=
    continuousOn_integral_Ioi (f := fun t => c t * w t) (a := z₀ / 2)
      (hint (z₀ / 2) hhalf) z₀ hlt
  have hca : ContinuousAt (fun z => ∫ t in Set.Ioi z, c t * w t) z₀ :=
    (continuousWithinAt_iff_continuousAt (Ioi_mem_nhds hlt)).mp hcont
  exact hca.continuousWithinAt

end Work.FTS.H2.ModalSolR
