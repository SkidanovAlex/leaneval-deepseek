import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.StrongEps.EpsLocalPStar.TraceToEpsMem

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsLocalPStar

open scoped Real Topology
open MeasureTheory Set Filter

/-- **Tracing the weighted `ℋ¹`-bound down to the `ε`-space — almost-everywhere version.**

Same as `TraceToEpsMem`, but the two vanishing-trace hypotheses are only required for
almost every `z > 0` (w.r.t. Lebesgue measure), rather than for every `z > 0`.  This is
exactly the form in which the traces are available along the flow of the `ε`-scheme (they
are produced by the angular trace theorems `SliceTraceO`/`SliceTracePiO` a.e. in `z`).

The proof is the proof of `TraceToEpsMem`: the pointwise traces were consumed only inside
the a.e.-in-`z` step `hpoint`, so the two a.e. trace hypotheses simply join the
`filter_upwards` there.  The only bookkeeping is that the a.e. statement is phrased for
`volume.restrict (Ioi 0)` while the slices are indexed by `z ∈ Iz = Ici 0`; the two
measures agree since `Ici 0 = Ioi 0 ∪ {0}` and `{0}` is null. -/
theorem TraceToEpsMemAe :
    ∃ C : ℝ, 0 < C ∧ ∀ α : ℝ, α ∈ Set.Ioc 0 1 → ∀ f : Work.FTS.Galerkin.Fn,
      Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 1 f →
      (∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi (0:ℝ))),
          Filter.Tendsto (fun θ => f z θ) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)) →
      (∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi (0:ℝ))),
          Filter.Tendsto (fun θ => f z θ) (nhdsWithin (Real.pi/2) (Set.Iio (Real.pi/2))) (nhds 0)) →
      Work.FTS.StrongEps.EpsMem α f ∧
        Work.FTS.StrongEps.EpsSq α f
          ≤ C / (Work.Spaces.gam α - 1) ^ 2 * Work.Spaces.HkSq α 1 f := by
  obtain ⟨CS, hCSpos, hCS⟩ := EpsSliceLe
  refine ⟨CS, hCSpos, fun α hα f hso hm ht1 ht2 => ?_⟩
  obtain ⟨hα0, hα1⟩ := hα
  -- the `(0,1)`-slot of `ℋ¹`
  obtain ⟨hslotInt, hslotLe⟩ := Slot01LeHkSq1 hso hm
  have hprod := Work.FTS.EllipticEst.AeSlotOneAe.Interp.integrable_uncurry_slot_mixed
    (α := α) (k := 1) (F := f) hso hm 0 1 (by norm_num) (by norm_num)
  have hslot_ae := hprod.prod_right_ae
  have hae_pos := Work.FTS.StrongEps.EpsSqTools.ae_pos_Iz
  -- the a.e. trace hypotheses are stated for `volume.restrict (Ioi 0)`, the slices are
  -- indexed by `z ∈ Iz = Ici 0`; the two restricted measures agree (`{0}` is null)
  have hIz : MeasureTheory.volume.restrict (Set.Ioi (0:ℝ))
      = MeasureTheory.volume.restrict Work.Spaces.Iz := by
    rw [Work.Spaces.Iz]
    exact MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioi_ae_eq_Ici
  have ht1' : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      Filter.Tendsto (fun θ => f z θ) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    rw [← hIz]; exact ht1
  have ht2' : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      Filter.Tendsto (fun θ => f z θ)
        (nhdsWithin (Real.pi/2) (Set.Iio (Real.pi/2))) (nhds 0) := by
    rw [← hIz]; exact ht2
  -- the slicewise Hardy bound, for almost every `z`
  have hpoint : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      MeasureTheory.Integrable (fun θ => (f z θ * Work.FTS.StrongEps.epsW α z θ) ^ 2)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) ∧
      (∫ θ in Work.Spaces.Iθ, (f z θ * Work.FTS.StrongEps.epsW α z θ) ^ 2)
          ≤ CS / (Work.Spaces.gam α - 1) ^ 2 *
            (∫ θ in Work.Spaces.Iθ, (Work.Spaces.mixed 0 1 f z θ * Work.Spaces.Wt α z θ) ^ 2) := by
    filter_upwards [hslot_ae, hae_pos, ht1', ht2'] with z hslot hz htz1 htz2
    have hcd : ContDiffOn ℝ 1 (fun θ => f z θ) (Set.Ioo 0 (Real.pi / 2)) :=
      (hso.curry_θ hz).of_le (show (1 : WithTop ℕ∞) ≤ Work.Stability.smoothOrder from by
        simp [Work.Stability.smoothOrder])
    exact hCS α (show α ∈ Set.Ioc 0 1 from ⟨hα0, hα1⟩) f z hz hcd htz1 htz2 hslot
  have hEint' : MeasureTheory.Integrable
      (fun z : ℝ => CS / (Work.Spaces.gam α - 1) ^ 2 *
        (∫ θ in Work.Spaces.Iθ, (Work.Spaces.mixed 0 1 f z θ * Work.Spaces.Wt α z θ) ^ 2))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := hslotInt.const_mul _
  -- the outer `z`-integral
  have hmain : (∫ z in Work.Spaces.Iz,
        ∫ θ in Work.Spaces.Iθ, (f z θ * Work.FTS.StrongEps.epsW α z θ) ^ 2)
      ≤ CS / (Work.Spaces.gam α - 1) ^ 2 * Work.Spaces.HkSq α 1 f := by
    refine le_trans ?_ (mul_le_mul_of_nonneg_left hslotLe (div_nonneg hCSpos.le (sq_nonneg _)))
    rw [← MeasureTheory.integral_const_mul]
    refine MeasureTheory.integral_mono_of_nonneg
      (Eventually.of_forall fun z => MeasureTheory.integral_nonneg fun θ => sq_nonneg _) hEint' ?_
    filter_upwards [hpoint] with z hz using hz.2
  refine ⟨?_, ?_⟩
  · -- `EpsMem α f`
    have hAESM : MeasureTheory.AEStronglyMeasurable
        (fun p : ℝ × ℝ => (f p.1 p.2 * Work.FTS.StrongEps.epsW α p.1 p.2) ^ 2)
        ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
      Work.Spaces.aesm_of_continuousOn_Qd _
        (ContinuousOn.pow (ContinuousOn.mul (hso.forall 0).continuousOn
          (Work.FTS.StrongEps.EpsSqTools.continuousOn_epsW α)) 2)
    have hslice : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
        MeasureTheory.HasFiniteIntegral
          (fun θ => (f z θ * Work.FTS.StrongEps.epsW α z θ) ^ 2)
          (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
      filter_upwards [hpoint] with z hz using hz.1.2
    have hzInt : MeasureTheory.HasFiniteIntegral
        (fun z : ℝ => ∫ θ, ‖(f z θ * Work.FTS.StrongEps.epsW α z θ) ^ 2‖
          ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
        (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
      have haesm : MeasureTheory.AEStronglyMeasurable
          (fun z : ℝ => ∫ θ, ‖(f z θ * Work.FTS.StrongEps.epsW α z θ) ^ 2‖
            ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
          (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
        hAESM.norm.integral_prod_right'
      have hbdd : (fun z : ℝ => ‖∫ θ, ‖(f z θ * Work.FTS.StrongEps.epsW α z θ) ^ 2‖
            ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ)‖)
          ≤ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iz]
          (fun z : ℝ => CS / (Work.Spaces.gam α - 1) ^ 2 *
            (∫ θ in Work.Spaces.Iθ,
              (Work.Spaces.mixed 0 1 f z θ * Work.Spaces.Wt α z θ) ^ 2)) := by
        filter_upwards [hpoint] with z hz
        rw [Real.norm_of_nonneg (MeasureTheory.integral_nonneg fun θ => norm_nonneg _)]
        refine le_trans (le_of_eq ?_) hz.2
        exact MeasureTheory.integral_congr_ae
          (Filter.Eventually.of_forall fun θ => Real.norm_of_nonneg (sq_nonneg _))
      exact (MeasureTheory.Integrable.mono' hEint' haesm hbdd).2
    have hmeas : (MeasureTheory.volume : Measure (ℝ × ℝ)).restrict (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)
        = (MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
      rw [MeasureTheory.Measure.volume_eq_prod, Measure.prod_restrict]
    rw [Work.FTS.StrongEps.EpsMem, MeasureTheory.IntegrableOn, hmeas]
    exact ⟨hAESM, (MeasureTheory.hasFiniteIntegral_prod_iff' hAESM).mpr ⟨hslice, hzInt⟩⟩
  · calc Work.FTS.StrongEps.EpsSq α f
        = ∫ z in Work.Spaces.Iz,
            ∫ θ in Work.Spaces.Iθ, (f z θ * Work.FTS.StrongEps.epsW α z θ) ^ 2 := rfl
      _ ≤ CS / (Work.Spaces.gam α - 1) ^ 2 * Work.Spaces.HkSq α 1 f := hmain

end Work.FTS.StrongEps.EpsLocalPStar
