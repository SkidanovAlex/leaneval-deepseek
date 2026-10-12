import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.SmallBoxA0.PolarSphere.polarNullAe
import Submission.Work.SmallBoxA0.UncondDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open MeasureTheory Metric
open scoped Real ENNReal

namespace Work.SmallBoxA0.PolarSphere

abbrev E3 := EuclideanSpace ℝ (Fin 3)
abbrev S2 := (Metric.sphere (0 : E3) 1)

/-- The spherical average `r ↦ ∫_{S²} g (r • ω) dσ(ω)` (definition `Work.SmallBoxA0.sphAvg` in `Submission.Work.SmallBoxA0.UncondDefs`) of an a.e. measurable function `g` on `ℝ³` is an a.e. measurable function of the radius.  Suggested route: transport `g` along the polar-coordinates homeomorphism using Mathlib's `Measure.measurePreserving_homeomorphUnitSphereProd` (as in `Work.SmallBoxBridge.Kernel.lintegralPolarR3`) and apply `MeasureTheory.AEStronglyMeasurable.integral_prod_right'`.  (Careful: the homeomorphism only covers the punctured space, so `r ≤ 0` needs a separate argument — e.g. `sphAvg g` is even because `volume.toSphere` is invariant under `ω ↦ -ω`.) -/
theorem aemeasurable_sphAvg {g : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hg : AEMeasurable g (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3)))) :
    AEMeasurable (Work.SmallBoxA0.sphAvg g) (MeasureTheory.volume : MeasureTheory.Measure ℝ) := by
  classical
  -- A measurable representative `f` of `g`.
  set f : E3 → ℝ := hg.mk g with hf_eq
  have hf_meas : Measurable f := hg.measurable_mk
  have hgf : g =ᵐ[(volume : Measure E3)] f := hg.ae_eq_mk
  -- The set where `f` and `g` differ is null; enlarge it to a measurable null set `M`.
  have hN0 : (volume : Measure E3) {x : E3 | f x ≠ g x} = 0 := by
    rw [show {x : E3 | f x ≠ g x} = {x : E3 | ¬ (g x = f x)} from
      Set.ext fun x => by simp only [Set.mem_ofPred_eq, ne_eq, eq_comm]]
    exact MeasureTheory.ae_iff.mp hgf
  set M : Set E3 := toMeasurable (volume : Measure E3) {x : E3 | f x ≠ g x} with hM_eq
  have hM_meas : MeasurableSet M := measurableSet_toMeasurable _ _
  have hM_null : (volume : Measure E3) M = 0 := by
    rw [hM_eq, measure_toMeasurable]; exact hN0
  have hM_sub : {x : E3 | f x ≠ g x} ⊆ M := subset_toMeasurable _ _
  -- Almost every spherical average of `f` agrees with that of `g`.
  have hae : Work.SmallBoxA0.sphAvg f =ᵐ[(volume : Measure ℝ)] Work.SmallBoxA0.sphAvg g := by
    filter_upwards [polarNullAe hM_meas hM_null] with r hr
    rw [sphAvg, sphAvg]
    refine integral_congr_ae ?_
    rw [Filter.EventuallyEq, MeasureTheory.ae_iff]
    refine measure_mono_null (fun ω hω => ?_) hr
    exact hM_sub hω
  -- Fubini: the spherical average of the measurable `f` is a.e. measurable.
  have hF : AEMeasurable (Work.SmallBoxA0.sphAvg f) (MeasureTheory.volume : MeasureTheory.Measure ℝ) := by
    have hASM : AEStronglyMeasurable (fun p : ℝ × S2 => f ((p.1 : ℝ) • ((p.2 : S2) : E3)))
        ((volume : Measure ℝ).prod (volume : Measure E3).toSphere) :=
      (hf_meas.comp (by fun_prop : Continuous
        (fun p : ℝ × S2 => (p.1 : ℝ) • ((p.2 : S2) : E3))).measurable).aemeasurable.aestronglyMeasurable
    have h2 : AEStronglyMeasurable (fun r : ℝ => ∫ ω : S2, f ((r : ℝ) • ((ω : S2) : E3))
          ∂(volume : Measure E3).toSphere) (volume : Measure ℝ) :=
      MeasureTheory.AEStronglyMeasurable.integral_prod_right' hASM
    show AEMeasurable (fun r : ℝ => ∫ ω : S2, f ((r : ℝ) • ((ω : S2) : E3))
          ∂(volume : Measure E3).toSphere) (volume : Measure ℝ)
    exact h2.aemeasurable
  exact hF.congr hae

end Work.SmallBoxA0.PolarSphere
