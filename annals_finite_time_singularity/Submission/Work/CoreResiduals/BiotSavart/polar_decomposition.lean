/-
# Polar (spherical) decomposition of Lebesgue measure on `ℝ³`

A reusable form of the change of variables

`∫_{ℝ³} F(x) dx = ∫_{S²} ∫_{(0,∞)} F(r • u) d(volumeIoiPow 2)(r) d(volume.toSphere)(u)`

for an arbitrary (Bochner-integrable or not) real-valued function `F`, obtained from
`MeasureTheory.Measure.measurePreserving_homeomorphUnitSphereProd`.
-/
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.Topology.Separation.CompletelyRegular
import Submission.Work.LWP.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace Work.CoreResiduals.BiotSavart

/-- `Module.finrank ℝ ℝ³ = 3`. -/
lemma finrank_R3 : Module.finrank ℝ Work.LWP.R3 = 3 := by
  simp [Work.LWP.R3, finrank_euclideanSpace]

/-- **Polar decomposition of `ℝ³`.**  Integration against Lebesgue measure on `ℝ³` can be
written as an iterated integral over the unit sphere (`Measure.toSphere`) and the radial
measure `Measure.volumeIoiPow 2` on `(0,∞)` (which has density `r ↦ r²` with respect to
Lebesgue measure). -/
lemma polar_decomposition (F : Work.LWP.R3 → ℝ) :
    ∫ x, F x ∂(volume : Measure Work.LWP.R3)
      = ∫ p : Metric.sphere (0 : Work.LWP.R3) 1 × Set.Ioi (0:ℝ),
          F (p.2.1 • (p.1.1 : Work.LWP.R3))
          ∂((volume : Measure Work.LWP.R3).toSphere.prod (Measure.volumeIoiPow 2)) := by
  have hmp := MeasureTheory.Measure.measurePreserving_homeomorphUnitSphereProd
    (μ := (volume : Measure Work.LWP.R3))
  rw [finrank_R3] at hmp
  conv_lhs => rw [← restrict_compl_singleton (μ := (volume : Measure Work.LWP.R3)) (0 : Work.LWP.R3)]
  rw [← integral_subtype_comap (measurableSet_singleton (0:Work.LWP.R3)).compl F]
  have hcongr : ∀ x : ({0}ᶜ : Set Work.LWP.R3),
      (fun p : Metric.sphere (0 : Work.LWP.R3) 1 × Set.Ioi (0:ℝ) =>
          F (p.2.1 • (p.1.1 : Work.LWP.R3)))
        (homeomorphUnitSphereProd Work.LWP.R3 x) = F ↑x := by
    intro x
    have h := homeomorphUnitSphereProd_symm_apply_coe Work.LWP.R3
      (homeomorphUnitSphereProd Work.LWP.R3 x)
    rw [Homeomorph.symm_apply_apply] at h
    exact congrArg F h.symm
  rw [show (∫ x : ({0}ᶜ : Set Work.LWP.R3),
              F ↑x ∂(Measure.comap Subtype.val (volume : Measure Work.LWP.R3)))
        = ∫ x, (fun p : Metric.sphere (0 : Work.LWP.R3) 1 × Set.Ioi (0:ℝ) =>
              F (p.2.1 • (p.1.1 : Work.LWP.R3)))
            (homeomorphUnitSphereProd Work.LWP.R3 x)
            ∂(Measure.comap Subtype.val (volume : Measure Work.LWP.R3))
        from integral_congr_ae (Filter.Eventually.of_forall fun x => (hcongr x).symm)]
  exact hmp.integral_comp (Homeomorph.measurableEmbedding _)
    (fun p : Metric.sphere (0 : Work.LWP.R3) 1 × Set.Ioi (0:ℝ) =>
      F (p.2.1 • (p.1.1 : Work.LWP.R3)))

end Work.CoreResiduals.BiotSavart
