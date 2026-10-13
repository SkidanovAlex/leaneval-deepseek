/-
Copyright: work module for the Elgindi finite-time singularity project.

# A.e. strong measurability of the `η`-weighted square of an angular slice

Vocabulary shared by the `remov/SourceBound` stretch of the elliptic estimates.

* `ae_mem_Ioo_of_mem_Iθ` : almost every point of `Iθ = [0,π/2]` lies in the open interval
  `(0,π/2)` (the two endpoints are null).
* `aesm_slice_sq_mul_sEta` : if `A` is continuous on the open quadrant `Q0 = (0,∞)×(0,π/2)`
  then for every `z > 0` the angular slice `θ ↦ A z θ ^ 2 * sEta θ` is a.e. strongly
  measurable for `volume.restrict Iθ`.

The second lemma is the measurability input of every "extract a single slot of `HkMem`"
argument: `HkMem` only supplies integrability of the *weighted* square
`(DzIter i g · w/sin(2θ)^{η/2})²`, whose angular integrability has to be transferred to the
unweighted form `(DzIter i g)² sin(2θ)^{-η}`; that transfer is an a.e. domination, and
`Integrable.mono'` requires the a.e. strong measurability of the dominated function.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.aesm_slice_of_continuousOn_Qd
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.StraightDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.remov.SourceBound

set_option autoImplicit false

/-- Almost every point of `Iθ = [0,π/2]` lies in the open interval `(0,π/2)`. -/
theorem ae_mem_Ioo_of_mem_Iθ :
    ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ), θ ∈ Set.Ioo (0 : ℝ) (π / 2) := by
  have h : (volume.restrict (Set.Ioo (0 : ℝ) (π / 2)) : Measure ℝ)
      = volume.restrict Work.Spaces.Iθ :=
    MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioo_ae_eq_Icc
  rw [← h]
  exact MeasureTheory.ae_restrict_mem measurableSet_Ioo

/-- `sEta` is continuous on the open angular interval. -/
theorem continuousOn_sEta_Ioo :
    ContinuousOn Work.FTS.EllipticEst.sEta (Set.Ioo (0 : ℝ) (π / 2)) := by
  have hsin : ContinuousOn (fun θ : ℝ => Real.sin (2 * θ)) (Set.Ioo (0 : ℝ) (π / 2)) :=
    (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn
  unfold Work.FTS.EllipticEst.sEta
  exact ContinuousOn.rpow hsin continuousOn_const (fun θ hθ => Or.inl (ne_of_gt
    (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1])
      (by linarith [hθ.2, Real.pi_pos]))))

/-- **A.e. strong measurability of the `η`-weighted square of an angular slice.**

If `A` is continuous on the open quadrant `Q0 = (0,∞) × (0,π/2)`, then for every `z > 0` the
slice `θ ↦ (A z θ)² · sEta θ` is a.e. strongly measurable for `volume.restrict Iθ`. -/
theorem aesm_slice_sq_mul_sEta {A : ℝ → ℝ → ℝ}
    (hA : ContinuousOn (Function.uncurry A) Work.FTS.EllipticEst.Q0) {z : ℝ} (hz : 0 < z) :
    AEStronglyMeasurable (fun θ => (A z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      (volume.restrict Work.Spaces.Iθ) := by
  have hse : ContinuousOn (fun p : ℝ × ℝ => Work.FTS.EllipticEst.sEta p.2)
      Work.FTS.EllipticEst.Q0 :=
    continuousOn_sEta_Ioo.comp continuous_snd.continuousOn
      (fun p hp => (Work.FTS.EllipticEst.mem_Q0.mp hp).2)
  have hcont : ContinuousOn
      (fun p : ℝ × ℝ => (A p.1 p.2) ^ 2 * Work.FTS.EllipticEst.sEta p.2)
      Work.FTS.EllipticEst.Q0 :=
    (hA.pow 2).mul hse
  exact Work.Spaces.aesm_slice_of_continuousOn_Qd
    (fun p : ℝ × ℝ => (A p.1 p.2) ^ 2 * Work.FTS.EllipticEst.sEta p.2) hcont hz

end Work.FTS.EllipticEst.remov.SourceBound
