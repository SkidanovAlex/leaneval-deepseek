import Mathlib
import Submission.Work.KT.FP.PencilDefs
import Submission.Work.KT.Fund.SpectralAux

namespace Work.KT.FP

open Matrix MeasureTheory intervalIntegral
open scoped Topology Interval

noncomputable section

/-- **Deformation invariance of the pencil resolvent circle integral.**

If the pencil `z ↦ z • A + B` is invertible on the closed annulus `r ≤ ‖z‖ ≤ s` (`0 < r ≤ s`), then
the contour integral `∮_{|z| = ρ} (zA + B)⁻¹ A dz` is independent of the radius `ρ ∈ [r, s]`; here
stated for the two endpoints.

Route: this is a verbatim adaptation of `Work.KT.Fund.circleIntegral_resolvent_eq` in
`Submission/Work/KT/Fund/SpectralAux.lean` (which does the case `A = 1`, `B = -b`).  With
`f z := Ring.inverse (z • A + B) * A`:
* `z ↦ z • A + B` is continuous, `Ring.inverse` is continuous on the units
  (`NormedRing.inverse_continuousAt`), hence `f` is continuous on the closed annulus
  `Metric.closedBall 0 s \ Metric.ball 0 r`;
* `f` is holomorphic on the open annulus: `DifferentiableAt ℂ (fun z => z • A + B) z` and
  `.inverse` with the `IsUnit` hypothesis, then `.mul_const A`;
* conclude with `Complex.circleIntegral_eq_of_differentiable_on_annulus_off_countable`
  (with `s := ∅`), noting `pCirc A B ρ = ∮ z in C(0, ρ), f z`. -/
theorem pCirc_eq_of_annulus {R : Type*} [NormedRing R] [NormedAlgebra ℂ R] [CompleteSpace R]
    (A B : R) {r s : ℝ} (hr : 0 < r) (hrs : r ≤ s)
    (hunit : ∀ z : ℂ, r ≤ ‖z‖ → ‖z‖ ≤ s → IsUnit (z • A + B)) :
    pCirc A B s = pCirc A B r := by
  have hle_closedBall : ∀ z : ℂ, z ∈ Metric.closedBall (0:ℂ) s → ‖z‖ ≤ s :=
    fun z hz => by simpa [Metric.mem_closedBall, dist_zero_right] using hz
  have hge_not_ball : ∀ z : ℂ, z ∉ Metric.ball (0:ℂ) r → r ≤ ‖z‖ := by
    intro z hz
    by_contra hcon
    exact hz (by simpa [Metric.mem_ball, dist_zero_right] using not_le.mp hcon)
  have hge_not_closedBall : ∀ z : ℂ, z ∉ Metric.closedBall (0:ℂ) r → r ≤ ‖z‖ := by
    intro z hz
    by_contra hcon
    exact hz (by
      rw [Metric.mem_closedBall, dist_zero_right]
      exact le_of_lt (not_le.mp hcon))
  have hle_ball : ∀ z : ℂ, z ∈ Metric.ball (0:ℂ) s → ‖z‖ ≤ s :=
    fun z hz => by
      have : ‖z‖ < s := by simpa [Metric.mem_ball, dist_zero_right] using hz
      exact le_of_lt this
  have hann : ∀ z ∈ (Metric.closedBall (0:ℂ) s \ Metric.ball (0:ℂ) r), IsUnit (z • A + B) :=
    fun z hz => hunit z (hge_not_ball z hz.2) (hle_closedBall z hz.1)
  have hunits : ContinuousOn Ring.inverse {x : R | IsUnit x} := by
    intro x hx
    simpa only [IsUnit.unit_spec hx] using (NormedRing.inverse_continuousAt hx.unit).continuousWithinAt
  have hlin : Continuous fun z : ℂ => z • A + B :=
    (continuous_id.smul continuous_const).add continuous_const
  have hres : ContinuousOn (fun z : ℂ => Ring.inverse (z • A + B))
      (Metric.closedBall (0:ℂ) s \ Metric.ball (0:ℂ) r) := by
    have := hunits.comp hlin.continuousOn (fun z hz => hann z hz)
    simpa [Function.comp_def] using this
  have hcont : ContinuousOn (fun z : ℂ => pResA A B z)
      (Metric.closedBall (0:ℂ) s \ Metric.ball (0:ℂ) r) := by
    have hconst : ContinuousOn (fun _ : ℂ => A)
        (Metric.closedBall (0:ℂ) s \ Metric.ball (0:ℂ) r) := continuousOn_const
    exact (hres.mul hconst).congr (fun z _ => by simp [pResA, pRes])
  have hdiff : ∀ z ∈ (Metric.ball (0:ℂ) s \ Metric.closedBall (0:ℂ) r),
      DifferentiableAt ℂ (fun z : ℂ => pResA A B z) z := by
    intro z hz
    have hzr : r ≤ ‖z‖ := hge_not_closedBall z hz.2
    have hzs : ‖z‖ ≤ s := hle_ball z hz.1
    have hg : DifferentiableAt ℂ (fun y : ℂ => y • A + B) z :=
      (((differentiableAt_id : DifferentiableAt ℂ (fun y : ℂ => y) z)).smul_const A).add_const B
    have h := (hg.inverse (hunit z hzr hzs)).mul_const A
    simpa [pResA, pRes] using h
  exact Complex.circleIntegral_eq_of_differentiable_on_annulus_off_countable (c := 0) hr hrs
    Set.countable_empty hcont (fun z hz => hdiff z hz.1)

end

end Work.KT.FP
