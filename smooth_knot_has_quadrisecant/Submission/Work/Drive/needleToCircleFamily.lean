import Mathlib
import Submission.Work.Drive.framedCInfSlices
import Submission.Work.Drive.isUnknotted_of_starShapedPolarGraph
import Submission.Work.Drive.polarCircle_isSmoothKnot
import Submission.Work.Drive.framedStarShapedPolarGraph

/-!
# The needle-to-circle family

`Work.Drive.sweepNeedleToCircle_clauses`: the **low end of the chord sweep**.  The needle of the
sweep is a thin lens; the workspace's planned route to the round circle interpolates its *polar
data* to the constant data of a circle.  The polar data is data (`Work.Drive.framedCurve` consumes
the radius function `lam` and the angle function `psi`), so the interpolation itself is pure
bookkeeping — this file does it once and for all.

Given `C^∞` polar data `(lam, psi)` of a closed curve `N t = c + lam t • (cos (psi t) • u + sin (psi t) • v)`
about an orthonormal frame `(u, v)` — `lam > 0` and `period`-periodic, `psi` strictly increasing with
`psi (t + period) = psi t + period` — the single formula

  `t ↦ framedCurve lam psi c u v s t = (1 - s) • c + starRad lam s t • (cos (starAngle psi s t) • u
      + sin (starAngle psi s t) • v)`

is a jointly `C^∞` (hence jointly `C¹`) family of `C^∞` knots running from the needle `N` (at `s = 0`)
to the **round circle** `t ↦ cos t • u + sin t • v` (at `s = 1`).  All five clauses are instances of
the lemmas of `Work.Drive.framedCInfSlices` and `Work.Drive.isSmoothKnot_framedCurve`, which were
proved exactly for this purpose; nothing here is new mathematics.

The companion facts needed to *apply* this (that the circle is unknotted — `framedStarShapedPolarGraph`
— and analytic — `polarCircle_isSmoothKnot`) are already in the workspace.
-/

noncomputable section
namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant
open scoped Real Topology

/-- **The needle-to-circle family (structural clauses).**  The framed polar interpolation of `C^∞`
polar data is a jointly `C¹` family of `C^∞` knots, `period`-periodic in the curve parameter,
starting at the polar graph `N` and ending at the round circle of the frame `(u, v)`. -/
theorem sweepNeedleToCircle_clauses {lam psi : ℝ → ℝ} {c u v : Space}
    (h1 : ‖u‖ = 1) (h2 : ‖v‖ = 1) (hperp : inner ℝ u v = 0)
    (hlam : ContDiff ℝ cInfT lam) (hpsi : ContDiff ℝ cInfT psi)
    (hlampos : ∀ t : ℝ, 0 < lam t) (hlamper : Function.Periodic lam period)
    (hψ : StrictMono psi) (hpsishift : ∀ t : ℝ, psi (t + period) = psi t + period)
    (hpsideriv : ∀ t : ℝ, 0 < deriv psi t) :
    ContDiff ℝ 1 (fun p : ℝ × ℝ => framedCurve lam psi c u v p.2 p.1) ∧
    (∀ s t : ℝ,
      framedCurve lam psi c u v s (t + period) = framedCurve lam psi c u v s t) ∧
    (∀ s ∈ Set.Icc (0 : ℝ) 1, IsCInfKnot (fun t : ℝ => framedCurve lam psi c u v s t)) ∧
    (∀ t : ℝ,
      framedCurve lam psi c u v 0 t
        = c + lam t • (Real.cos (psi t) • u + Real.sin (psi t) • v)) ∧
    (∀ t : ℝ, framedCurve lam psi c u v 1 t = Real.cos t • u + Real.sin t • v) := by
  have hjoint : ContDiff ℝ cInfT (fun p : ℝ × ℝ => framedCurve lam psi c u v p.2 p.1) := by
    have h := framedSlice_contDiff_cInf (lam := lam) (psi := psi) c
      (g := fun _ : ℝ => (u, v)) hlam hpsi contDiff_const
    simpa [framedSlice_eq_framedCurve] using h
  refine ⟨hjoint.of_le one_le_cInfT, ?_, ?_, ?_, ?_⟩
  · intro s t
    exact framedCurve_periodic c u v s hlamper hpsishift t
  · intro s hs
    exact isCInfKnot_framedCurve_cInf h1 h2 hperp hlam hpsi hlampos hlamper hψ hpsishift
      hpsideriv hs.1 hs.2
  · intro t
    rw [framedCurve_eq]
    simp [starRad_zero, starAngle_zero, frameDir]
  · intro t
    rw [framedCurve_eq]
    simp [starRad_one, starAngle_one, frameDir]

end Work.Drive
