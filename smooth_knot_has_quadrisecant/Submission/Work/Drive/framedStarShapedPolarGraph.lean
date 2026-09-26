import Mathlib
import Submission.Work.Drive.framedPolarDefs
import Submission.Work.Drive.framePathDefs
import Submission.Work.Drive.framePath
import Submission.Work.Drive.contDiff_framedSliceFamily
import Submission.Work.Drive.isSmoothKnot_framedCurve

namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant

/-- **Framed star-shaped polar graphs are unknotted.**

If `(f1, f2)` is an orthonormal pair of vectors, `lam` is analytic,
`period`-periodic and positive and `psi` is analytic with
`psi (t + period) = psi t + period` and `0 < deriv psi t`, then the curve
`t ↦ c + lam t • (cos (psi t) • f1 + sin (psi t) • f2)` is unknotted: the
isotopy is the single analytic formula
`(t, s) ↦ (1 - s) • c + starRad lam s t • (cos (starAngle psi s t) • g s).1 + sin (starAngle psi s t) • (g s).2)`
where `g` is an analytic path of orthonormal pairs from `(f1, f2)` to `(e1, e2)`
(`Work.Drive.framePathExists`): at `s = 0` it is the given curve, at `s = 1`
the round circle `t ↦ cos t • e1 + sin t • e2 = standardCircle t`, and every
slice is a smooth knot (`Work.Drive.isSmoothKnot_framedCurve`). -/
theorem framedStarShapedPolarGraph {lam psi : ℝ → ℝ}
    (c f1 f2 : LeanEval.KnotTheory.Quadrisecant.Space)
    (h1 : ‖f1‖ = 1) (h2 : ‖f2‖ = 1) (hperp : inner ℝ f1 f2 = 0)
    (hlam : ContDiff ℝ ⊤ lam)
    (hlamper : Function.Periodic lam LeanEval.KnotTheory.Quadrisecant.period)
    (hlampos : ∀ t : ℝ, 0 < lam t)
    (hpsi : ContDiff ℝ ⊤ psi)
    (hpsishift : ∀ t : ℝ, psi (t + LeanEval.KnotTheory.Quadrisecant.period)
      = psi t + LeanEval.KnotTheory.Quadrisecant.period)
    (hpsideriv : ∀ t : ℝ, 0 < deriv psi t) :
    LeanEval.KnotTheory.Quadrisecant.IsUnknotted
      (fun t : ℝ => c + lam t • (Real.cos (psi t) • f1 + Real.sin (psi t) • f2)) := by
  obtain ⟨g, hg_cont, hg0, hg1, horth⟩ := framePathExists h1 h2 hperp
  refine ⟨fun t s => framedSlice lam psi c g s t,
    contDiff_framedSliceFamily c hlam hpsi hg_cont, ?_, ?_, ?_⟩
  · intro t
    change framedSlice lam psi c g 0 t
      = c + lam t • (Real.cos (psi t) • f1 + Real.sin (psi t) • f2)
    simp [framedSlice, starRad, starAngle, hg0]
  · intro t
    change framedSlice lam psi c g 1 t = standardCircle t
    simp [framedSlice, starRad, starAngle, hg1, standardCircle, vec3_decomp]
  · intro s hs
    obtain ⟨hs1, hs2, hsperp⟩ := horth s hs
    rw [show (fun t : ℝ => framedSlice lam psi c g s t)
        = (fun t : ℝ => framedCurve lam psi c (g s).1 (g s).2 s t) from
      funext fun t => framedSlice_eq_framedCurve lam psi c g s t]
    exact isSmoothKnot_framedCurve (u := (g s).1) (v := (g s).2) hs1 hs2 hsperp
      hlam hlamper hlampos hpsi hpsishift hpsideriv hs

end Work.Drive
