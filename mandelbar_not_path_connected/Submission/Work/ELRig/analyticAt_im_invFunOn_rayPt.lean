import Mathlib
import Submission.Work.ELRig.CylLift
import Submission.Work.ELRig.analyticOnNhd_dynBottcher
import Submission.Work.ELRig.analyticOnNhd_invFunOn
import Submission.Work.ELRig.analyticOn_rayPt_of_analytic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.ELRig

open Set Filter
open scoped Topology

/-- **The imaginary part of the `Ψ`-preimage of a dynamic ray point is real-analytic in the level.**

For a root-parabolic parameter `d`, a parabolic flower `fl`, and a ray-cylinder lift `L` of the
flower, the preimage in the far-left half plane `{Re < -L.R}` of the level-`t` point of the root
ray `R(α₁)` — read through the inverse branch
`Function.invFunOn fl.Ψ {w | w.re < -L.R}` — has an imaginary part which depends real-analytically
on `t`, at every level `t > 1` whose ray point does lie in the image half plane.

Route.  The far-left half plane `U = {w | w.re < -L.R}` is open, `fl.Ψ` is entire (hence analytic
on `U`) and injective there (`L.hinj`), so `Function.invFunOn fl.Ψ U` is analytic on
`fl.Ψ '' U` (`Work.ELRig.analyticOnNhd_invFunOn`); in particular at the given ray point.  The
level-parametrisation `s ↦ Work.EL.rayPt d.hN α₁ s` is real-analytic on `(1, ∞)`
(`Work.ELRig.analyticOn_rayPt_of_analytic`, with the analyticity of the Böttcher coordinate
supplied by `Work.ELRig.analyticOnNhd_dynBottcher`).  The composite is therefore real-analytic
(complex analyticity restricts to `ℝ`, and `AnalyticAt.comp`), and applying the continuous linear
map `Complex.imCLM` preserves real-analyticity. -/
theorem analyticAt_im_invFunOn_rayPt {c : ℂ} (d : Work.EL.RootParabolic c)
    (fl : Work.EL.ParabolicFlower (Work.EL.F c) ((LeanEval.ComplexAnalysis.Tantibar c)^[5]) d.z₁)
    (L : Work.ELRig.RayCylLift d fl) {t : ℝ} (ht : 1 < t)
    (hmem : Work.EL.rayPt d.hN Work.EL.alpha1 t ∈ fl.Ψ '' {w : ℂ | w.re < -L.R}) :
    AnalyticAt ℝ (fun s : ℝ => (Function.invFunOn fl.Ψ {w : ℂ | w.re < -L.R}
      (Work.EL.rayPt d.hN Work.EL.alpha1 s)).im) t := by
  set U : Set ℂ := {w : ℂ | w.re < -L.R} with hUdef
  have hUopen : IsOpen U := isOpen_lt Complex.continuous_re continuous_const
  have hΨan : AnalyticOnNhd ℂ fl.Ψ U :=
    (fl.Ψ_diff.differentiableOn).analyticOnNhd hUopen
  have hgan : AnalyticOnNhd ℂ (Function.invFunOn fl.Ψ U) (fl.Ψ '' U) :=
    analyticOnNhd_invFunOn hUopen hΨan L.hinj
  have hgAt : AnalyticAt ℂ (Function.invFunOn fl.Ψ U)
      (Work.EL.rayPt d.hN Work.EL.alpha1 t) := hgan _ hmem
  have hray : AnalyticAt ℝ (fun s : ℝ => Work.EL.rayPt d.hN Work.EL.alpha1 s) t :=
    (analyticOn_rayPt_of_analytic d.hN (analyticOnNhd_dynBottcher d.bottcher)
      Work.EL.alpha1).analyticAt (isOpen_Ioi.mem_nhds ht)
  have hcomp : AnalyticAt ℝ
      (fun s : ℝ => Function.invFunOn fl.Ψ U (Work.EL.rayPt d.hN Work.EL.alpha1 s)) t :=
    AnalyticAt.comp (g := Function.invFunOn fl.Ψ U)
      (f := fun s : ℝ => Work.EL.rayPt d.hN Work.EL.alpha1 s) hgAt.restrictScalars hray
  have him : AnalyticAt ℝ (fun z : ℂ => z.im)
      (Function.invFunOn fl.Ψ U (Work.EL.rayPt d.hN Work.EL.alpha1 t)) :=
    Complex.imCLM.analyticAt _
  simpa [Function.comp_def] using
    (AnalyticAt.comp (g := fun z : ℂ => z.im)
      (f := fun s : ℝ => Function.invFunOn fl.Ψ U (Work.EL.rayPt d.hN Work.EL.alpha1 s))
      him hcomp)

end Work.ELRig
