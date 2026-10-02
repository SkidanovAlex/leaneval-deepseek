import Mathlib
import Submission.Work.ELAssembly.PullInputs
import Submission.Work.ELRig.analyticOnNhd_invFunOn
import Submission.Work.ELTop.isOpen_polyRegion
import Submission.Work.ELTop.isClosed_polyCurve
import Submission.Work.LandLeaves.analyticAt_tsq_iterate

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.ELAssembly

-- Shell: `namespace Work.ELAssembly` (area `Submission/Work/ELAssembly/`).
/-- **The inverse branch `gQ` of `F c` is holomorphic on the level-`0` region `Q̂₀`.**  Given the
pull-back `Set.BijOn` of level `1` onto level `0` (`Work.ELAssembly.pullQ_bij` applied at `n = 0`;
taken here as a hypothesis so that this does not depend on that file), the branch
`gQ c d L P0 N = Function.invFunOn (F c) (polyRegion [P0, N.Qp 1] (Qlev L 1))` is the inverse of
the holomorphic injection `F c = (Tsq c)^[5]` on the open set
`U = polyRegion [P0, N.Qp 1] (Qlev L 1)`.  By
`Work.ELRig.analyticOnNhd_invFunOn` (`hU : IsOpen U`, `AnalyticOnNhd ℂ f U`, `InjOn f U`)
`invFunOn (F c) U` is analytic on `F c '' U = polyRegion [P0, N.Qp 0] (Qlev L 0)`, whence the
conclusion by `AnalyticOnNhd.differentiableOn`.  Openness of `U` is
`Work.ELTop.isOpen_polyRegion` with the unconditional `Work.ELTop.isClosed_polyCurve`; the
analyticity of `F c` (a polynomial, `F c = (Tsq c)^[5]`) is
`Work.LandLeaves.analyticAt_tsq_iterate`. -/
theorem diffOn_gQ {c : ℂ} {d : Work.EL.RootParabolic c} {L : ℝ} {P0 : Work.EL.CoPair d.hN}
    {N : NestPairs d}
    (hbij : Set.BijOn (Work.EL.F c)
      (Work.EL.polyRegion [P0, N.Qp 1] (Work.ELNest.Qlev L 1))
      (Work.EL.polyRegion [P0, N.Qp 0] (Work.ELNest.Qlev L 0))) :
    DifferentiableOn ℂ (gQ c d L P0 N)
      (Work.EL.polyRegion [P0, N.Qp 0] (Work.ELNest.Qlev L 0)) := by
  have hU : IsOpen (Work.EL.polyRegion [P0, N.Qp 1] (Work.ELNest.Qlev L 1)) :=
    Work.ELTop.isOpen_polyRegion d.hN [P0, N.Qp 1] (Work.ELNest.Qlev L 1)
      (Work.ELTop.isClosed_polyCurve d.hN [P0, N.Qp 1] (Work.ELNest.Qlev L 1))
  have hf : AnalyticOnNhd ℂ (Work.EL.F c)
      (Work.EL.polyRegion [P0, N.Qp 1] (Work.ELNest.Qlev L 1)) :=
    fun z _ => Work.LandLeaves.analyticAt_tsq_iterate c 5 z
  have hinj : Set.InjOn (Work.EL.F c)
      (Work.EL.polyRegion [P0, N.Qp 1] (Work.ELNest.Qlev L 1)) := hbij.injOn
  have hdiff : DifferentiableOn ℂ
      (Function.invFunOn (Work.EL.F c)
        (Work.EL.polyRegion [P0, N.Qp 1] (Work.ELNest.Qlev L 1)))
      (Work.EL.polyRegion [P0, N.Qp 0] (Work.ELNest.Qlev L 0)) := by
    have h := (Work.ELRig.analyticOnNhd_invFunOn hU hf hinj).differentiableOn
    rwa [Set.BijOn.image_eq hbij] at h
  simpa only [gQ] using hdiff

end Work.ELAssembly
