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
/-- **The inverse branch `gD6` of `f_c^6` is holomorphic on the level-`0` region `Δ̂₀`.**  Given
the pull-back `Set.BijOn` of level `1` onto level `0` (`Work.ELAssembly.pullD_bij` applied at
`n = 0`; taken here as a hypothesis so that this does not depend on that file), the branch
`gD6 c L N = Function.invFunOn (F6 c) (polyRegion [Za 1, Zb 1, Zc 1] (Dlev L 1))` is the inverse
of the holomorphic injection `f_c^6 = (Tsq c)^[3]` on the open set
`U = polyRegion [Za 1, Zb 1, Zc 1] (Dlev L 1)`.  By `Work.ELRig.analyticOnNhd_invFunOn`
`invFunOn (F6 c) U` is analytic on `F6 c '' U = polyRegion [Za 0, Zb 0, Zc 0] (Dlev L 0)`,
whence the conclusion by `AnalyticOnNhd.differentiableOn`.  Openness of `U` is
`Work.ELTop.isOpen_polyRegion` with the unconditional `Work.ELTop.isClosed_polyCurve`; the
analyticity of `F6 c = (Tsq c)^[3]` is `Work.LandLeaves.analyticAt_tsq_iterate`. -/
theorem diffOn_gD6 {c : ℂ} {d : Work.EL.RootParabolic c} {L : ℝ} {N : NestPairs d}
    (hbij : Set.BijOn (Work.ELNest.F6 c)
      (Work.EL.polyRegion [N.Za 1, N.Zb 1, N.Zc 1] (Work.ELNest.Dlev L 1))
      (Work.EL.polyRegion [N.Za 0, N.Zb 0, N.Zc 0] (Work.ELNest.Dlev L 0))) :
    DifferentiableOn ℂ (gD6 c L N)
      (Work.EL.polyRegion [N.Za 0, N.Zb 0, N.Zc 0] (Work.ELNest.Dlev L 0)) := by
  -- the level-`1` region `U` is open (its boundary `polyCurve` is always closed)
  have hUopen : IsOpen (Work.EL.polyRegion [N.Za 1, N.Zb 1, N.Zc 1]
      (Work.ELNest.Dlev L 1)) :=
    Work.ELTop.isOpen_polyRegion d.hN [N.Za 1, N.Zb 1, N.Zc 1] (Work.ELNest.Dlev L 1)
      (Work.ELTop.isClosed_polyCurve d.hN [N.Za 1, N.Zb 1, N.Zc 1] (Work.ELNest.Dlev L 1))
  -- `F6 c = (Tsq c)^[3]` is analytic everywhere
  have hf : AnalyticOnNhd ℂ (Work.ELNest.F6 c)
      (Work.EL.polyRegion [N.Za 1, N.Zb 1, N.Zc 1] (Work.ELNest.Dlev L 1)) :=
    fun z _ => Work.LandLeaves.analyticAt_tsq_iterate c 3 z
  -- the set-theoretic inverse of an injective analytic map is analytic on the image
  have hAn := Work.ELRig.analyticOnNhd_invFunOn hUopen hf hbij.injOn
  rw [hbij.image_eq] at hAn
  exact hAn.differentiableOn

end Work.ELAssembly
