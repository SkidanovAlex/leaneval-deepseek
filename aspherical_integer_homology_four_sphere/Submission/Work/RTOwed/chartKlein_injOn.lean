import Mathlib
import Submission.Work.RTOwed.cuspChartBeta
import Submission.Work.RTOwed.cuspChartData
import Submission.Work.RTOwed.chartKlein_image_open
import Submission.Work.RTOwed.chartKlein_strict
import Submission.Work.RTOwed.cuspCert.cube_quad
import Submission.Work.RTOwed.cuspCert.CuspSupport

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open scoped Matrix

namespace Work.RTOwed

/-- **The cusp cube chart is injective on the upper half space.**

`chartKlein a q = kleinOfHyp (M_a · hypOfUHS q)` with `M_a = chartMatR a` (the real cast of the
integer table `chartMat a`).  The chart matrix satisfies
`(chartMat a)ᵀ · Jz · (chartMat a) = (chartScaleZ a)^2 • Jz` where `chartScaleZ a ∈ {1,2}`
(`chartMat_gramZ` in `Submission/Work/RTOwed/chartKlein_image_open.lean`), hence `M_a` is
invertible and `Q(M_a v) = (chartScale a)^2 · Q(v)` for the Lorentz form `Q`.

Therefore, if `chartKlein a q = chartKlein a q'` for two points of the upper half space
(`0 < q 3`, `0 < q' 3`), then the hyperboloid vectors `M_a · hypOfUHS q` and `M_a · hypOfUHS q'`
(which both lie on the level `Q = -(chartScale a)^2` with positive last coordinate) are proportional
with positive ratio; since the level fixes the ratio up to sign and both last coordinates are
positive, the ratio is `1`, so `M_a · hypOfUHS q = M_a · hypOfUHS q'`; a left inverse of `M_a` is
`(chartScale a)⁻² • Jz · M_aᵀ · Jz`.  Then `hypOfUHS q = hypOfUHS q'` and
`Work.HypModel.hypOfUHS_injOn` gives `q = q'`.

Useful tools: `Work.HypModel.kleinOfHyp_smul`, `Work.HypModel.hypOfKlein_kleinOfHyp`,
`Work.HypModel.kleinOfHyp_hypOfKlein`, `Work.HypModel.hypOfUHS_injOn`, `Work.HypModel.lorentz_hypOfUHS_self`.

The conclusion holds for all 48 `a` on the whole upper half space, no cube-region hypothesis. -/
theorem chartKlein_injOn (a : Fin 48) :
    Set.InjOn (Work.RTOwed.chartKlein a) {q : Work.RTOwed.CuspE4 | 0 < q 3} := by
  -- The normalised chart matrix `chartK a = (chartScale a)⁻¹ • chartMat a` is a Lorentz matrix,
  -- i.e. `(chartK a)ᵀ * J * (chartK a) = J` with `0 < chartK a 4 4`.
  have hK : Work.HypModel.IsLorentzMat (chartK a) := chartK_isLorentz a
  -- Such a matrix has left inverse `J * (chartK a)ᵀ * J`, hence acts injectively on `ℝ⁵`.
  have hmv : Function.Injective (chartK a).mulVec :=
    Work.FoldInst.foldInst_mulVec_injective_of_isometry hK.1
  intro q hq q' hq' h
  -- `0 < q 3` is exactly membership in the upper half space.
  have hqU : q ∈ Work.HypModel.upperHalfSpace := hq
  have hqU' : q' ∈ Work.HypModel.upperHalfSpace := hq'
  -- The chart is the Klein projection of the Lorentz image of the hyperboloid lift.
  have h1 : Work.HypModel.kleinOfHyp (chartK a *ᵥ Work.HypModel.hypOfUHS q)
      = Work.HypModel.kleinOfHyp (chartK a *ᵥ Work.HypModel.hypOfUHS q') := by
    rw [← chartKlein_eq a q, ← chartKlein_eq a q', h]
  -- Both Lorentz images lie on the upper sheet, where `kleinOfHyp` is a bijection with inverse
  -- `hypOfKlein`: applying `hypOfKlein` to `h1` recovers the vectors themselves.
  have hP : chartK a *ᵥ Work.HypModel.hypOfUHS q ∈ Work.HypModel.upperSheet :=
    Work.HypModel.mulVec_mem_upperSheet hK (Work.RTOwed.hypOfUHS_mem_upperSheet hqU)
  have hP' : chartK a *ᵥ Work.HypModel.hypOfUHS q' ∈ Work.HypModel.upperSheet :=
    Work.HypModel.mulVec_mem_upperSheet hK (Work.RTOwed.hypOfUHS_mem_upperSheet hqU')
  have h2 : chartK a *ᵥ Work.HypModel.hypOfUHS q = chartK a *ᵥ Work.HypModel.hypOfUHS q' := by
    have h3 := congrArg Work.HypModel.hypOfKlein h1
    rwa [Work.HypModel.hypOfKlein_kleinOfHyp hP,
      Work.HypModel.hypOfKlein_kleinOfHyp hP'] at h3
  -- Cancel the injective Lorentz matrix, then the injective upper half space lift.
  exact Work.HypModel.hypOfUHS_injOn hqU hqU' (hmv h2)

end Work.RTOwed
