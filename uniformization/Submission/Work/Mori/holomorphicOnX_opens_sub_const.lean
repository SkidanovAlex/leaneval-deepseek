import Mathlib
import Submission.Work.Mori.Defs

namespace Work.Mori

/-- **Chart bookkeeping for an open subset of `ℂ`.**  The preferred chart of the subspace `U` at
`u` is the restriction of the identity chart of `ℂ` to `U`, so it is the inclusion:
`(chartAt ℂ u) z = (z : ℂ)`. -/
private theorem chartAt_opens_apply (U : TopologicalSpace.Opens ℂ) (u z : U) :
    (chartAt ℂ u) z = (z : ℂ) := by
  rw [TopologicalSpace.Opens.chartAt_eq (x := u), OpenPartialHomeomorph.subtypeRestr_coe]
  rfl

/-- **The inclusion of an open subset of `ℂ` is holomorphic.**  For `U : TopologicalSpace.Opens ℂ`
and `p : ℂ`, the function `fun z : U => (z : ℂ) - p` is holomorphic on all of the one-dimensional
complex manifold `U`.

The chart of `U` restricted from the identity chart of `ℂ` makes the chart representation of this
function the identity (minus a constant), which is complex analytic: this is the type-level plumbing
that lets a holomorphic function on `ℂ` be restricted to an open subset, and it is needed to apply
`Work.Parabolic.holomorphicOnX_comp_biholomorph` to `fun z : U => (z : ℂ) - p` with `U` the open
image of a biholomorphism.  (`Work.Modulus.Defs` has the analogous facts for the punctured surface
`puncturedOpens z₀`, which is the same kind of subtype of a charted space.) -/
theorem holomorphicOnX_opens_sub_const (U : TopologicalSpace.Opens ℂ) (p : ℂ) :
    Submission.HolomorphicOnX (fun z : U => (z : ℂ) - p) Set.univ := by
  intro u _
  rw [Submission.HolomorphicOnXAt]
  -- the chart of the subspace evaluates at points of `U` as the inclusion into `ℂ`
  have hcomp : ∀ z : U, (chartAt ℂ u) z = (z : ℂ) := fun z => chartAt_opens_apply U u z
  rw [hcomp u]
  -- so the chart representation of `fun z => z - p` is `fun w => w - p`, which is analytic
  have hana : AnalyticAt ℂ (fun w : ℂ => w - p) (u : ℂ) := analyticAt_id.sub analyticAt_const
  refine hana.congr ?_
  filter_upwards [(chartAt ℂ u).open_target.mem_nhds
    ((chartAt ℂ u).map_source (mem_chart_source ℂ u))] with w hw
  have hwu : (((chartAt ℂ u).symm w : U) : ℂ) = w := by
    rw [← hcomp ((chartAt ℂ u).symm w)]
    exact (chartAt ℂ u).right_inv hw
  simp only [Function.comp_apply]
  rw [hwu]

end Work.Mori
