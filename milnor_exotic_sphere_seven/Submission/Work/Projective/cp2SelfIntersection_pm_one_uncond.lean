import Mathlib
import Submission.Work.Projective.CP2Concrete
import Submission.Work.Projective.CP2Duality
import Submission.Work.Projective.cp2_hc
import Submission.Work.Projective.GoodCp2.localAssembly

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.Projective

open CategoryTheory Limits Work.Cohomology

set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

/-- **Poincaré duality for `ℂP²`**: the predicate `Good 4 cp2C Set.univ` of the workspace's
duality project, for the concrete manifold `ℂP²` of `Submission/Work/Projective/CP2Concrete.lean`.

It is the finite-coordinate-cover assembly `Work.Projective.pd_good_univ_local` applied to the
fundamental-class condition `Work.Projective.cp2_hc`, with the empty case
`Work.Cohomology.good_empty`.  The gluing step used by the assembly is specialised to
intersections lying in a single chart, where its supplementary vanishing input is the clean
`Work.Cohomology.chart_relCohomology_vanishing_of_compact`
(`Work.Projective.glue_chart`). -/
theorem cp2_good_univ_uncond :
    Work.Cohomology.Good 4 cp2C (Set.univ : Set (CPSpace 2)) isOpen_univ := by
  haveI : ChartedSpace (EuclideanSpace ℝ (Fin 4)) ↥(CPSpace 2) := instChartedSpaceEuclidean 2
  exact pd_good_univ_local cp2C cp2_hc (by norm_num) (Work.Cohomology.good_empty 4 cp2C)

/-- **The middle self-intersection of `ℂP²` is `±1`**, unconditionally.

`cp2SelfIntersection = ⟨h ⌣ h, [ℂP²]⟩` with `h` a generator of `H²(ℂP²;ℤ) ≅ ℤ` (`cp2H_span`)
and `[ℂP²]` a generator of `H₄(ℂP²;ℤ) ≅ ℤ` (`cp2C_span`): Poincaré duality in the middle degree
makes the intersection form on `H²(ℂP²;ℤ) = ℤ⟨h⟩` the `1 × 1` form `(m)` with
`m = cp2SelfIntersection`, which is unimodular, so `m = ±1`.

The argument is the perfect-pairing one of `Work.Projective.cp2SelfIntersection_pm_one_of_good`:
the Kronecker pairing `H² → Hom(H₂,ℤ)` is bijective (`cfkronH_two_cp2_bijective`, the homology of
`ℂP²` is free) and the cap product with the fundamental class is bijective by Poincaré duality.
The duality input `Work.Cohomology.Good 4 cp2C Set.univ` for the concrete manifold `ℂP²` is
`Work.Projective.cp2_good_univ_uncond`, assembled from the chart-local gluing step
`Work.Projective.glue_chart` (surjectivity from `pd_union_hit`, injectivity from
`pd_union_kill_chart` with the high-degree vanishing supplied by
`chart_relCohomology_vanishing_of_compact`), the fundamental-class condition
`Work.Projective.cp2_hc`, and the finite-coordinate-cover assembly
`Work.Projective.pd_good_univ_local`. -/
theorem cp2SelfIntersection_pm_one_uncond :
    Work.Projective.cp2SelfIntersection = 1 ∨ Work.Projective.cp2SelfIntersection = -1 :=
  cp2SelfIntersection_pm_one_of_good cp2_good_univ_uncond

end Work.Projective
