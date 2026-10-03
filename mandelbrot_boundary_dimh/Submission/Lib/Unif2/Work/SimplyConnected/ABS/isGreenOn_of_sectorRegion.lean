import Mathlib
import Submission.Lib.Unif2.Work.SimplyConnected.ABS.Defs
import Submission.Lib.Unif2.Work.SimplyConnected.ABS.RegularPieceDefs
import Submission.Lib.Unif2.Work.SimplyConnected.ABS.barrier_of_sector
import Submission.Lib.Unif2.Work.SimplyConnected.Perron.greenOn

/-!
# The Green function of a relatively compact region with sector boundary

`Work.SimplyConnected.ABS.HasSectorBoundary W p` is the cone condition at a frontier point `p` of the
region `W`: in a chart at `p`, `W` avoids a non-degenerate sector with apex `p`.  By
`barrier_of_sector` this cone condition produces, at every frontier point, a *barrier* in the sense
of the Dirichlet problem (a function which is superharmonic on `W` near `p`, positive there,
continuous on a neighbourhood of `p` and vanishes at `p`).

`Work.SimplyConnected.Perron.exists_isGreenOn_of_barriers_final` is the sweep (balayage)
construction: a barrier at every frontier point of a relatively compact, connected, non-total open
region `W` of a Riemann surface yields the Green function of `W` with pole `x₀ ∈ W`, in the ambient
form `Work.SimplyConnected.ABS.IsGreenOn`.

This module assembles the two: every relatively compact connected non-total open region of a Riemann
surface with the cone condition at each of its frontier points has a Green function.

The only topological input is `p ∉ W` for `p ∈ frontier W`, which holds because `W` is open:
`frontier W = closure W \ interior W` and `interior W = W`.
-/

open LeanEval.Geometry
open scoped Manifold ContDiff Topology

set_option linter.unusedSectionVars false

noncomputable section

open Filter Set
open Classical

namespace Work.SimplyConnected.ABS

theorem isGreenOn_of_sectorRegion {X : Type*} [TopologicalSpace X] [T2Space X]
    [ConnectedSpace X] [SecondCountableTopology X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
    {W : Set X} (hWo : IsOpen W) (hWc : IsConnected W) (hWne : W ≠ Set.univ)
    (hcomp : IsCompact (closure W)) {x₀ : X} (hx₀ : x₀ ∈ W)
    (hsect : ∀ p ∈ frontier W, Work.SimplyConnected.ABS.HasSectorBoundary W p) :
    ∃ E : X → ℝ, Work.SimplyConnected.ABS.IsGreenOn W x₀ E := by
  refine Work.SimplyConnected.Perron.exists_isGreenOn_of_barriers_final (X := X)
    hWo hWc hWne hcomp hx₀ ?_
  intro p hp
  -- a frontier point of the open set `W` is not in `W`
  have hpi : p ∉ interior W := hp.2
  have hpW : p ∉ W := by rwa [hWo.interior_eq] at hpi
  exact barrier_of_sector (X := X) hWo hpW (hsect p hp)

end Work.SimplyConnected.ABS
