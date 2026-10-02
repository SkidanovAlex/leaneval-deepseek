import Mathlib
import Submission.Work.RatHurewicz.trackSetup
import Submission.Work.RatHurewicz.RelHomotopy
import Submission.Work.RatHurewicz.trackFibreHomeo
import Submission.Work.RatHurewicz.ConnectivityBridge
import Submission.Work.RatHurewicz.subsingleton_zerothHomotopy_of_homotopyEquiv
import Submission.Work.Serre.pathConnectedSpace_homotopyFibre

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The fibre of the mapping track is path connected

`Work.RatHurewicz.trackSetup` introduces the mapping track `Track inc` of `inc : X → Z` with its
"track fibration" `trackMap inc : Track inc → Z`, `(x, γ) ↦ γ 0`, and its fibre
`trackFibre inc (inc x₀)` over `inc x₀` (the pairs `(x, γ)` with `γ` a path from `inc x₀` to `inc x`).

`Work.RatHurewicz.trackFibreHomeo` identifies this fibre with the homotopy fibre
`homotopyFibre inc x₀` of `inc` by a homeomorphism fixing base points.  Hence, if the *homotopy*
fibre is path connected — which is exactly the statement that its zeroth homotopy group (in the
cube model `HomotopyGroup (Fin 0)`) is a subsingleton — then the *track* fibre is path connected,
being a continuous image of a path connected space.
-/

namespace Work.RatHurewicz

open scoped Topology

noncomputable section

/-- **The fibre of the mapping track of `inc` over `inc x₀` is path connected**, provided the
homotopy fibre `homotopyFibre inc x₀` has trivial `π₀` (stated in the cube model as
`Subsingleton (HomotopyGroup (Fin 0) _ _)`).

The proof is a transport along the base-point preserving homeomorphism
`Work.RatHurewicz.trackFibreHomeo`: cube-based `π₀`-triviality of the homotopy fibre gives
`PathConnectedSpace (homotopyFibre inc x₀)`
(`Work.RatHurewicz.pathConnectedSpace_of_subsingleton_pi_zero`), and path connectedness is
preserved by a surjective continuous map, here the homeomorphism. -/
theorem trackFibre_pathConnected {X Z : Type} [TopologicalSpace X] [TopologicalSpace Z]
    (inc : C(X, Z)) (x₀ : X)
    (hconn0 : Subsingleton (HomotopyGroup (Fin 0)
      (Work.RatHurewicz.homotopyFibre inc x₀)
      (Work.RatHurewicz.homotopyFibreBasepoint inc x₀))) :
    PathConnectedSpace (↥(Work.RatHurewicz.trackFibre inc (inc x₀))) := by
  haveI : PathConnectedSpace (Work.RatHurewicz.homotopyFibre inc x₀) :=
    Work.RatHurewicz.pathConnectedSpace_of_subsingleton_pi_zero _ hconn0
  obtain ⟨e, -, -⟩ := Work.RatHurewicz.trackFibreHomeo inc x₀
  exact e.surjective.pathConnectedSpace e.continuous

end

end Work.RatHurewicz
