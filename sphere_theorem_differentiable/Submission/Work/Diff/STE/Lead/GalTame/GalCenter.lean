import Mathlib
import Submission.Work.Diff.STE.Torus
import Submission.Work.Diff.STE.B3.Comp

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The centred cube and the `Hᵐ` energy over it

The B3 layer measures the `Hᵐ` energy `Work.Diff.STE.ENormSq m f` as a sum of integrals over the
half open unit cube `(0,1]^ι`.  The localised chart components, however, are supported in a small
ball around the *origin* of the flat coordinate, i.e. they straddle the boundary of `(0,1]^ι`, and
the natural domain for them is the *centred* cube `(-1/2,1/2]^ι` (which is the fundamental domain
on which `Work.Diff.STE.B3Data.centreCube` lives, and which contains the ball of radius `1/2`).

This module fixes the vocabulary for the centred-cube energy so that the tame estimates for the
chart data and for the residual of the transport identity can be stated on the centred cube:

* `Work.Diff.STE.Lead.GalTame.cubeC ι` — the centred cube `(-1/2,1/2]^ι`;
* `Work.Diff.STE.Lead.GalTame.CENormSq m f` — `Σ_{l : Fin m → ι} ∫_{cubeC} ‖∂^l f‖²`, the
  `Hᵐ` energy of `f` over the centred cube.
-/

namespace Work.Diff.STE.Lead.GalTame

noncomputable section

open scoped BigOperators

/-- The centred half open cube `(-1/2,1/2]^ι`: the fundamental domain which contains the ball of
radius `1/2`, hence the supports of all the localised chart data (whose support lies in a ball of
radius `< 1/2` around the origin of the flat coordinate). -/
def cubeC (ι : Type*) : Set (ι → ℝ) :=
  Set.pi Set.univ (fun _ : ι => Set.Ioc (-(1 / 2 : ℝ)) (1 / 2))

/-- **The `Hᵐ` energy over the centred cube**: `Σ_{l : Fin m → ι} ∫_{cubeC} ‖∂^l f‖²`.  This is
`Work.Diff.STE.ENormSq m f` with the unit cube replaced by the centred cube `cubeC`; for a function
whose support lies in the ball of radius `1/2` around the origin (in particular for any chart
function supported in a `2σ`-ball, `2σ ≤ 1/4`) the two integrals agree, since both cubes are
fundamental domains of the lattice action and the function vanishes on a neighbourhood of the
difference set. -/
def CENormSq {ι : Type*} [Fintype ι] [DecidableEq ι] (m : ℕ) (f : (ι → ℝ) → ℂ) : ℝ :=
  ∑ l : Fin m → ι, ∫ z in cubeC ι, ‖Work.Diff.STE.pdVec m l f z‖ ^ 2

end

end Work.Diff.STE.Lead.GalTame
