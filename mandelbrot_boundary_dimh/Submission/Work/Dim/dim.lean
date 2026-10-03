import Mathlib
import Submission.Work.Interfaces.Basic
import Submission.Work.Dim.Main
import Submission.Work.Dim.BallEstimates
import Submission.Work.Dim.Koebe.discBounds
import Submission.Work.Dim.DimPrinciple

/-!
# Dimension of the limit set of a conformal IFS (area DIM)

`Work.Dim.dim`: for a conformal IFS `τ : Fin N → ℂ → ℂ` on the ball `ball p r` (univalent branches
mapping `ball p r` into `ball p (r/2)` with disjoint images and derivative modulus at least
`K⁻¹` on `ball p (r/2)`), the Hausdorff dimension of every cylinder of the coding map is at least
`log N / log K`.

The proof is assembled in `Work.Dim.Main.dim_of_inputs` from:

* `Work.Dim.Branch.derivBound` — the uniform contraction `θ < 1` of the branches on
  `closedBall p (r/2)` (Schwarz–Pick);
* the Koebe-type estimates with universal constants: on the unit disc (`Work.Dim.Koebe.discBounds`)
  and rescaled to a general disc (`Work.Dim.ballBounds'`);
* the coding map theory `Work.Dim.Coding.map` (convergence, continuity, membership in pieces);
* the Moran antichain, the packing count `Work.Dim.Packing.packing` and the Frostman bound
  (`Work.Dim.Main.frostman_bound`);
* the Bernoulli measure `Work.Dim.Code.measure` and the mass-distribution principle
  `Work.Dim.le_dimH_of_frostman`.
-/

open MandelDim

namespace Work.Dim

theorem dim : DimStatement :=
  dim_of_inputs Koebe.discBounds
    (fun Cup Clow hCup hClow hdisc => ballBounds' Cup Clow hCup hClow hdisc)
    (fun {_s _d} hd μ hμ hbound => le_dimH_of_frostman hd μ hμ hbound)

end Work.Dim
