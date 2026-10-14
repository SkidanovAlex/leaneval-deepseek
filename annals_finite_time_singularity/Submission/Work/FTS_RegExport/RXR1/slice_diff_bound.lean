import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.FinalV2.Defs
import Submission.Work.FTS.PhiStar.Honesty.SlotsLimit.integrableOn_term
import Submission.Work.FTS.StrongEps.EpsE4Thr.regQo_const_mul
import Submission.Work.FTS.StrongEps.LocUnif.mixed_partials_of_smoothOpen
import Submission.Work.FTS.StrongEps.SupPort.classC_sup_le
import Submission.Work.FTS_EllLimOK.LimExtract_bounds
import Submission.Work.FTS_EllLimOK.tower_jet_identities
import Submission.Work.FTS_RegExport.C4.Dth_mixed_eq_C4
import Submission.Work.R1G.DecayInZ_gA
import Submission.Work.Spaces.one_le_mul_w

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_RegExport.RXR1.slice_diff_bound`

The `τ`-Lipschitz modulus of the order-`≤ 2` mixed jets of the slices of the strong solution
`g` of the fake-time equation (the "difference" half of the consistency statement RX-A2):

`|D_z^b D_θ^a (g(·,·,τ) - g(·,·,τ'))(z,θ)| ≤ 10/√(γ-1) · L · |τ - τ'|`

for `a + b ≤ 2` and `(z,θ)` in the open quadrant, with `L` the `ℋ⁴`-Lipschitz modulus of the
class-C approximants supplied by `LimApprox`.

## The route

`LimApprox α C₀ Φs E g` provides a sequence `gn` of class-C families, uniformly in `ℋ⁶`, whose
`ℋ⁴`-differences are `L`-Lipschitz in `τ`, and whose mixed jets converge pointwise on the open
quadrant (`Qd = Q0`) to those of `g`.

1. For fixed `τ, τ'` the *difference* family `H n = slice (gn n) τ - slice (gn n) τ'` is
   `C^∞` on the open quadrant (`EComparison.classC_sub`), and `ZsqAux.mixed_sub_open` rewrites
   its jets as differences of the jets of the two class-C slices.  The class-C bound
   `classC_mixed_sup_le_four` (order `≤ 4`) then bounds the order-`≤ 3` jets of `H n`
   *uniformly in `n`, `z`, `θ`*; the identities `∂_z (mixed c d) = mixed (c+1) d / z`,
   `∂_θ (mixed c d) = mixed c (d+1) / sin 2θ` (`mixed_partials_of_smoothOpen`) make the
   order-`≤ 2` jets uniformly Lipschitz on every compact subset of the open quadrant, and
   `eqc_uniform` converts pointwise convergence + equicontinuity into
   `TendstoLocallyUniformlyOn`.
2. `LimTower_dz` turns the locally uniform convergence into the two tower relations
   `∂_z (F c d) = F (c+1) d / z`, `∂_θ (F c d) = F c (d+1) / sin 2θ` for the limit family
   `F c d := mixed c d (slice g τ) - mixed c d (slice g τ')`; `LimTower_identify` then
   identifies `F c d` with `mixed c d (F 0 0) = D_z^c D_θ^d (slice g τ - slice g τ')`.
3. The pointwise class-C bound `|mixed b a (H n) z θ| ≤ 10/√(γ-1) · ℋ⁴(H n)` (RX-A1 on the
   open class, `mixed_abs_le_of_smoothOpen`) together with the Lipschitz clause of `LimApprox`
   bounds `|F b a z θ|`; the bound passes to the limit (`le_of_tendsto'`).
-/

namespace Work.FTS_RegExport.RXR1

open Filter Set
open scoped Topology

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

/-! ## §1 Uniform convergence on compacta from pointwise convergence and equicontinuity -/


/-! ## §2 Locally uniform convergence of the jets of the approximant differences -/


/-! ## §3 The Lipschitz modulus of the slice differences -/


end

end Work.FTS_RegExport.RXR1
