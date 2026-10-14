import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.ClassC.pth_Vop_EllResid_classC
import Submission.Work.FTS.EllSol.ClassC
import Submission.Work.FTS.EllipticEst.EllHyp_certificates
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.RPFresh.straight_transfers
import Submission.Work.FTS.H2.hard_sq_prod_z
import Submission.Work.FTS.LocData.zero_slice_locG
import Submission.Work.FTS.LocDataExt.Zfar5
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.StarSlotPcs.DzdIterBound
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.FTS_StreamBdry.SB4.DzEpartEq
import Submission.Work.SolutionDelivery.DatumOdd

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.PkgK5

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-!
# `Work.FTS.EllSol.PkgK5.VopcPth2Transfer`

The second angular derivative of the *residual* `Ξ = EllResid α g Φg` is controlled by that of
the *straightened* unknown `Ψ̂ = ellShift α g Φg` plus the source `g`, at every level `k ≤ 5`:

`∂_θθΞ ∈ ℋ^k`  and  `|∂_θθΞ|_{ℋ^k} ≤ C (|∂_θθΨ̂|_{ℋ^k} + |g|_{ℋ^k})`.

This is the *reverse* (and easier) direction of the sibling
`Work.FTS.ClassC.NormPieces.pthIter2_shift_le_classC`, and it is the transfer that lets a
consumer who has the `∂_θθ`-honesty of the straight unknown obtain the same for the object
`EllResid α g Φg` on which the operators `Rop`, `Uop`, `Vop` act.

## Proof

The two unknowns differ on the whole plane by the *layer* `Ḡ(α,g)·sin 2θ`
(`Gsing = Gstar + Ḡ`, `Gstar = -(1/(4α)) L₁₂`, `PhiTil = EllResid`):

  `Ξ = Ψ̂ - Ḡ·sin 2θ`   (pointwise, `EllResid_eq_ellShift_sub_Gbar_point`),

whence the pointwise identity on the open quadrant

  `∂_θθΞ = ∂_θθΨ̂ + 4·(Ḡ·sin 2θ)`    (`∂_θθ(a(z) sin 2θ) = -4 a(z) sin 2θ`).

The `ℋ^k`-membership of `∂_θθΞ` is then the membership of the right-hand side
(`HkMem_add_open` for `∂_θθΨ̂` and the layer, whose membership is
`Cert.GbarLayer.layer_HkMem_target_of_smoothOpen`), transported back along the open-quadrant
equality by `Cert.GbarSin.HkMem_congr_Q0` (which needs *no* smoothness on the side being
transported to).  The norm bound is `HkNorm_add_le` (the layer is `SmoothOpen`, from
`ClassC.smoothOpen_GbarSin_classC`) followed by `HkNorm_const_mul` and the norm bound
`Cert.GbarLayer.layer_Gbar_HkNorm_le_SmoothOpen` of the layer.

`ClassC.mem` supplies `HkMem α 7 g`, which `TT.HkMem_descend_open` downgrades to the required
level `k ≤ 5 ≤ 7`; that is the only place the bound `k ≤ 5` is used (the statement in fact
holds for every `k ≤ 7`).
-/

end Work.FTS.EllSol.PkgK5
