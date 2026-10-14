import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.H2W.AeProof.AeCutEnergyV2
import Submission.Work.FTS.EllipticEst.Honest.HR2.HonToAe
import Submission.Work.FTS.EllipticEst.Honest.Step1G.AeClear.AeEnergyExpl
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.EllipticEst.interpol_trunc_defs
import Submission.Work.FTS.LocData.ZfarFstar.ZFBase
import Submission.Work.FTS.LocDataExt.Defs
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.Spaces.SmoothStripDefs
import Submission.Work.Spaces.mixed_mul_le
import Submission.Work.Spaces.pz_DthIter_mul_eq
-- ===== merged: Submission.Work.FTS.EllipticEst.H2W.AeProof.AeEnergyExpl =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end
noncomputable section
open scoped Real Topology BigOperators ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.H2W.AeProof
set_option autoImplicit false
set_option linter.unusedVariables false

end Work.FTS.EllipticEst.H2W.AeProof

namespace Work.FTS.EllipticEst.H2W.AeProof
set_option autoImplicit false
set_option linter.unusedVariables false

end Work.FTS.EllipticEst.H2W.AeProof

namespace Work.FTS.EllipticEst.H2W.AeProof
set_option autoImplicit false
set_option linter.unusedVariables false

end Work.FTS.EllipticEst.H2W.AeProof

namespace Work.FTS.EllipticEst.H2W.AeProof
set_option autoImplicit false
set_option linter.unusedVariables false

end Work.FTS.EllipticEst.H2W.AeProof

namespace Work.FTS.EllipticEst.H2W.AeProof
set_option autoImplicit false
set_option linter.unusedVariables false

end Work.FTS.EllipticEst.H2W.AeProof

namespace Work.FTS.EllipticEst.H2W.AeProof
set_option autoImplicit false
set_option linter.unusedVariables false

end Work.FTS.EllipticEst.H2W.AeProof

namespace Work.FTS.EllipticEst.H2W.AeProof
set_option autoImplicit false
set_option linter.unusedVariables false

end Work.FTS.EllipticEst.H2W.AeProof
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Honest.Step1G.EnergyG =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Honest.Step1G

/-!
# `EnergyG` — the honest `w²`-weighted energy inequality (Step 1 of `prop:H2`)

This is Elgindi's Step 1 in the honest class `Hon` (smooth on the *open* quadrant only, with
`HkMem α 0` of `F`, `z²∂_zzΨ`, `∂_θθΨ`).  The statement below is byte-identical to the sibling
`Work.FTS.EllipticEst.Honest.HonEnergyExpl` (which still carries a `sorry`).

**Full design, constant bookkeeping, available pieces and the remaining crux are written up in
`Submission/Work/FTS/EllipticEst/Honest/Step1G/NOTES_EnergyG.md` — read that first.**

Sketch.  For `φ ∈ C_c^∞((0,∞))` (`φ ≥ 0`, `φ ≤ 1`, `φ ↑ 1`) and `η ∈ C_c^∞((0,π/2))`
(`η ≥ 0`, `η ≤ 1`, `η ↑ 1`), the truncated identity (`Step1G/TruncIdentityHon`, a pure
integration by parts, delegated) reads

`∫_z φ w² ∫_θ (bslOp α Ψ)(ηΨ)`
`  = α² ∫_z φ w² z² ∫_θ η (∂_zΨ)² - (α²/2) ∫_z (φ w² z²)'' ∫_θ ηΨ²`
`    + (α(5+α)/2) ∫_z (φ w² z)' ∫_θ ηΨ²`
`    + ∫_z φ w² [∫_θ η(∂_θΨ)² + (1/2)∫_θ η(Ψ/cos)² - 6∫_θ ηΨ²`
`                 + ∫_θ η'(Ψ_θΨ - (1/2)tanθΨ²)]`.

Using `(Ψ/cos)² = Ψ²(1 + tan²θ)` and `∫η'Ψ_θΨ = -(1/2)∫η''Ψ²` this becomes

`LHS_{φ,η} = TF + (α²/2)∫(φw²z²)''A_η - (α(5+α)/2)∫(φw²z)'A_η + (11/2)∫φw²A_η`
`            + (1/2)∫_z φ w² ∫_θ [η'' - η tan²θ + η' tanθ]Ψ²`

(`A_η = ∫_θ ηΨ²`), and with `|(z²w²)''| ≤ 6w²`, `(z w²)' ≥ -3w²` (`weightTransferBounds`, proved),
`TF ≤ (1/2)(HkSq α 0 F + ∫∫φw²ηΨ²)` and `A_η ≤ A` one gets exactly the target constant
`13/2 + 3α² + (3/2)α(5+α)` — with **no room to spare**.

Case 1: `P := ∫⁻_z w² ∫⁻_θ ofReal(Ψ²) = ⊤` makes the right-hand side `⊤`.
Case 2 (`P < ⊤`, so `∫_z w²A < ∞` by `Honest/HonEnergyData`, proved): the left-hand side is the
monotone limit of `LHS_{φ,η}` as `φ ↑ 1`, `η ↑ 1`; the cut-off layer errors are `≤ C∫_{layers}w²A`
which `→ 0`, and the last display's bracket integral must be shown `≤ o(1)` (see the notes: this is
the one remaining analytic crux, handled by a `C^∞` cut-off with a controlled profile together with
the a.e. left-endpoint vanishing and the slice Lipschitz bound).
-/


end Work.FTS.EllipticEst.Honest.Step1G
end
