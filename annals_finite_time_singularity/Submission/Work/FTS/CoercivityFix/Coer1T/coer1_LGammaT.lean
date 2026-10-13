/-
# `Coer1T/coer1_LGammaT` — the level-1 coercivity of `𝓛_Γ^T` in the interior class

The paper's Corollary `FirstDerivativeCoercivity` (Elgindi, Annals 194 (3) 2021) in the
class `CoerAdm` of the route: `HkSq α 1 f ≤ H1IP α (𝓛_Γ^T f) f`.

The proof is the arithmetic ledger of `SlotsDzGam.lean`, fed with the four §6 slot
estimates for `𝓛_Γ^T` in the interior class (`slotDz_LGammaT`, `slotEta_LGammaT`,
`slotW_LGammaT`, `slotGam_LGammaT`, in the sibling files of this directory) and the three
auxiliary inputs (`hardyHyp_of_coerAdm`, `gammaL2Bnd_fts`, `gammaPointwiseBnd_fts`).

See `NOTES_coer1_LGammaT.md` for the route.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Basic.Real.Basic
import Mathlib.Order.Filter.Defs
import Mathlib.Tactic.NormNum.Ineq
import Submission.Work.FTS.CoercivityFix.Basic
import Submission.Work.FTS.Vocab
import Submission.Work.Coercivity.zAux
import Submission.Work.Coercivity.thetaAux
import Submission.Work.Coercivity.C0_sq_le4
import Submission.Work.Coercivity.EL12z_Kd
import Submission.Work.Coercivity.L2CoercivityTransport
import Submission.Work.FTS.CoercivityFix.Coer1.Defs
import Submission.Work.FTS.CoercivityFix.Coer1.zIBP
import Submission.Work.FTS.CoercivityFix.Coer1.thetaIBP
import Submission.Work.FTS.CoercivityFix.Coer1.IntFacts
import Submission.Work.FTS.CoercivityFix.Coer1.Estimates
import Submission.Work.FTS.CoercivityFix.LhatCalc.Dz_Lhat
import Submission.Work.FTS.CoercivityFix.LhatCalc.Dth_Lhat
import Submission.Work.FTS.GalerkinFix.RegQ.regQ_mono
import Submission.Work.FTS.LocData.SmoothChain
import Submission.Work.FTS.CoercivityFix.Coer1T.SlotsDzGam
import Submission.Work.FTS.CoercivityFix.Coer1T.gammaPointwiseBnd_fts
import Submission.Work.FTS.CoercivityFix.Coer1T.gammaL2Bnd_fts
import Submission.Work.FTS.CoercivityFix.Coer1T.hardyHyp_of_coerAdm
import Submission.Work.FTS.CoercivityFix.Coer1T.slotDz_LGammaT
import Submission.Work.FTS.CoercivityFix.Coer1T.slotEta_LGammaT
import Submission.Work.FTS.CoercivityFix.Coer1T.slotW_LGammaT
import Submission.Work.FTS.CoercivityFix.Coer1T.slotGam_LGammaT

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityFix.Coer1T

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-- **The level-1 coercivity of `𝓛_Γ^T` in the interior class `CoerAdm`** (the paper's
Corollary `FirstDerivativeCoercivity`):
`|f|²_{ℋ¹} ≤ (𝓛_Γ^T f, f)_{ℋ¹}` for `α ≤ 10⁻¹⁴` and `f ∈ CoerAdm α`. -/
theorem coer1_LGammaT (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1 / 10 ^ 14) {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.Nonlin.CoerAdm α f) :
    Work.Spaces.HkSq α 1 f ≤ Work.Coercivity.H1IP α (Work.Coercivity.LGammaT α f) f := by
  have hreg2 : Work.FTS.Nonlin.RegQ α 2 f :=
    Work.FTS.GalerkinFix.RegQ.regQ_mono hf.reg (by norm_num)
  have hreg1 : Work.FTS.Nonlin.RegQ α 1 f :=
    Work.FTS.GalerkinFix.RegQ.regQ_mono hf.reg (by norm_num)
  have hsq : Work.FTS.LocData.SmoothQuad f := hf.reg.1
  have hm2 : Work.Spaces.HkMem α 2 f := hreg2.2.1
  have hm1 : Work.Spaces.HkMem α 1 f := hreg1.2.1
  have hHH : Work.Coercivity.HardyHyp f := hardyHyp_of_coerAdm α hα hα1 hf
  have hG : Work.Coercivity.GammaL2Bnd α := gammaL2Bnd_fts α hα hα1
  have hG2 : Work.Coercivity.GammaPointwiseBnd α := gammaPointwiseBnd_fts α hα
  exact ledger α hα hα1 hsq hm1 (EDthW_le_EDth_Q α hα hsq hm2)
    (EL12z_le_Q α hα hsq hm2 hHH)
    (slotDz_LGammaT α hα hα1 hf hHH)
    (slotEta_LGammaT α hα hα1 hf hHH hG)
    (slotW_LGammaT α hα hα1 hf hHH hG)
    (slotGam_LGammaT α hα hα1 hf hHH hG2)

end Work.FTS.CoercivityFix.Coer1T
