import Mathlib
import Submission.Work.CORE4.Defs
import Submission.Work.CORE4.API
import Submission.Work.CORE4.Case2Numeric
import Submission.Work.CORE4.Case2SevenCentralizer
import Submission.Work.CORE4.Case2SevenRemainingOfCtx
import Submission.Work.CORE4.Case2PrePlusOfCtx

namespace Work.CORE4

open Subgroup

variable {G : Type} [Group G] [Finite G]

/-- **Bender 1981, §4 (7) at the `Case2Ctx` level.**  For the §4 configuration `h : Case2Ctx B`
the seven-facts bundle `Case2SevenFacts B h.D` holds unconditionally:

* `O₂(H ⊓ M) = O₂(H)` (`SevenO2HM`);
* `π(K₀) = π(F(U))`: the inclusion `⊆` is `Case2SevenRemainingOfCtx`, the reverse one is Bender's
  `X`-argument `SevenX.piFU_le_pi_K0F` together with Bender's (6)-witness
  (`exists_witness_of_case2ctx6` + `SevenX.piF_le_pi_K0_of_witness` + `conj2_iff_piF`);
* `π(U ⊓ C_G(K₀F)) = π(F(U))` is `Case2SevenCentralizer`;
* `π(K) ⊆ π(F(U))` and `π(F(M)) ⊆ π(F(U))` are `Case2SevenRemainingOfCtx`;
* `π⁅S ⊓ M, B₀⁆ ⊆ π(F(U))` is trivial because Bender's (2) (`Case2PrePlusOfCtx`) gives
  `B₀ ≤ C_G(S ⊓ E(M)) = C_G(S ⊓ M)`.

The assembly is `Case2SevenFacts_of_pieces` (`Case2Numeric.lean`), fed with
`Case2SevenRemainingOfCtx` (whose hypothesis is the centralizer conjunct, supplied by
`Case2SevenCentralizer`) and `Case2PrePlusOfCtx`. -/
theorem Case2SevenFacts_of_ctx (I : Work.GW2.C4Inputs) :
    ∀ (G : Type) [Group G] [Finite G], Work.GW2.BenderCtx G →
      ∀ (B : Work.GW2.BenderSetup G) (h : Work.GW2.Case2Ctx B),
        Work.GW2.Case2SevenFacts B h.D := by
  intro G _ _ hbc B h
  have hpre : Work.GW2.Case2PrePlus B h.D := Work.CORE4.Case2PrePlusOfCtx G I hbc B h
  have hC : Work.GW2.primesOf (B.U ⊓ Subgroup.centralizer
      (((Work.GW2.Case2Data.K0 h.D ⊔ h.D.F : Subgroup G)) : Set G)) = B.piFU :=
    Work.CORE4.Case2SevenCentralizer I G hbc B (Work.CORE4.Case2Ctx.toCtx6 h)
      (Work.CORE4.Case2Ctx.toCase2 h) hpre
  have hRem := Work.CORE4.Case2SevenRemainingOfCtx I G hbc B h hC
  exact Work.CORE4.Case2SevenFacts_of_pieces I hbc h hRem

end Work.CORE4
