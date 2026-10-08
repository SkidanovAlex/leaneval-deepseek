import Mathlib
import Submission.Work.CORE3.Defs
import Submission.Work.CORE3.MDataAux
import Submission.Work.CORE3.Core18BcLeM
import Submission.Work.CORE3.MData.BcInfMLeOddCore
import Submission.Work.CORE3.MData.LocalControlOfOddCore

namespace Work.CORE3.MData

/-! Bender 1981 §3, p. 223: `B = C_U(S) ≤ M` in the §3a `M`-analysis.  No cycle: the
local-control clause is used in Bender's own form (`1 ≠ X ⊆ B ∩ M`, i.e. `X ≤ O(M)`), and
the argument is Bender's own order (design pass 18 §B):

1. `B ∩ M = O(M)` (`MData.BcInfMLeOddCore`);
2. local control for `1 ≠ X ≤ O(M)` (`MData.LocalControlOfOddCore`);
3. `P = O_p(U) ≤ M` (`Work.CORE3.Core18PcoreLeM`, from 1+2);
4. `B` normalizes `X' = (P ⊔ P^n) ∩ B ≠ ⊥` (`Work.CORE3.Core18BcNormalizesInf`, `n ∈ N_G(V₁)`);
5. `B ≤ N_G(X') ≤ M` (`Core18BcLeM`). -/

theorem BcLeM (I : Work.CORE3.Case1Inputs) (hSetup : Work.GW2.Case1aSetupProp)
    (hFr : Work.GW2.Case1aFrattiniProp) (hAb : Work.GW2.Case1aAbelianProp)
    (hA7 : Work.GW2.Case1aA7Prop) :
    ∀ (G : Type) [Group G] [Finite G], Work.GW2.FeitThompsonProp → Work.GW2.BenderCtx G →
      ∀ B : Work.GW2.BenderSetup G, Work.GW2.Case1 B → B.Hhat = B.H →
      ∀ D : Work.GW2.Case1aData B, ∀ P2 M : Subgroup G,
      P2 ≤ B.U ⊓ Subgroup.centralizer ((B.S : Subgroup G) : Set G) → IsPGroup D.p P2 →
      ¬ D.p ∣ P2.relIndex (B.U ⊓ Subgroup.centralizer ((B.S : Subgroup G) : Set G)) →
      IsCoatom M → Subgroup.normalizer (P2 : Set G) ≤ M →
      B.U ⊓ Subgroup.centralizer ((B.S : Subgroup G) : Set G) ≤ M := by
  intro G _instG _finG hFT hCtx B hCase hHhat D P2 M hP2le hP2grp hP2ndvd hMcoat hNM
  exact Work.CORE3.Core18BcLeM G I hAb hFT hCtx B hCase hHhat D P2 M hP2le hP2grp hP2ndvd
    hMcoat hNM
    (Work.CORE3.MData.BcInfMLeOddCore I hSetup hFr hAb hA7 G hFT hCtx B hCase hHhat D P2 M
      hP2le hP2grp hP2ndvd hMcoat hNM)
    (Work.CORE3.MData.LocalControlOfOddCore I hSetup hFr hAb hA7 G hFT hCtx B hCase hHhat D P2 M
      hP2le hP2grp hP2ndvd hMcoat hNM)

end Work.CORE3.MData
