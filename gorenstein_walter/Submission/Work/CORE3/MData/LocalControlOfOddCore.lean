import Mathlib
import Submission.Work.CORE3.Defs
import Submission.Work.CORE3.MDataAux
import Submission.Work.CORE3.MDataLocalControlOddCore

namespace Work.CORE3.MData

/-! Bender 1981 §3, p. 223: the local-control clause of the §3a `M`-analysis in the form
Bender states it, `N_G(X) ≤ M` for `1 ≠ X ≤ O(M)`.  Proved in
`Submission/Work/CORE3/MDataLocalControlOddCore.lean` (route: `O(M)` centralizes `E(M)`,
then Lemma 2.9 at `N_G(X)` and the maximality of `M`). -/

theorem LocalControlOfOddCore (I : Work.CORE3.Case1Inputs) (hSetup : Work.GW2.Case1aSetupProp)
    (hFr : Work.GW2.Case1aFrattiniProp) (hAb : Work.GW2.Case1aAbelianProp)
    (hA7 : Work.GW2.Case1aA7Prop) :
    ∀ (G : Type) [Group G] [Finite G], Work.GW2.FeitThompsonProp → Work.GW2.BenderCtx G →
      ∀ B : Work.GW2.BenderSetup G, Work.GW2.Case1 B → B.Hhat = B.H →
      ∀ D : Work.GW2.Case1aData B, ∀ P2 M : Subgroup G,
      P2 ≤ B.U ⊓ Subgroup.centralizer ((B.S : Subgroup G) : Set G) → IsPGroup D.p P2 →
      ¬ D.p ∣ P2.relIndex (B.U ⊓ Subgroup.centralizer ((B.S : Subgroup G) : Set G)) →
      IsCoatom M → Subgroup.normalizer (P2 : Set G) ≤ M →
      ∀ X : Subgroup G, X ≠ ⊥ → X ≤ Work.GW2.oddCoreIn M →
        Subgroup.normalizer (X : Set G) ≤ M :=
  Work.CORE3.MDataLocalControlOddCore I hSetup hFr hAb hA7

end Work.CORE3.MData
