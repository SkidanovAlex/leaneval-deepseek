import Mathlib
import Submission.Work.CORE3.Defs
import Submission.Work.CORE3.CosetInvCountLeSix
import Submission.Work.CORE3.CentralizerPcoreEqVU
import Submission.Work.BSW.Cases.K4.CardSup
import Submission.Work.CORE3.Case1bDiv
import Submission.Work.CORE3.FreeAux.CardHhat72

/-!
# Bender 1981 §3, subcase `(1b)`: `|O₂(Ĥ)·O(H)| = 12` and `|Ĥ| = 72`

In Bender's §3 subcase `(1b)` (`V = O₂(Ĥ)` is a four-group), Bender's Theorem 2.6 gives
`Ĥ/V·U ≅ D₃` (`[Ĥ : V ⊔ U] = 6`), and `|V| = 4`.  Hence, once `|U| = 3` is known (the input
`hU3` here), the arithmetic of the §3 count gives

* `|V ⊔ U| = |V| · |U| = 12`  (`V ⊓ U = 1`, `U` normalises `V`),
* `|Ĥ| = 36 · |U| / ... ` more precisely `|Ĥ| = 12 · 6 = 72`  (`|H| = |U|·|S| = 24`,
  `[Ĥ : H] = 3`; see `Work.CORE3.FreeAux.CardHhat72`).

Both ingredients are already available, so this module is the assembly:

* `Work.CORE3.card_VU` (`V ⊓ U = 1`, `U ≤ N(V)`) gives `|V ⊔ U| = |V| · |U|` from Theorem 2.6's
  `S ⊓ C_G(U) = V`;
* `Work.CORE3.FreeAux.CardHhat72` gives `|Ĥ| = 72` from `|U| = 3`.
-/

namespace Work.CORE3

theorem VUCardTwelve (G : Type) [Group G] [Finite G] (I : Work.CORE3.Case1Inputs)
    (hBc : Work.GW2.BenderCtx G) (B : Work.GW2.BenderSetup G) (h1 : Work.GW2.Case1 B)
    (D : Work.GW2.Case1bData B) (hU3 : Nat.card B.U = 3) :
    Nat.card ↥(Work.GW2.pCoreIn 2 B.Hhat ⊔ B.U) = 12 ∧ Nat.card B.Hhat = 72 := by
  refine ⟨?_, Work.CORE3.FreeAux.CardHhat72 G I hBc B h1 D hU3⟩
  -- Theorem 2.6: `S ⊓ C_G(U) = O₂(Ĥ)`
  have h26 : (B.S : Subgroup G) ⊓ Subgroup.centralizer (B.U : Set G)
      = Work.GW2.pCoreIn 2 B.Hhat := (I.h26 G I.T.ft hBc B).2.1
  -- `|V ⊔ U| = |V| · |U|`, `|V| = 4` (`V` is a four-group), `|U| = 3`.
  rw [Work.CORE3.card_VU B h26, D.four.1, hU3]

end Work.CORE3
