import Mathlib
import Submission.Work.CORE3.Defs
import Submission.Work.CORE3.Case1bCount
import Submission.Work.CORE3.Case1bEightNineDefs
import Submission.Work.CORE3.VUInvSetTrivial
import Submission.Work.CORE3.CosetInvCountLeSix
import Submission.Work.CORE3.CosetInvCountNeFive
import Submission.Work.CORE3.CosetInvCountNeSixOf
import Submission.Work.CORE3.CosetInvCountNeSix
import Submission.Work.CORE3.BenderSevenU3
import Submission.Work.CORE3.Case1bSevenNeSix
import Submission.Work.CORE3.Case1bSevenInvInI
import Submission.Work.CORE3.CardInfConjSubOfThree
import Submission.Work.CORE3.CosetPairCountFour
import Submission.Work.CORE3.CommutingPairTallyCosets
import Submission.Work.CORE3.CommutingPairTallyCentralizers
import Submission.Work.CORE3.InvolutionCentralizerCount
import Submission.Work.CORE3.CommutingInvolsVsharp
import Submission.Work.CORE3.CommutingInvolsOutsideV

/-!
# `Work.CORE3.J4.Case1bSixEightClean`

The "clean" form of the first two conjuncts of Bender 1981 §3 (6)–(9)
(`Work.GW2.Case1bEightNineProp`):

* `bₙ = 0` for `n ≥ 5`;
* `3 b₄ + b₂ = 6 k²`, where `k = |K|`.

Unlike `Work.GW2.Case1bEightNineProp` the statement does not carry `FeitThompsonProp` — the
instance used is the one already packaged in the input bundle, `I.T.ft`.

The two conjuncts are obtained from the two halves of §3:

* **(6)/(9)(1):** `bₙ = 0` for `n ≥ 5` via `Work.CORE3.bCount_eq_zero_of_involution_bound`,
  which needs the pointwise bound `cosetInvCount Ĥ y ≤ 4`; the bound uses `≤ 6`
  (`Work.CORE3.cosetInvCount_le_six`), `≠ 5` (`Work.CORE3.CosetInvCountNeFive`) and `≠ 6`
  (`Work.CORE3.cosetInvCountNeSixClean` below);
* **(8):** the two tallies `2 b₂ + 6 b₄ = 12 k²` (`Work.CORE3.CommutingPairTallyCosets`,
  `Work.CORE3.CommutingPairTallyCentralizers`), using the involution identities
  `Work.CORE3.Case1bCount`.

The helper `cosetInvCountNeSixClean` is the reason for this file: the in-tree
`Work.CORE3.CosetInvCountNeSix` reaches `≠ 6` through `Work.CORE3.BenderSeven`, whose first
conjunct `|U| = 3` is still `sorry`-dependent (via `Work.CORE3.Case1bSeven`).  The route used
here avoids that: `Work.CORE3.cosetInvCount_ne_six_of` consumes only the *second* conjunct
`|Ĥ ⊓ Ĥ^y| = 6` of Bender (7), which we rebuild from the clean pieces
`Work.CORE3.BenderSixNeSixAuxS` (Bender (6), supplying Bender's `N_Ĥ(X)` witness `s`),
`Work.CORE3.BenderSevenU3` (`|U| = 3` from the witness `s`),
`Work.CORE3.Case1bSevenNeSix` / `Work.CORE3.Case1bSevenInvInI` (`n ≠ 6` and `n ≥ 4`) and
`Work.CORE3.card_inf_conjSubOfThree`.  All of these are `sorry`-free.
-/

namespace Work.CORE3.J4

open Work.GW2

/-- **Bender (6) + (7) ⟹ `n ≠ 6`, `sorry`-free form.**  Bender's `≠ 6` statement
(`Work.CORE3.CosetInvCountNeSix`), proved here without the `sorry`-dependent `|U| = 3` step by
feeding `Work.CORE3.cosetInvCount_ne_six_of` only the `D₆`-half of Bender (7). -/
theorem cosetInvCountNeSixClean {G : Type} [Group G] [Finite G] (I : Case1Inputs)
    (hBc : BenderCtx G) (B : BenderSetup G) (h1 : Case1 B) (D : Case1bData B) :
    ∀ y : G, orderOf y = 2 → y ∉ B.Hhat → cosetInvCount B.Hhat y ≠ 6 := by
  -- Bender (5): no involution outside `Ĥ` inverts a nontrivial element of `VU = O₂(Ĥ)·O(Ĥ)`.
  have h5 : ∀ z : G, orderOf z = 2 → z ∉ B.Hhat →
      invSet (pCoreIn 2 B.Hhat ⊔ B.U) z = {1} :=
    Work.CORE3.VUInvSetTrivial G I hBc B h1 D
  refine Work.CORE3.cosetInvCount_ne_six_of G I hBc B h1 D h5 ?_ ?_
  · -- Bender (6) in the strong form carrying the `N_Ĥ(X)`-witness `s`.
    intro y hy2 hyH hbig
    exact Work.CORE3.BenderSixNeSixAuxS G I hBc B h1 D h5 y hy2 hyH hbig
  · -- Bender (7): here only the `|Ĥ ⊓ Ĥ^y| = 6` half is consumed, and it is rebuilt from the
    -- clean inputs rather than from the `sorry`-dependent `Work.CORE3.BenderSeven`.
    intro y X hy2 hyH hXle hXne hXodd hinv hCeven hNeven s hsH hs2 hsX
    have hU3 : Nat.card B.U = 3 :=
      Work.CORE3.BenderSevenU3 G I hBc B h1 D hy2 hyH X hXle hXne hXodd hinv hCeven
        (s := s) hsH hs2 hsX
    refine ⟨hU3, ?_⟩
    have hle6 : cosetInvCount B.Hhat y ≤ 6 :=
      Work.CORE3.cosetInvCount_le_six G I hBc B h1 D h5 y hy2 hyH
    have hne5 : cosetInvCount B.Hhat y ≠ 5 :=
      Work.CORE3.CosetInvCountNeFive G I hBc B h1 D h5 y hy2 hyH
    have hne6 : cosetInvCount B.Hhat y ≠ 6 := by
      intro h6
      exact Work.CORE3.Case1bSevenNeSix G I hBc B h1 D hU3 hy2 hyH hXle hXne hXodd hinv
        hCeven h6
    have hge4 : 4 ≤ cosetInvCount B.Hhat y :=
      Work.CORE3.Case1bSevenInvInI G I hBc B h1 D hU3 hy2 hyH hXle hXne hXodd hinv hCeven
    have hy4 : cosetInvCount B.Hhat y = 4 := by omega
    exact Work.CORE3.card_inf_conjSubOfThree I hBc B h1 D hy2 hyH X hXle hXne hXodd hinv
      hCeven hNeven hU3 hy4

theorem Case1bSixEightClean {G : Type} [Group G] [Finite G] (I : Work.CORE3.Case1Inputs)
    (hBc : Work.GW2.BenderCtx G) (B : Work.GW2.BenderSetup G) (h1 : Work.GW2.Case1 B)
    (D : Work.GW2.Case1bData B) :
    (∀ n : ℕ, 5 ≤ n → Work.GW2.bCount B.Hhat n = 0) ∧
      3 * Work.GW2.bCount B.Hhat 4 + Work.GW2.bCount B.Hhat 2 = 6 * Nat.card D.K ^ 2 := by
  classical
  -- Bender (1)–(4): the involution identities of §3.
  have hCount : Case1bCountProp := Work.CORE3.Case1bCount I
  -- Bender (5).  Recorded here as `h5`; used by (6) and by the strong `≠ 6` result.
  have h5 : ∀ z : G, orderOf z = 2 → z ∉ B.Hhat →
      invSet (pCoreIn 2 B.Hhat ⊔ B.U) z = {1} :=
    Work.CORE3.VUInvSetTrivial G I hBc B h1 D
  -- Bender (6): at most four involutions per coset.
  have hA : ∀ y : G, orderOf y = 2 → y ∉ B.Hhat → cosetInvCount B.Hhat y ≤ 4 := by
    intro y hy2 hyH
    have h6 := Work.CORE3.cosetInvCount_le_six G I hBc B h1 D h5 y hy2 hyH
    have hne5 := Work.CORE3.CosetInvCountNeFive G I hBc B h1 D h5 y hy2 hyH
    have hne6 := cosetInvCountNeSixClean I hBc B h1 D y hy2 hyH
    omega
  -- Bender (7)/(8): a four-involution coset contributes six commuting pairs.
  have hB : ∀ y : G, orderOf y = 2 → y ∉ B.Hhat → cosetInvCount B.Hhat y = 4 →
      Work.CORE3.cosetPairCount B.Hhat y = 6 :=
    fun y hy hyH h4 => Work.CORE3.CosetPairCountFour G I hBc B h1 D y hy hyH h4
  -- The three structural inputs of the centralizer-side tally.
  have hCent : ∀ s : G, orderOf s = 2 →
      (involutionSet (⊤ : Subgroup G) ∩ Subgroup.centralizer ({s} : Set G)).ncard
        = 3 + 2 * Nat.card D.K :=
    fun s hs => Work.CORE3.InvolutionCentralizerCount G I hBc B h1 D s hs
  have hVsharp : ∀ s : G, s ∈ pCoreIn 2 B.Hhat → orderOf s = 2 →
      (involutionSet B.Hhat ∩ Subgroup.centralizer ({s} : Set G)).ncard
        = 3 + 2 * Nat.card D.K :=
    fun s hsV hs => Work.CORE3.CommutingInvolsVsharp G I hBc B h1 D s hsV hs
  have hOut : ∀ s : G, s ∈ B.Hhat → orderOf s = 2 → s ∉ pCoreIn 2 B.Hhat →
      (involutionSet B.Hhat ∩ Subgroup.centralizer ({s} : Set G)).ncard = 3 :=
    fun s hsH hs hsV => Work.CORE3.CommutingInvolsOutsideV G I hBc B h1 D s hsH hs hsV
  refine ⟨?_, ?_⟩
  · -- (9)/(1): `bₙ = 0` for `n ≥ 5`
    intro n hn
    exact Work.CORE3.bCount_eq_zero_of_involution_bound B.Hhat hA n hn
  · -- (8): `3 b₄ + b₂ = 6 k²`, by comparing the two tallies
    have hT1 := Work.CORE3.CommutingPairTallyCosets G I hBc B h1 D hA hB
    have hT2 := Work.CORE3.CommutingPairTallyCentralizers G I hBc B h1 D hCount hCent hVsharp
      hOut
    have hmain : 2 * bCount B.Hhat 2 + 6 * bCount B.Hhat 4 = 12 * Nat.card D.K ^ 2 :=
      hT1.symm.trans hT2
    have hmain' : 2 * (3 * bCount B.Hhat 4 + bCount B.Hhat 2) = 12 * Nat.card D.K ^ 2 := by
      rw [show 2 * (3 * bCount B.Hhat 4 + bCount B.Hhat 2)
          = 2 * bCount B.Hhat 2 + 6 * bCount B.Hhat 4 by ring]
      exact hmain
    have h2 : 12 * Nat.card D.K ^ 2 = 2 * (6 * Nat.card D.K ^ 2) := by ring
    exact Nat.mul_left_cancel (by norm_num : (0 : ℕ) < 2) (by rw [hmain', h2])

end Work.CORE3.J4
