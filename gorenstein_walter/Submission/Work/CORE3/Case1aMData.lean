import Mathlib
import Submission.Work.CORE3.Defs
import Submission.Work.CORE2A.Basic
import Submission.Work.CORE3.MDataAux
import Submission.Work.CORE3.MData.BcLeM
import Submission.Work.CORE3.MData.BcInfMLeOddCore
import Submission.Work.CORE3.MData.OddCoreLeBc
import Submission.Work.CORE3.MData.UMLe
import Submission.Work.CORE3.MData.LocalControlOfOddCore

namespace Work.CORE3

namespace Work.CORE3

open Subgroup
open Work.GW2

/-- Bender 1981 §3, p. 223: the `M`-analysis of the subcase `Ĥ = H`.  Deliverable
`Work.CORE3.Case1aMDataProp`.

Bender's paragraph "Again by Lemma 2.9, `E(N_G(X))` contains and hence equals `E` whenever
`1 ≠ X ⊆ B ∩ M`, and this implies `N_G(X) ⊆ M`.  Applying this to the normal subgroup
`X = B ∩ PP^g` of `C_{F(U)}(t₂) = B C_{F(U)}(t₂)`, we see that `B ⊆ M` and
`C_U(t₂) = B × P₀`", together with the display `B ∩ M = O(M)`, `|S| = 8`, `|P₀| = 3`,
`U ∩ M = P₀ × (B ∩ M)`, gives the four conjuncts: `B ≤ M`, `B ∩ M = O(M)`,
`U ∩ M = P₀ ⊔ (B ∩ M)`, and local control `N_G(X) ≤ M` for `1 ≠ X ≤ B` (Lemma 2.9, `I.h29`;
with `E(N_G(X)) ⊇ E` and `N_G(E) = M` by maximality).

Inputs: `hSetup` (for `D : Case1aData B`), `hFr` (`P₂ ≠ 1`, `N_G(P₁) ⊄ H`), `hAb`
(`P ∩ P^g = ⊥`, `P P^g` abelian), `hA7` (`E(M)/Z ≅ A₇`, `|S| = 8`, `|P₀| = 3`,
`⟨t,t₂⟩ ≤ E(M)`). -/
theorem Case1aMData (I : Case1Inputs) (hSetup : Case1aSetupProp) (hFr : Case1aFrattiniProp)
    (hAb : Case1aAbelianProp) (hA7 : Case1aA7Prop) : Case1aMDataProp := by
  intro G _instG _finG hFT hCtx B hCase hHhat D P2 M hP2le hP2grp hP2ndvd hMcoat hNM
  -- the `A₇` data of the §3 `M`-analysis (`Case1aA7Prop` at the same `P2`, `M`)
  obtain ⟨_hSleM, _hV2, _hiso, _hcardS, _hcardP0⟩ :=
    hA7 G hFT hCtx B hCase hHhat D P2 M hP2le hP2grp hP2ndvd hMcoat hNM
  -- `P₂ ≠ ⊥` (Bender's "`P₂ ≠ 1`"), hence `B = C_U(S) ≠ ⊥`
  have hP2ne : P2 ≠ ⊥ := (hFr G hFT hCtx B hCase hHhat D P2 hP2le hP2grp hP2ndvd).2.2
  have hBne : B.U ⊓ Subgroup.centralizer ((B.S : Subgroup G) : Set G) ≠ ⊥ := by
    intro hbot
    exact hP2ne (eq_bot_iff.mpr (le_trans hP2le (le_of_eq hbot)))
  -- conjunct 1: `B ≤ M` (Bender p. 223)
  have h1 : B.U ⊓ Subgroup.centralizer ((B.S : Subgroup G) : Set G) ≤ M :=
    Work.CORE3.MData.BcLeM I hSetup hFr hAb hA7 G hFT hCtx B hCase hHhat D P2 M
      hP2le hP2grp hP2ndvd hMcoat hNM
  -- conjunct 2: `B ∩ M = O(M)` (Bender's display)
  have h2 : (B.U ⊓ Subgroup.centralizer ((B.S : Subgroup G) : Set G)) ⊓ M = oddCoreIn M := by
    refine le_antisymm ?_ ?_
    · exact Work.CORE3.MData.BcInfMLeOddCore I hSetup hFr hAb hA7 G hFT hCtx B hCase hHhat D P2 M
        hP2le hP2grp hP2ndvd hMcoat hNM
    · exact le_inf
        (Work.CORE3.MData.OddCoreLeBc I hSetup hFr hAb hA7 G hFT hCtx B hCase hHhat D P2 M
          hP2le hP2grp hP2ndvd hMcoat hNM)
        (Work.CORE3.oddCoreIn_le_self M)
  -- conjunct 3: `U ∩ M = P₀ ⊔ (B ∩ M)` (Bender's display)
  have h3 : B.U ⊓ M =
      (pCoreIn D.p B.U ⊓ M) ⊔ (B.U ⊓ Subgroup.centralizer ((B.S : Subgroup G) : Set G)) := by
    refine le_antisymm ?_ ?_
    · exact Work.CORE3.MData.UMLe I hSetup hFr hAb hA7 G hFT hCtx B hCase hHhat D P2 M
        hP2le hP2grp hP2ndvd hMcoat hNM
    · refine sup_le (le_inf (le_trans inf_le_left (Work.CORE3.pCoreIn_le_self D.p B.U)) inf_le_right) ?_
      exact le_inf (MdataB_le_U B) h1
  -- conjunct 4: Lemma 2.9 local control (via `B ∩ M = O(M)`)
  have h4 : ∀ X : Subgroup G, X ≠ ⊥ →
      X ≤ B.U ⊓ Subgroup.centralizer ((B.S : Subgroup G) : Set G) →
        Subgroup.normalizer (X : Set G) ≤ M := by
    intro X hXne hXle
    have hXO : X ≤ Work.GW2.oddCoreIn M := by
      rw [← h2]
      exact le_inf hXle (le_trans hXle h1)
    exact Work.CORE3.MData.LocalControlOfOddCore I hSetup hFr hAb hA7 G hFT hCtx B hCase hHhat
      D P2 M hP2le hP2grp hP2ndvd hMcoat hNM X hXne hXO
  exact ⟨h1, h2, h3, h4⟩

end Work.CORE3

open Work.GW2

/-- The same theorem, exposed at the namespace of the file path (the skeleton's doubly nested
name `Work.CORE3.Work.CORE3.Case1aMData` continues to exist unchanged). -/
theorem Case1aMData (I : Case1Inputs) (hSetup : Case1aSetupProp) (hFr : Case1aFrattiniProp)
    (hAb : Case1aAbelianProp) (hA7 : Case1aA7Prop) : Case1aMDataProp :=
  _root_.Work.CORE3.Work.CORE3.Case1aMData I hSetup hFr hAb hA7

end Work.CORE3
