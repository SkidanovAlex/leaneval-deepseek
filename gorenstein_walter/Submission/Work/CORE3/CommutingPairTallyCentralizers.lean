import Mathlib
import Submission.Work.CORE3.Defs
import Submission.Work.CORE2A.Basic
import Submission.Work.CORE3.Case1bEightNineDefs
import Submission.Work.CORE3.BCountSum
import Submission.Work.CPTC.NcardPairsEqSum
import Submission.Work.CPTC.NcardInvolutionsFourGroup
import Submission.Work.CPTC.NcardInvolutionSetTopSplit

namespace Work.CORE3

open Subgroup
open Work.GW2

/-- A set-builder `ncard` in a finite type is a `Finset.filter`-cardinality. -/
private lemma ncard_eq_filter_card_aux {α : Type} [Fintype α] (p : α → Prop) [DecidablePred p] :
    ({x : α | p x} : Set α).ncard = (Finset.univ.filter p).card := by
  rw [Set.ncard_eq_toFinset_card', Set.toFinset_ofPred]

/-- **Bender 1981 §3 (8), centralizer form.**  The number of ordered pairs `(z,s)` of commuting
involutions with `z ∉ Ĥ` and `s ∈ Ĥ` is `12·|K|²`.

* `Work.CPTC.NcardPairsEqSum` computes the number of such pairs as the sum, over the involutions
  `s ∈ Ĥ`, of the number of involutions outside `Ĥ` centralizing `s`;
* `Work.CPTC.NcardInvolutionSetTopSplit` splits the involutions of `G` centralizing `s` into
  those outside `Ĥ` and those inside `Ĥ`, so that `hCent` and `hVsharp` resp. `hOut` give that
  exactly `0` (for `s ∈ V = O₂(Ĥ)`) resp. `2·|K|` (for `s ∈ Ĥ − V`) involutions outside `Ĥ`
  centralize `s`;
* `Work.CPTC.NcardInvolutionsFourGroup` gives `|V \ {1}| = 3`, so that `hCount` — which gives
  `|Ĥ ∩ J| = 3 + 6·|K|` — yields `|(Ĥ − V) ∩ J| = 6·|K|`, whence `12·|K|² = (6|K|)·(2|K|)`. -/
theorem CommutingPairTallyCentralizers (G : Type) [Group G] [Finite G] (I : Work.CORE3.Case1Inputs) (h : Work.GW2.BenderCtx G)
    (B : Work.GW2.BenderSetup G) (h1 : Work.GW2.Case1 B) (D : Work.GW2.Case1bData B)
    (hCount : Work.GW2.Case1bCountProp)
    (hCent : ∀ s : G, orderOf s = 2 →
      (Work.GW2.involutionSet (⊤ : Subgroup G) ∩ Subgroup.centralizer ({s} : Set G)).ncard
        = 3 + 2 * Nat.card D.K)
    (hVsharp : ∀ s : G, s ∈ Work.GW2.pCoreIn 2 B.Hhat → orderOf s = 2 →
      (Work.GW2.involutionSet B.Hhat ∩ Subgroup.centralizer ({s} : Set G)).ncard
        = 3 + 2 * Nat.card D.K)
    (hOut : ∀ s : G, s ∈ B.Hhat → orderOf s = 2 → s ∉ Work.GW2.pCoreIn 2 B.Hhat →
      (Work.GW2.involutionSet B.Hhat ∩ Subgroup.centralizer ({s} : Set G)).ncard = 3) :
    (Work.CORE3.commutingPairsOutsideHat B).ncard = 12 * Nat.card D.K ^ 2 := by
  classical
  haveI : Fintype G := Fintype.ofFinite G
  have hVH : Work.GW2.pCoreIn 2 B.Hhat ≤ B.Hhat := Subgroup.map_subtype_le _
  -- ## 1.  The target as a commuting-pair set, and the Fubini identity over `s ∈ Ĥ ∩ J`.
  have htarget : (Work.CORE3.commutingPairsOutsideHat B).ncard
      = ({p : G × G | p.1 ∈ Work.CORE3.involsOutsideHat B
          ∧ p.2 ∈ Work.GW2.involutionSet B.Hhat
          ∧ p.1 * p.2 = p.2 * p.1} : Set (G × G)).ncard := rfl
  rw [htarget, Work.CPTC.NcardPairsEqSum (Z := Work.CORE3.involsOutsideHat B)
    (J := Work.GW2.involutionSet B.Hhat)]
  -- ## 2.  Split the sum by whether `s ∈ V = O₂(Ĥ)`.
  rw [← Finset.sum_filter_add_sum_filter_not
    (Finset.univ.filter (fun s : G => s ∈ Work.GW2.involutionSet B.Hhat))
    (fun s : G => s ∈ Work.GW2.pCoreIn 2 B.Hhat)
    (fun s : G => (Work.CORE3.involsOutsideHat B
      ∩ Subgroup.centralizer ({s} : Set G)).ncard)]
  -- ## 3.  The `s ∈ V` part vanishes.
  have hsum1 : (((Finset.univ.filter (fun s : G => s ∈ Work.GW2.involutionSet B.Hhat)).filter
      (fun s : G => s ∈ Work.GW2.pCoreIn 2 B.Hhat)).sum
      (fun s : G => (Work.CORE3.involsOutsideHat B
        ∩ Subgroup.centralizer ({s} : Set G)).ncard)) = 0 := by
    apply Finset.sum_eq_zero
    intro s hs
    have hsJ : s ∈ Work.GW2.involutionSet B.Hhat :=
      (Finset.mem_filter.mp (Finset.mem_filter.mp hs).1).2
    have hsV : s ∈ Work.GW2.pCoreIn 2 B.Hhat := (Finset.mem_filter.mp hs).2
    obtain ⟨-, hs2⟩ := Work.CORE2A.mem_involutionSet.mp hsJ
    have hAB : (Work.CORE3.involsOutsideHat B ∩ Subgroup.centralizer ({s} : Set G)).ncard
        + (Work.GW2.involutionSet B.Hhat ∩ Subgroup.centralizer ({s} : Set G)).ncard
        = 3 + 2 * Nat.card D.K :=
      Work.CPTC.NcardInvolutionSetTopSplit (K := B.Hhat) (s := s) ▸ hCent s hs2
    rw [hVsharp s hsV hs2] at hAB
    omega
  rw [hsum1]
  -- ## 4.  The `s ∉ V` part contributes `2k` per element.
  have hconst : ∀ s ∈ ((Finset.univ.filter (fun s : G =>
      s ∈ Work.GW2.involutionSet B.Hhat)).filter
      (fun s : G => ¬ s ∈ Work.GW2.pCoreIn 2 B.Hhat)),
      (Work.CORE3.involsOutsideHat B ∩ Subgroup.centralizer ({s} : Set G)).ncard
        = 2 * Nat.card D.K := by
    intro s hs
    have hsJ : s ∈ Work.GW2.involutionSet B.Hhat :=
      (Finset.mem_filter.mp (Finset.mem_filter.mp hs).1).2
    have hsV : ¬ s ∈ Work.GW2.pCoreIn 2 B.Hhat := (Finset.mem_filter.mp hs).2
    obtain ⟨hsH, hs2⟩ := Work.CORE2A.mem_involutionSet.mp hsJ
    have hAB : (Work.CORE3.involsOutsideHat B ∩ Subgroup.centralizer ({s} : Set G)).ncard
        + (Work.GW2.involutionSet B.Hhat ∩ Subgroup.centralizer ({s} : Set G)).ncard
        = 3 + 2 * Nat.card D.K :=
      Work.CPTC.NcardInvolutionSetTopSplit (K := B.Hhat) (s := s) ▸ hCent s hs2
    rw [hOut s hsH hs2 hsV] at hAB
    omega
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, smul_eq_mul]
  -- ## 5.  The two cardinalities.
  have hcard1 : ((Finset.univ.filter (fun s : G => s ∈ Work.GW2.involutionSet B.Hhat)).filter
      (fun s : G => s ∈ Work.GW2.pCoreIn 2 B.Hhat)).card = 3 := by
    have hfe : ((Finset.univ.filter (fun s : G => s ∈ Work.GW2.involutionSet B.Hhat)).filter
        (fun s : G => s ∈ Work.GW2.pCoreIn 2 B.Hhat))
        = (Finset.univ.filter (fun s : G =>
            s ∈ Work.GW2.involutionSet (Work.GW2.pCoreIn 2 B.Hhat))) := by
      ext s
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Work.CORE2A.mem_involutionSet]
      constructor
      · rintro ⟨⟨hsH, hs2⟩, hsV⟩; exact ⟨hsV, hs2⟩
      · rintro ⟨hsV, hs2⟩; exact ⟨⟨hVH hsV, hs2⟩, hsV⟩
    have h2 : (Finset.univ.filter (fun s : G =>
        s ∈ Work.GW2.involutionSet (Work.GW2.pCoreIn 2 B.Hhat))).card
        = (Work.GW2.involutionSet (Work.GW2.pCoreIn 2 B.Hhat)).ncard :=
      (ncard_eq_filter_card_aux (p := fun s : G =>
        s ∈ Work.GW2.involutionSet (Work.GW2.pCoreIn 2 B.Hhat))).symm
    rw [hfe, h2]
    exact Work.CPTC.NcardInvolutionsFourGroup _ D.four
  have hcard2 : ((Finset.univ.filter (fun s : G => s ∈ Work.GW2.involutionSet B.Hhat)).filter
      (fun s : G => ¬ s ∈ Work.GW2.pCoreIn 2 B.Hhat)).card = 6 * Nat.card D.K := by
    have hsplit := Finset.card_filter_add_card_filter_not
      (s := Finset.univ.filter (fun s : G => s ∈ Work.GW2.involutionSet B.Hhat))
      (p := fun s : G => s ∈ Work.GW2.pCoreIn 2 B.Hhat)
    have hJh : (Finset.univ.filter (fun s : G => s ∈ Work.GW2.involutionSet B.Hhat)).card
        = (Work.GW2.involutionSet B.Hhat).ncard :=
      (ncard_eq_filter_card_aux
        (p := fun s : G => s ∈ Work.GW2.involutionSet B.Hhat)).symm
    have hJhv : (Work.GW2.involutionSet B.Hhat).ncard = 3 + 6 * Nat.card D.K :=
      (hCount G I.T.ft h B h1 D).2.1
    omega
  -- ## 6.  Assemble.
  rw [hcard2]
  ring

end Work.CORE3
