import Mathlib
import Submission.Work.ThmG2.Defs
import Submission.Work.ThmG.Main
import Submission.Work.ThmG.degree_count_engine
import Submission.Work.ThmG.nilpotent_of_K_ne_one
import Submission.Work.ThmG.nilpotent_two_odd_split
import Submission.Work.ThmG.rankOne_isTI
import Submission.Work.ThmG.rankOne_index
import Submission.Work.ThmG.oddPart_le_normalizer
import Submission.Work.ThmG.irr_eq_one_of_forall_eq_one
import Submission.Work.PGroup.card_sup_mul_card_inf
import Submission.Work.PGroup.card_sup_mul_card_inf_of_le_normalizer
import Submission.Work.CharCore.Main

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Area `ThmG2`: Théorème G with the corrected rank-one inputs — `thmG2`

The assembly of Théorème G (Peterfalvi II, Ch. VI §1, p. 257) from the corrected inputs.  This is
the proof of `Work.ThmG.thmG` (`Submission/Work/ThmG/Main.lean`) **verbatim**, with exactly three
edits forced by the correction of fields 5 and 6 (see `ThmG2/Defs.lean`):

1. the hypothesis is `hStr : RankOneStructure2Prop`;
2. `obtain ⟨lam, hlam, hlam1, hlamne, hlamQ, hlamK⟩ := hstr.exists_linear` carries the extra
   `K ⊆ ker lam` component;
3. `hstr.ind_two lam hlam hlam1 hlamne hlamQ hlamK` is fed the extra component.

The rest — `nilpotent_of_K_ne_one`, `nilpotent_two_odd_split`, `rankOne_isTI`, `rankOne_index`,
Feit–Sibley, `degree_count_engine` (which uses only `Q ⊆ ker lam`, `λ ≠ 1`, linearity and
`Ind λ = f₁ + f₂`) and the final simplicity contradiction — is unchanged.

See `Submission/Work/ThmG/_design/ThmG2_check.lean` for the scratch elaboration of this same proof.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

noncomputable section

open Classical
open Submission.Blueprint

namespace Work.ThmG2

open Work.ThmG

/-- **Théorème G** (Peterfalvi II, Ch. VI §1, p. 257), with the corrected rank-one inputs: in a
simple group in situation (B0)–(B2) with a split rank-one datum `H = Q ⋊ D`, `t ∉ H`, which is not
a Zassenhaus group and satisfies `(B3)`, the normal complement `Q` is a 2-group. -/
theorem thmG2 (hFT : FeitThompsonProp) (hFS : FeitSibleyProp) (hC4 : ChIIFourProp)
    (hTh : ThompsonFrobeniusProp) (hStr : RankOneStructure2Prop) : ThmGProp := by
  intro G _ _ hSit hsimple H Q t hsplit hnotZ hB3
  letI : Fintype G := Fintype.ofFinite G
  by_contra hnotp
  have hstr : RankOneStructure2 G H Q t := hStr G H Q t ⟨hSit, hsimple, hsplit, hnotZ, hB3⟩
  -- `Q` is nilpotent (Ch. V §1 Prop. 1 b)
  have hQnil : Group.IsNilpotent Q :=
    nilpotent_of_K_ne_one hSit hC4 hTh hsplit hstr.K_ne_one
  -- the decomposition `Q = S × Q₁`
  obtain ⟨hsupQ, hinfQ, hcommQ, hcopS, hoddQ₁, hnilS, hcardQ, hQ₁ne⟩ :=
    nilpotent_two_odd_split Q hQnil
  have hQ₁Q : oddPart Q ≤ Q := oddPart_le Q
  have hQ₁H : oddPart Q ≤ H := le_trans hQ₁Q hsplit.le
  have hQ₁ne' : oddPart Q ≠ ⊥ := hQ₁ne hnotp
  have hDnorm : twoPoint H t ≤ Subgroup.normalizer (Q : Set G) :=
    le_trans inf_le_left hsplit.normal
  -- cardinalities
  have hcardHD : Nat.card ↥H = Nat.card ↥Q * Nat.card ↥(twoPoint H t) := by
    have h := Work.PGroup.card_sup_mul_card_inf_of_le_normalizer (H := Q)
      (K := twoPoint H t) hDnorm
    rw [hsplit.sup_eq, hsplit.inf_eq] at h
    simpa using h
  have hEvenH : Even (Nat.card ↥H) := hsplit.stronglyEmbedded.2.1
  have hOddD : Odd (Nat.card ↥(twoPoint H t)) := hsplit.stronglyEmbedded.2.2 t hsplit.not_mem
  have hEvenQ : Even (Nat.card ↥Q) := even_of_eq_mul hcardHD hEvenH hOddD
  have hS2 : 2 ≤ Nat.card ↥(twoPart Q) :=
    two_le_of_eq_mul hcardQ.symm hEvenQ hoddQ₁ Nat.card_pos.ne'
  have hQ₁3 : 3 ≤ Nat.card ↥(oddPart Q) :=
    three_le_of_odd_ne_one hoddQ₁ (fun h1 => hQ₁ne' (Subgroup.card_eq_one.mp h1))
  have hD3 : 3 ≤ Nat.card ↥(twoPoint H t) :=
    three_le_of_odd_ne_one hOddD (fun h1 => hstr.D_ne_bot (Subgroup.card_eq_one.mp h1))
  have hQ₁N : ((oddPart Q).subgroupOf H).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hQ₁H]
    exact oddPart_le_normalizer hsplit.normal
  have hQ₁card : Nat.card ↥((oddPart Q).subgroupOf H) = Nat.card ↥(oddPart Q) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQ₁H).toEquiv
  have hQ₁pos : Nat.card ↥(oddPart Q) ≠ 0 := Nat.card_pos.ne'
  have hindex : ((oddPart Q).subgroupOf H).index
      = Nat.card ↥(twoPart Q) * Nat.card ↥(twoPoint H t) := by
    have h1 : Nat.card ↥((oddPart Q).subgroupOf H) * ((oddPart Q).subgroupOf H).index
        = Nat.card ↥H := Subgroup.card_mul_index _
    rw [hQ₁card] at h1
    exact index_eq_of_mul_eq h1 hcardHD hcardQ.symm hQ₁pos
  have hindexQ : H.index = Nat.card ↥Q + 1 := rankOne_index hsplit
  have hHindexOdd : Odd H.index := by
    rw [hindexQ]
    exact hEvenQ.add_one
  have hnot2Q₁ : ¬ IsPGroup 2 (oddPart Q) := by
    intro h2
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp h2
    have hn0 : n = 0 := by
      by_contra hn0
      have hdvd : 2 ∣ 2 ^ n := dvd_pow_self 2 hn0
      rw [← hn] at hdvd
      have hmod : Nat.card ↥(oddPart Q) % 2 = 0 :=
        Nat.dvd_iff_mod_eq_zero.mp (hn ▸ hdvd)
      have hodd : Nat.card ↥(oddPart Q) % 2 = 1 := Nat.odd_iff.mp hoddQ₁
      omega
    rw [hn0, pow_zero] at hn
    exact hQ₁ne' (Subgroup.card_eq_one.mp hn)
  -- Feit–Sibley (App. XII): `𝒮` is coherent for `Ind_H^G`
  have hFSdata : 2 ≤ (excludingKernel H (oddPart Q)).card ∧
      Work.Coherence.Coherent (excludingKernel H (oddPart Q)) (indLinear H) :=
    hFS G H Q (twoPoint H t) (twoPart Q) (oddPart Q)
      hsplit.stronglyEmbedded.1 hsplit.le hsplit.normal inf_le_left
      hsplit.inf_eq hsplit.sup_eq hstr.coprime (rankOne_isTI hsplit)
      hsupQ hinfQ hcommQ hcopS hnilS hstr.fpf_oddPart hnot2Q₁ hOddD
  obtain ⟨hcard2, hcoh⟩ := hFSdata
  obtain ⟨lam, hlam, hlam1, hlamne, hlamQ, hlamK⟩ := hstr.exists_linear
  obtain ⟨f₁, hf1, f₂, hf2, hfne, hind⟩ := hstr.ind_two lam hlam hlam1 hlamne hlamQ hlamK
  -- the degree count
  obtain ⟨f, hf, hfne1, hker⟩ :=
    degree_count_engine hQ₁H hQ₁N hsplit.normal (rankOne_isTI hsplit)
      hsplit.sup_eq hsplit.inf_eq hstr.coprime hD3 hS2 hQ₁3 hcardHD hcardQ.symm hindex
      hcoh hcard2 hstr.vanishes_off hstr.degree hlam hlam1 hlamQ hlamne hf1 hf2 hfne hind
      hindexQ hHindexOdd
  -- `ker f` is a non-trivial proper normal subgroup
  obtain ⟨N, hNnorm, hNset⟩ := Work.CharCore.charKernel_subgroup hf
  have hQ₁Nle : oddPart Q ≤ N := by
    intro x hx
    show x ∈ (N : Set G)
    rw [hNset]
    exact hker ⟨x, hQ₁H hx⟩ hx
  have hNbot : N ≠ ⊥ := by
    rintro rfl
    exact hQ₁ne' (le_bot_iff.mp hQ₁Nle)
  have hNtop : N ≠ ⊤ := by
    intro htop
    have hconst : ∀ x : G, f x = f 1 := by
      intro x
      have hxN : x ∈ (N : Set G) := by
        rw [htop]
        exact Subgroup.mem_top x
      rw [hNset] at hxN
      exact hxN
    exact hfne1 (irr_eq_one_of_forall_eq_one hf hconst)
  rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal _ _ hsimple N hNnorm with h | h
  · exact hNbot h
  · exact hNtop h

end Work.ThmG2
