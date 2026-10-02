import Submission.Work.ConeSwitch.MathlibNoHG
import Submission.Work.Deep.Kahn.boxProb

/-!
# Sensitivity of `keptEvidence`, and the certificate property

The statistic `X ω = #(keptEvidence K e ω)` (the number of colours of `L e` that are used at
`e` by an activated witness) is used in the `usedColours` estimate together with Talagrand's
certificate machinery (`Work.Deep.Reed.Prob.certifiable_upper`).  This module proves the two
structural inputs:

* `lipschitz`: changing one coordinate of the outcome changes `X` by at most `1`;
* `certifiable`: for every level `w ≥ 1` at most `2 w` coordinates need to be frozen to keep
  `X ≥ w`.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open scoped BigOperators
open Finset

namespace Work.Deep.Kahn

open ErdosFaberLovaszConjecture

noncomputable section

variable {n c : ℕ} {𝓗 : ErdosFaberLovaszConjecture.Hypergraph (Fin n)} [Fintype 𝓗]
  {L : 𝓗 → Finset (Fin c)} {K : ℕ} [NeZero K]

/-- **Sensitivity and certificates for `#keptEvidence`.**

The first component says that `X ω = #(keptEvidence K e ω)` is `1`-Lipschitz for the product
metric on the coordinates: moving a single edge to another class/index pair changes the set of
colours used at `e` by adding at most the single colour named by the new coordinate and losing
at most the single colour named by the old one.

The second component is the certificate property with `r = 2`: if `1 ≤ w ≤ X ω`, then freezing
the (at most `⌈w⌉ ≤ 2w`) witness edges of `⌈w⌉` used colours keeps those colours used. -/
theorem keptEvidence_lip_cert (e : 𝓗) :
    (∀ (i : 𝓗) (ω : Round.Space K 𝓗 L) (x : Round.Coord K 𝓗 L i),
      |(((keptEvidence K e (Function.update ω i x)).card : ℝ)) -
        (((keptEvidence K e ω).card : ℝ))| ≤ 1) ∧
    (∀ (ω : Round.Space K 𝓗 L) (w : ℝ), 1 ≤ w → w ≤ ((keptEvidence K e ω).card : ℝ) →
      ∃ S : Finset 𝓗, (S.card : ℝ) ≤ 2 * w ∧
        ∀ g : Round.Space K 𝓗 L, (∀ i ∈ S, g i = ω i) →
          w ≤ ((keptEvidence K e g).card : ℝ)) := by
  classical
  constructor
  · intro i ω x
    set A := keptEvidence K e (Function.update ω i x) with hA
    set B := keptEvidence K e ω with hB
    have hAB : A \ B ⊆ ({idxColour L i x.2} : Finset (Fin c)) := by
      intro γ hγ
      rw [Finset.mem_sdiff] at hγ
      obtain ⟨hγA, hγB⟩ := hγ
      obtain ⟨hγLe, f, hfe, hmeet, hcls, hidx⟩ := mem_classEvidence.mp hγA
      by_cases hfi : f = i
      · rw [hfi] at hcls hidx
        rw [Finset.mem_singleton, ← hidx]
        simp only [idxOf, Function.update_self]
      · exfalso
        have hupd : Function.update ω i x f = ω f := Function.update_of_ne hfi x ω
        refine hγB (mem_classEvidence.mpr ⟨hγLe, f, hfe, hmeet, ?_, ?_⟩)
        · change (ω f).1 = 0
          rw [← hupd]; exact hcls
        · simpa only [idxOf, hupd] using hidx
    have hBA : B \ A ⊆ ({idxColour L i (ω i).2} : Finset (Fin c)) := by
      intro γ hγ
      rw [Finset.mem_sdiff] at hγ
      obtain ⟨hγB, hγA⟩ := hγ
      obtain ⟨hγLe, f, hfe, hmeet, hcls, hidx⟩ := mem_classEvidence.mp hγB
      by_cases hfi : f = i
      · rw [hfi] at hcls hidx
        rw [Finset.mem_singleton, ← hidx]
        rfl
      · exfalso
        have hupd : Function.update ω i x f = ω f := Function.update_of_ne hfi x ω
        refine hγA (mem_classEvidence.mpr ⟨hγLe, f, hfe, hmeet, ?_, ?_⟩)
        · simpa only [clsOf, hupd] using hcls
        · simpa only [idxOf, hupd] using hidx
    have hcardAB : (A \ B).card ≤ 1 :=
      Finset.card_le_one.mpr fun a ha b hb => by
        have ha' := Finset.mem_singleton.mp (hAB ha)
        have hb' := Finset.mem_singleton.mp (hAB hb)
        rw [ha', hb']
    have hcardBA : (B \ A).card ≤ 1 :=
      Finset.card_le_one.mpr fun a ha b hb => by
        have ha' := Finset.mem_singleton.mp (hBA ha)
        have hb' := Finset.mem_singleton.mp (hBA hb)
        rw [ha', hb']
    have hAcard : A.card ≤ (A ∩ B).card + 1 := by
      have h1 := Finset.card_sdiff_add_card_inter A B
      omega
    have hBcard : B.card ≤ (B ∩ A).card + 1 := by
      have h1 := Finset.card_sdiff_add_card_inter B A
      omega
    have hBA' : (B ∩ A).card = (A ∩ B).card := by rw [Finset.inter_comm]
    rw [hBA'] at hBcard
    have hIA : (A ∩ B).card ≤ A.card := Finset.card_le_card Finset.inter_subset_left
    have hIB : (A ∩ B).card ≤ B.card := Finset.card_le_card Finset.inter_subset_right
    have h1 : ((A.card : ℝ) - (B.card : ℝ)) ≤ 1 := by
      have h2 : (A.card : ℝ) ≤ ((A ∩ B).card : ℝ) + 1 := by
        have hcast : ((A.card : ℕ) : ℝ) ≤ (((A ∩ B).card + 1 : ℕ) : ℝ) :=
          Nat.cast_le.mpr hAcard
        push_cast at hcast
        linarith
      have h3 : ((A ∩ B).card : ℝ) ≤ (B.card : ℝ) := Nat.cast_le.mpr hIB
      linarith
    have h2 : ((B.card : ℝ) - (A.card : ℝ)) ≤ 1 := by
      have h3 : (B.card : ℝ) ≤ ((A ∩ B).card : ℝ) + 1 := by
        have hcast : ((B.card : ℕ) : ℝ) ≤ (((A ∩ B).card + 1 : ℕ) : ℝ) :=
          Nat.cast_le.mpr hBcard
        push_cast at hcast
        linarith
      have h4 : ((A ∩ B).card : ℝ) ≤ (A.card : ℝ) := Nat.cast_le.mpr hIA
      linarith
    exact (abs_sub_le_iff (a := ((A.card : ℝ))) (b := ((B.card : ℝ)))).mpr ⟨h1, h2⟩
  · intro ω w hw1 hwle
    set B := keptEvidence K e ω with hB
    have hk : ⌈w⌉₊ ≤ B.card := Nat.ceil_le.mpr hwle
    obtain ⟨T, hTB, hTcard⟩ := Finset.exists_subset_card_eq hk
    have hwit : ∀ γ : {x // x ∈ T}, ∃ f : 𝓗, f ≠ e ∧
        ((f : Set (Fin n)) ∩ (e : Set (Fin n))).Nonempty ∧
        (ω f).1 = 0 ∧ idxColour L f (ω f).2 = γ.1 := by
      intro γ
      obtain ⟨-, f, hfe, hmeet, hcls, hidx⟩ := mem_classEvidence.mp (hTB γ.2)
      exact ⟨f, hfe, hmeet, hcls, hidx⟩
    choose φ hφ using hwit
    refine ⟨T.attach.image φ, ?_, ?_⟩
    · have h1 : (T.attach.image φ).card ≤ T.attach.card := Finset.card_image_le
      have h2 : T.attach.card = T.card := Finset.card_attach
      have h3 : ((T.card : ℕ) : ℝ) = (⌈w⌉₊ : ℝ) := by rw [hTcard]
      have h4 : (⌈w⌉₊ : ℝ) < w + 1 :=
        Nat.ceil_lt_add_one (show (0 : ℝ) ≤ w from le_trans zero_le_one hw1)
      have hcast : ((T.attach.image φ).card : ℝ) ≤ ((T.attach.card : ℕ) : ℝ) :=
        Nat.cast_le.mpr h1
      rw [h2, h3] at hcast
      linarith
    · intro g hg
      have hmem : ∀ γ ∈ T, γ ∈ keptEvidence K e g := by
        intro γ hγT
        have hγLe : γ ∈ L e := (mem_classEvidence.mp (hTB hγT)).1
        have hmemimg : φ ⟨γ, hγT⟩ ∈ T.attach.image φ :=
          Finset.mem_image.mpr ⟨⟨γ, hγT⟩, Finset.mem_attach _ _, rfl⟩
        have hagree : g (φ ⟨γ, hγT⟩) = ω (φ ⟨γ, hγT⟩) := hg _ hmemimg
        obtain ⟨hfe, hmeet, hcls, hidx⟩ := hφ ⟨γ, hγT⟩
        refine mem_classEvidence.mpr ⟨hγLe, φ ⟨γ, hγT⟩, hfe, hmeet, ?_, ?_⟩
        · simpa only [clsOf, hagree] using hcls
        · simpa only [idxOf, hagree] using hidx
      have h3 : ((T.card : ℕ) : ℝ) ≤ ((keptEvidence K e g).card : ℝ) :=
        Nat.cast_le.mpr (Finset.card_le_card hmem)
      have h4 : w ≤ (⌈w⌉₊ : ℝ) := Nat.le_ceil w
      rw [hTcard] at h3
      linarith

end

end Work.Deep.Kahn
