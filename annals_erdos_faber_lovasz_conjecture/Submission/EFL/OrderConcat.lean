import Submission.EFL.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.Set.Card

/-!
# Concatenating two orderings of a hypergraph

The paper's proof of Theorem 6.1 (Figure 3) orders the edge set of `𝓗` by
concatenating orderings of the families `𝓗₃, W₂, 𝓗₂^good, 𝓗₁^good` produced
by three applications of the reordering lemma.

This module provides the basic utility: given a partition of the edges of
`𝓗` into two finsets `P` and `Q` (`P ∪ Q = univ`, `P`, `Q` disjoint) and
orderings `↥P ≃ Fin kP`, `↥Q ≃ Fin kQ`, it builds an ordering
`concatOrdering : 𝓗 ≃ Fin (kP + kQ)` in which every edge of `P` precedes
every edge of `Q`, with the comparison lemmas

* `concatOrdering_apply_of_mem`/`_of_notMem` — the rank of an edge;
* `concatOrdering_lt_of_mem_of_notMem` — `P` before `Q`;
* `concatOrdering_le_iff_of_mem` — agreement with `ordP` on `P`.

A block-wise ordering is then obtained by iterating the construction.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open scoped BigOperators

namespace ErdosFaberLovaszConjecture

noncomputable section

variable {n : ℕ} {𝓗 : Hypergraph (Fin n)} [Fintype 𝓗]

/-- helper: the right part of a partition -/
lemma mem_right_of_mem_union_left (P Q : Finset 𝓗) (hcover : P ∪ Q = Finset.univ)
    (hdisj : Disjoint P Q) {e : 𝓗} (he : e ∉ P) : e ∈ Q := by
  have h : e ∈ P ∪ Q := by rw [hcover]; exact Finset.mem_univ e
  rcases Finset.mem_union.mp h with h' | h'
  · exact absurd h' he
  · exact h'

variable (P Q : Finset 𝓗) (hcover : P ∪ Q = Finset.univ) (hdisj : Disjoint P Q)
variable {kP kQ : ℕ} (ordP : ↥P ≃ Fin kP) (ordQ : ↥Q ≃ Fin kQ)

/-- The rank function of the concatenation of the orderings `ordP` (on `P`) and
`ordQ` (on `Q`), all of `P` preceding all of `Q`. -/
def concatRank (e : 𝓗) : ℕ :=
  if h : e ∈ P then (ordP ⟨e, h⟩ : ℕ)
  else kP + (ordQ ⟨e, mem_right_of_mem_union_left P Q hcover hdisj h⟩ : ℕ)

lemma concatRank_of_mem {e : 𝓗} (h : e ∈ P) :
    concatRank P Q hcover hdisj ordP ordQ e = (ordP ⟨e, h⟩ : ℕ) := by
  rw [concatRank, dif_pos h]

lemma concatRank_of_notMem {e : 𝓗} (h : e ∉ P) :
    concatRank P Q hcover hdisj ordP ordQ e
      = kP + (ordQ ⟨e, mem_right_of_mem_union_left P Q hcover hdisj h⟩ : ℕ) := by
  rw [concatRank, dif_neg h]

lemma concatRank_lt (e : 𝓗) : concatRank P Q hcover hdisj ordP ordQ e < kP + kQ := by
  by_cases h : e ∈ P
  · rw [concatRank_of_mem P Q hcover hdisj ordP ordQ h]
    exact lt_of_lt_of_le (ordP ⟨e, h⟩).isLt (Nat.le_add_right kP kQ)
  · rw [concatRank_of_notMem P Q hcover hdisj ordP ordQ h]
    have := (ordQ ⟨e, mem_right_of_mem_union_left P Q hcover hdisj h⟩).isLt
    omega

lemma concatRank_injective : Function.Injective (concatRank P Q hcover hdisj ordP ordQ) := by
  intro e f hef
  by_cases he : e ∈ P
  · by_cases hf : f ∈ P
    · have h1 := concatRank_of_mem P Q hcover hdisj ordP ordQ he
      have h2 := concatRank_of_mem P Q hcover hdisj ordP ordQ hf
      rw [h1, h2] at hef
      have := ordP.injective (Fin.ext hef)
      exact Subtype.ext_iff.mp this
    · have h1 := concatRank_of_mem P Q hcover hdisj ordP ordQ he
      have h2 := concatRank_of_notMem P Q hcover hdisj ordP ordQ hf
      rw [h1, h2] at hef
      have := (ordP ⟨e, he⟩).isLt
      omega
  · by_cases hf : f ∈ P
    · have h1 := concatRank_of_notMem P Q hcover hdisj ordP ordQ he
      have h2 := concatRank_of_mem P Q hcover hdisj ordP ordQ hf
      rw [h1, h2] at hef
      have := (ordP ⟨f, hf⟩).isLt
      omega
    · have h1 := concatRank_of_notMem P Q hcover hdisj ordP ordQ he
      have h2 := concatRank_of_notMem P Q hcover hdisj ordP ordQ hf
      rw [h1, h2] at hef
      have heq : (ordQ ⟨e, mem_right_of_mem_union_left P Q hcover hdisj he⟩ : ℕ)
          = (ordQ ⟨f, mem_right_of_mem_union_left P Q hcover hdisj hf⟩ : ℕ) := by
        omega
      have := ordQ.injective (Fin.ext heq)
      exact Subtype.ext_iff.mp this

/-- the cardinality of the partition -/
lemma card_eq_add (P Q : Finset 𝓗) (hcover : P ∪ Q = Finset.univ) (hdisj : Disjoint P Q)
    (ordP : ↥P ≃ Fin kP) (ordQ : ↥Q ≃ Fin kQ) : Fintype.card 𝓗 = kP + kQ := by
  have h1 : Fintype.card 𝓗 = P.card + Q.card := by
    rw [← Finset.card_univ, ← hcover, Finset.card_union_of_disjoint hdisj]
  have h2 : P.card = kP := by
    rw [← Fintype.card_coe, Fintype.card_congr ordP, Fintype.card_fin]
  have h3 : Q.card = kQ := by
    rw [← Fintype.card_coe, Fintype.card_congr ordQ, Fintype.card_fin]
  rw [h1, h2, h3]

/-- **Concatenation of orderings**: all of `P` before all of `Q`. -/
def concatOrdering (P Q : Finset 𝓗) (hcover : P ∪ Q = Finset.univ) (hdisj : Disjoint P Q)
    (ordP : ↥P ≃ Fin kP) (ordQ : ↥Q ≃ Fin kQ) : 𝓗 ≃ Fin (kP + kQ) :=
  Equiv.ofBijective
    (fun e => (⟨concatRank P Q hcover hdisj ordP ordQ e,
      concatRank_lt P Q hcover hdisj ordP ordQ e⟩ : Fin (kP + kQ)))
    ⟨fun e f hef =>
        concatRank_injective P Q hcover hdisj ordP ordQ (congrArg Fin.val hef),
      by
        intro x
        set f : 𝓗 → Fin (kP + kQ) := fun e =>
          (⟨concatRank P Q hcover hdisj ordP ordQ e,
            concatRank_lt P Q hcover hdisj ordP ordQ e⟩ : Fin (kP + kQ)) with hf
        have hinj : Function.Injective f := fun e g hefg =>
          concatRank_injective P Q hcover hdisj ordP ordQ (congrArg Fin.val hefg)
        have himg : (Finset.univ.image f).card = Fintype.card 𝓗 := by
          rw [Finset.card_image_of_injective (s := (Finset.univ : Finset 𝓗)) (f := f) hinj,
            Finset.card_univ]
        have hEq : (Finset.univ.image f) = (Finset.univ : Finset (Fin (kP + kQ))) := by
          apply Finset.eq_of_subset_of_card_le
          · intro y hy
            simp
          · rw [himg, card_eq_add P Q hcover hdisj ordP ordQ]
            simp
        have hx : x ∈ Finset.univ.image f := by
          rw [hEq]; simp
        rcases (Finset.mem_image.mp hx) with ⟨y, _hy, hEqx⟩
        exact ⟨y, hEqx⟩⟩

lemma concatOrdering_apply_of_mem {e : 𝓗} (h : e ∈ P) :
    ((concatOrdering P Q hcover hdisj ordP ordQ e : Fin (kP + kQ)) : ℕ)
      = (ordP ⟨e, h⟩ : ℕ) :=
  concatRank_of_mem P Q hcover hdisj ordP ordQ h

lemma concatOrdering_apply_of_notMem {e : 𝓗} (h : e ∉ P) :
    ((concatOrdering P Q hcover hdisj ordP ordQ e : Fin (kP + kQ)) : ℕ)
      = kP + (ordQ ⟨e, mem_right_of_mem_union_left P Q hcover hdisj h⟩ : ℕ) :=
  concatRank_of_notMem P Q hcover hdisj ordP ordQ h

lemma concatOrdering_lt_of_mem_of_notMem {e f : 𝓗} (he : e ∈ P) (hf : f ∉ P) :
    ((concatOrdering P Q hcover hdisj ordP ordQ e : Fin (kP + kQ)) : ℕ)
      < ((concatOrdering P Q hcover hdisj ordP ordQ f : Fin (kP + kQ)) : ℕ) := by
  rw [concatOrdering_apply_of_mem P Q hcover hdisj ordP ordQ he,
    concatOrdering_apply_of_notMem P Q hcover hdisj ordP ordQ hf]
  have := (ordP ⟨e, he⟩).isLt
  omega

lemma concatOrdering_le_iff_of_mem {e f : 𝓗} (he : e ∈ P) (hf : f ∈ P) :
    ((concatOrdering P Q hcover hdisj ordP ordQ e : Fin (kP + kQ)) : ℕ)
      ≤ ((concatOrdering P Q hcover hdisj ordP ordQ f : Fin (kP + kQ)) : ℕ)
    ↔ (ordP ⟨e, he⟩ : ℕ) ≤ (ordP ⟨f, hf⟩ : ℕ) := by
  rw [concatOrdering_apply_of_mem P Q hcover hdisj ordP ordQ he,
    concatOrdering_apply_of_mem P Q hcover hdisj ordP ordQ hf]

lemma concatOrdering_apply_of_notMem' {e : 𝓗} (h : e ∉ P) :
    ((concatOrdering P Q hcover hdisj ordP ordQ e : Fin (kP + kQ)) : ℕ)
      = kP + (ordQ ⟨e, mem_right_of_mem_union_left P Q hcover hdisj h⟩ : ℕ) :=
  concatOrdering_apply_of_notMem P Q hcover hdisj ordP ordQ h

end
end ErdosFaberLovaszConjecture
