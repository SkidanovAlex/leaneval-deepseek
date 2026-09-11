import Mathlib
import Submission.SunBasic

/-!
# The `χ` ("best remainder") function
-/
open Finset
open scoped BigOperators

namespace Submission.Sun

variable {α : Type*} [DecidableEq α]

/-- candidates for χ: members A' ∈ S contained in A ∪ U -/
def cand (S : Finset (Finset α)) (U A : Finset α) : Finset (Finset α) :=
  S.filter (fun A' : Finset α => A' ⊆ A ∪ U)

lemma mem_cand {S : Finset (Finset α)} {U A A' : Finset α} :
    A' ∈ cand S U A ↔ A' ∈ S ∧ A' ⊆ A ∪ U := by
  simp [cand]

lemma cand_self {S : Finset (Finset α)} {U A : Finset α} (hA : A ∈ S) :
    A ∈ cand S U A := by
  simp [cand, hA]

lemma cand_nonempty {S : Finset (Finset α)} {U A : Finset α} (hA : A ∈ S) :
    (cand S U A).Nonempty := ⟨A, cand_self hA⟩

/-- The canonical best set: an element of the candidates minimizing `|A' \ U|`. -/
noncomputable def best (S : Finset (Finset α)) (U A : Finset α) : Finset α :=
  if h : (cand S U A).Nonempty then
    Classical.choose (Finset.exists_min_image (cand S U A) (fun A' : Finset α => (A' \ U).card) h)
  else A

lemma best_spec {S : Finset (Finset α)} {U A : Finset α} (h : (cand S U A).Nonempty) :
    best S U A ∈ cand S U A ∧
      ∀ A' ∈ cand S U A, (best S U A \ U).card ≤ (A' \ U).card := by
  rw [best, dif_pos h]
  exact Classical.choose_spec
    (Finset.exists_min_image (cand S U A) (fun A' : Finset α => (A' \ U).card) h)

lemma best_mem_cand {S : Finset (Finset α)} {U A : Finset α} (h : (cand S U A).Nonempty) :
    best S U A ∈ cand S U A := (best_spec (S := S) (U := U) (A := A) h).1

lemma best_mem {S : Finset (Finset α)} {U A : Finset α} (hA : A ∈ S) :
    best S U A ∈ S := by
  exact (mem_cand.mp (best_mem_cand (cand_nonempty hA))).1

lemma best_subset_union {S : Finset (Finset α)} {U A : Finset α} (hA : A ∈ S) :
    best S U A ⊆ A ∪ U := by
  exact (mem_cand.mp (best_mem_cand (cand_nonempty hA))).2

lemma best_card_le {S : Finset (Finset α)} {U A A' : Finset α} (hA : A ∈ S)
    (hA' : A' ∈ S) (hsub : A' ⊆ A ∪ U) :
    (best S U A \ U).card ≤ (A' \ U).card := by
  exact (best_spec (S := S) (U := U) (A := A) (cand_nonempty hA)).2 A' (by
    simp [cand, hA', hsub])

/-- χ(A,U): the best remainder -/
noncomputable def chi (S : Finset (Finset α)) (U A : Finset α) : Finset α :=
  best S U A \ U

lemma chi_subset {S : Finset (Finset α)} {U A : Finset α} (hA : A ∈ S) : chi S U A ⊆ A := by
  intro x hx
  have hx' : x ∈ best S U A := (Finset.mem_sdiff.mp hx).1
  have hxnotU : x ∉ U := (Finset.mem_sdiff.mp hx).2
  have hxU : x ∈ A ∪ U := best_subset_union (S := S) (U := U) (A := A) hA hx'
  rcases Finset.mem_union.mp hxU with hxA | hxU2
  · exact hxA
  · exact False.elim (hxnotU hxU2)

lemma chi_sdiff_subset_best {S : Finset (Finset α)} (U A : Finset α) :
    chi S U A ⊆ best S U A := by
  intro x hx
  exact (Finset.mem_sdiff.mp hx).1

lemma chi_card_le {S : Finset (Finset α)} {U A A' : Finset α} (hA : A ∈ S)
    (hA' : A' ∈ S) (hsub : A' ⊆ A ∪ U) :
    (chi S U A).card ≤ (A' \ U).card := by
  simpa [chi] using best_card_le (S := S) (U := U) (A := A) (A' := A') hA hA' hsub

lemma chi_card_le_self {S : Finset (Finset α)} {U A : Finset α} (hA : A ∈ S) :
    (chi S U A).card ≤ (A \ U).card := by
  exact chi_card_le (S := S) (U := U) (A := A) (A' := A) hA hA Finset.subset_union_left

lemma chi_card_le_k {S : Finset (Finset α)} {U A : Finset α} {k : ℕ} (hA : A ∈ S)
    (hU : ∀ A' ∈ S, (A' \ U).card ≤ k) :
    (chi S U A).card ≤ k := by
  exact (le_trans (chi_card_le_self (S := S) (U := U) (A := A) hA) (hU A hA) : (chi S U A).card ≤ k)

lemma chi_eq_empty_iff {S : Finset (Finset α)} {U A : Finset α} (hA : A ∈ S) :
    chi S U A = ∅ ↔ ∃ A' ∈ S, A' ⊆ U := by
  constructor
  · intro hchi
    have hb : best S U A ⊆ U := by
      rw [← sdiff_eq_empty_iff_subset]
      exact hchi
    exact ⟨best S U A, best_mem (S := S) (U := U) (A := A) hA, hb⟩
  · rintro ⟨A', hA', hsub⟩
    have hle : (chi S U A).card ≤ (A' \ U).card := chi_card_le (S := S) (U := U) (A := A) (A' := A') hA hA' (by
      exact subset_trans hsub (subset_union_right (s₁ := A) (s₂ := U)))
    have hA'U : A' \ U = ∅ := by
      rw [sdiff_eq_empty_iff_subset]
      exact hsub
    have hle' : (chi S U A).card ≤ 0 := by simpa [hA'U] using hle
    have hc : (chi S U A).card = 0 := by omega
    exact Finset.card_eq_zero.mp hc

lemma chi_card_zero_iff {S : Finset (Finset α)} {U A : Finset α} (hA : A ∈ S) :
    (chi S U A).card = 0 ↔ ∃ A' ∈ S, A' ⊆ U := by
  exact (Finset.card_eq_zero.trans (chi_eq_empty_iff (S := S) (U := U) (A := A) hA))

/-- monotonicity in the second argument: `U ⊆ W` ⟹ `|χ(A,W)| ≤ |χ(A,U)|` -/
lemma chi_card_mono {S : Finset (Finset α)} {U W A : Finset α} (hA : A ∈ S) (hUW : U ⊆ W) :
    (chi S W A).card ≤ (chi S U A).card := by
  let B : Finset α := best S U A
  have hBmem : B ∈ S := best_mem (S := S) (U := U) (A := A) hA
  have hBsub : B ⊆ A ∪ U := best_subset_union (S := S) (U := U) (A := A) hA
  have hBW : (chi S W A).card ≤ (B \ W).card := by
    apply chi_card_le (S := S) (U := W) (A := A) (A' := B) hA hBmem
    exact subset_trans hBsub (union_subset_union_right (s := A) hUW)
  have hBcard : (B \ W).card ≤ (B \ U).card := by
    exact Finset.card_le_card (by intro x hx; simp at hx ⊢; exact ⟨hx.1, fun hU => hx.2 (hUW hU)⟩)
  simpa [chi, B] using le_trans hBW hBcard

end Submission.Sun
