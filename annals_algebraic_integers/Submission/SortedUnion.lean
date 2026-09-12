import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Multiset.Sort
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Data.Finset.Sort

noncomputable section

open scoped Real BigOperators
open Polynomial

namespace Submission.SortedUnion

theorem sorted_union {N M : ℕ} (γ : Fin N → ℝ) (β : Fin M → ℝ)
    (hγ : ∀ i j : Fin N, i.val < j.val → γ i < γ j)
    (hβ : ∀ i j : Fin M, i.val < j.val → β i < β j)
    (hdisj : ∀ i : Fin N, ∀ j : Fin M, γ i ≠ β j) :
    ∃ α : Fin (N + M) → ℝ,
      (∀ i j : Fin (N + M), i.val < j.val → α i < α j) ∧
      (∀ i : Fin (N + M),
        (∃ k : Fin N, α i = γ k) ∨ (∃ l : Fin M, α i = β l)) ∧
      (∏ k : Fin N, (Polynomial.X - Polynomial.C (γ k))) *
          (∏ l : Fin M, (Polynomial.X - Polynomial.C (β l))) =
        ∏ i : Fin (N + M), (Polynomial.X - Polynomial.C (α i)) := by
  classical
  set gγ : Finset ℝ := Finset.image γ (Finset.univ : Finset (Fin N)) with hgγdef
  set gβ : Finset ℝ := Finset.image β (Finset.univ : Finset (Fin M)) with hgβdef
  set S : Finset ℝ := gγ ∪ gβ with hSdef
  have hinjγ : Function.Injective γ := by
    intro i j hij
    by_contra hne
    have hvalne : i.val ≠ j.val := by
      intro hv
      exact hne (Fin.ext hv)
    rcases lt_or_gt_of_ne hvalne with hlt | hgt
    · have hltc : γ i < γ j := hγ i j hlt
      exact (ne_of_lt hltc) hij
    · have hgtc : γ j < γ i := hγ j i hgt
      exact (ne_of_lt hgtc) hij.symm
  have hinjβ : Function.Injective β := by
    intro i j hij
    by_contra hne
    have hvalne : i.val ≠ j.val := by
      intro hv
      exact hne (Fin.ext hv)
    rcases lt_or_gt_of_ne hvalne with hlt | hgt
    · have hltc : β i < β j := hβ i j hlt
      exact (ne_of_lt hltc) hij
    · have hgtc : β j < β i := hβ j i hgt
      exact (ne_of_lt hgtc) hij.symm
  have hdis : Disjoint gγ gβ := by
    rw [Finset.disjoint_left, hgγdef, hgβdef]
    intro x hx1 hx2
    rw [Finset.mem_image] at hx1 hx2
    rcases hx1 with ⟨k, hk₁, hk₂⟩
    rcases hx2 with ⟨l, hl₁, hl₂⟩
    exact hdisj k l (hk₂.trans hl₂.symm)
  have hcardγ : gγ.card = N := by
    rw [hgγdef, Finset.card_image_of_injective (Finset.univ : Finset (Fin N)) hinjγ]
    simp
  have hcardβ : gβ.card = M := by
    rw [hgβdef, Finset.card_image_of_injective (Finset.univ : Finset (Fin M)) hinjβ]
    simp
  have hcardS : S.card = N + M := by
    rw [hSdef, Finset.card_union_of_disjoint hdis, hcardγ, hcardβ]
  let emb : Fin (N + M) ↪o ℝ := S.orderEmbOfFin hcardS
  let α : Fin (N + M) → ℝ := emb
  refine ⟨α, ?_, ?_, ?_⟩
  · intro i j hij
    have hijlt : i < j := hij
    have : emb i < emb j := (OrderEmbedding.lt_iff_lt emb).2 hijlt
    simpa [α] using this
  · intro i
    have hi : emb i ∈ S := Finset.orderEmbOfFin_mem S hcardS i
    have hmem : α i ∈ gγ ∪ gβ := by
      simpa [α, hSdef] using hi
    rw [Finset.mem_union] at hmem
    rcases hmem with hmemγ | hmemβ
    · left
      rw [Finset.mem_image] at hmemγ
      rcases hmemγ with ⟨k, hk₁, hk₂⟩
      refine ⟨k, hk₂.symm⟩
    · right
      rw [Finset.mem_image] at hmemβ
      rcases hmemβ with ⟨l, hl₁, hl₂⟩
      refine ⟨l, hl₂.symm⟩
  · let f : ℝ → Polynomial ℝ := fun x => Polynomial.X - Polynomial.C x
    have hprodS : (∏ x ∈ S, f x) = ∏ i : Fin (N + M), f (α i) := by
      calc
        (∏ x ∈ S, f x) = ∏ x ∈ Finset.image emb Finset.univ, f x := by
          rw [Finset.image_orderEmbOfFin_univ S hcardS]
        _ = ∏ x ∈ Finset.univ, f (emb x) := by
          rw [Finset.prod_image (by
            intro x hx y hy hxy
            exact (RelEmbedding.injective emb) hxy)]
        _ = ∏ i : Fin (N + M), f (emb i) := by
          rfl
        _ = ∏ i : Fin (N + M), f (α i) := by
          simp [α]
    have hsplit : (∏ x ∈ S, f x) =
        (∏ k : Fin N, f (γ k)) * (∏ l : Fin M, f (β l)) := by
      calc
        (∏ x ∈ S, f x) = ∏ x ∈ gγ ∪ gβ, f x := by rw [hSdef]
        _ = (∏ x ∈ gγ, f x) * (∏ x ∈ gβ, f x) := by
          rw [Finset.prod_union hdis]
        _ = (∏ x ∈ Finset.image γ (Finset.univ : Finset (Fin N)), f x) *
            (∏ x ∈ Finset.image β (Finset.univ : Finset (Fin M)), f x) := by
          rw [hgγdef, hgβdef]
        _ = (∏ k : Fin N, f (γ k)) * (∏ l : Fin M, f (β l)) := by
          congr 1
          · rw [Finset.prod_image (by
              intro x hx y hy hxy
              exact hinjγ hxy)]
          · rw [Finset.prod_image (by
              intro x hx y hy hxy
              exact hinjβ hxy)]
    calc
      (∏ k : Fin N, (Polynomial.X - Polynomial.C (γ k))) *
          (∏ l : Fin M, (Polynomial.X - Polynomial.C (β l))) =
          (∏ k : Fin N, f (γ k)) * (∏ l : Fin M, f (β l)) := by
        simp [f]
      _ = ∏ x ∈ S, f x := hsplit.symm
      _ = ∏ i : Fin (N + M), f (α i) := hprodS
      _ = ∏ i : Fin (N + M), (Polynomial.X - Polynomial.C (α i)) := by
        simp [f]

end Submission.SortedUnion
