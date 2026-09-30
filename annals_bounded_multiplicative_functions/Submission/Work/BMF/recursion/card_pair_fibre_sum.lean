import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.recursion

/-- **Fibre decomposition of a pair count.**  For a map `f : α → β` between finite types and
subsets `A B ⊆ α`, the number of pairs `(x,y) ∈ A × B` with `f x = f y` is the sum over the fibres
of `f` of the products `#(A ∩ f⁻¹ v) · #(B ∩ f⁻¹ v)`.

This is the elementary "Cauchy–Schwarz over the fibres" identity (with `A = B` it computes
`Σ_v #(A ∩ f⁻¹v)²`).  Proof: the pairs with `f x = f y` split into the disjoint union over
`v ∈ univ.image f` of `(A ∩ f⁻¹v) × (B ∩ f⁻¹v)`, so the cardinality is the sum of the products;
use `Finset.card_biUnion`/`Finset.card_product` and `Finset.mem_image`. -/
theorem card_pair_fibre_sum {α β : Type} [Fintype α] [DecidableEq α] [DecidableEq β]
    (f : α → β) (A B : Finset α) :
    (((Finset.univ : Finset (α × α)).filter
        (fun p => f p.1 = f p.2 ∧ p.1 ∈ A ∧ p.2 ∈ B)).card : ℝ)
      = ∑ v ∈ Finset.univ.image f,
          (((A.filter (fun x => f x = v)).card : ℝ) * ((B.filter (fun x => f x = v)).card : ℝ)) := by
  set S := (Finset.univ : Finset (α × α)).filter
    (fun p => f p.1 = f p.2 ∧ p.1 ∈ A ∧ p.2 ∈ B) with hSdef
  set g : β → Finset (α × α) :=
    fun v => (A.filter (fun x => f x = v)) ×ˢ (B.filter (fun x => f x = v)) with hgdef
  -- The filtered set of pairs is the disjoint union over the fibres of `f`.
  have hSu : S = (Finset.univ.image f).biUnion g := by
    ext p
    simp only [hSdef, hgdef, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion,
      Finset.mem_image, Finset.mem_product]
    constructor
    · rintro ⟨hfeq, hA, hB⟩
      exact ⟨f p.1, ⟨p.1, rfl⟩, ⟨hA, rfl⟩, ⟨hB, hfeq.symm⟩⟩
    · rintro ⟨v, ⟨w, rfl⟩, ⟨hA, hfv⟩, ⟨hB, hgv⟩⟩
      exact ⟨hfv.trans hgv.symm, hA, hB⟩
  -- Distinct fibres give disjoint pieces (a pair in the piece of `v` has `f p.1 = v`).
  have hdisj : (↑(Finset.univ.image f) : Set β).PairwiseDisjoint g := by
    intro a _ b _ hab
    change Disjoint (g a) (g b)
    rw [Finset.disjoint_left]
    intro x hxa hxb
    simp only [hgdef, Finset.mem_product, Finset.mem_filter] at hxa hxb
    exact hab (hxa.1.2.symm.trans hxb.1.2)
  have hmain : S.card = ∑ v ∈ Finset.univ.image f,
      (A.filter (fun x => f x = v)).card * (B.filter (fun x => f x = v)).card := by
    rw [hSu, Finset.card_biUnion hdisj]
    refine Finset.sum_congr rfl ?_
    intro v _
    simp only [hgdef, Finset.card_product]
  rw [hmain]
  push_cast
  rfl

end Work.BMF.recursion
