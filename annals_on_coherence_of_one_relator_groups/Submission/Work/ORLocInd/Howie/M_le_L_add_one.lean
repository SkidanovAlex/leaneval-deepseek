/-
# `M(∆) ≤ L(∆) + 1` for a Howie datum

This file proves the auxiliary inequality `D.M ≤ D.L + 1` for a `Datum` of a groupoid
presentation (Howie 2000, proof of Theorem 3.1).  It is the inequality that makes the truncated
subtraction in `Datum.measure = 2 * L + 2 - M` exact.

The proof is a counting argument.  The vertices visited by the datum are the union of the vertex
sets of the paths `γ_j`, of the paths `δ` of the terms and of the relator paths of the terms.  Each
of these paths is attached to an already-counted vertex:

* every `γ_j` is a closed path at `v`;
* every `δ` starts at `v`;
* the relator path of a term starts at the endpoint of `δ` (which was counted together with `δ`).

Hence, processing the paths in that order, each path of length `ℓ` contributes at most `ℓ` *new*
vertices, while `L(∆)` is exactly the sum of the lengths; so `M(∆) ≤ 1 + L(∆)`.
-/
import Mathlib
import Submission.Work.ORLocInd.Howie.Datum

set_option autoImplicit false

universe u

namespace Work.ORLocInd.Howie

open Quiver

section Aux

/-- Cardinality of a union with a `biUnion`: the elements already in `s` are charged to `s`, and
everything else of `f b` is charged to `f b \ s`. -/
theorem card_union_biUnion_le {α β : Type*} [DecidableEq α] [DecidableEq β]
    (s : Finset α) (t : Finset β) (f : β → Finset α) :
    (s ∪ t.biUnion f).card ≤ s.card + ∑ b ∈ t, ((f b) \ s).card := by
  have hsub : s ∪ t.biUnion f ⊆ s ∪ t.biUnion (fun b => (f b) \ s) := by
    intro x hx
    by_cases hxs : x ∈ s
    · exact Finset.mem_union.mpr (Or.inl hxs)
    · refine Finset.mem_union.mpr (Or.inr ?_)
      rw [Finset.mem_union] at hx
      rcases hx with h | h
      · exact absurd h hxs
      · rw [Finset.mem_biUnion] at h ⊢
        obtain ⟨b, hb, hxb⟩ := h
        exact ⟨b, hb, Finset.mem_sdiff.mpr ⟨hxb, hxs⟩⟩
  calc (s ∪ t.biUnion f).card
      ≤ (s ∪ t.biUnion (fun b => (f b) \ s)).card := Finset.card_le_card hsub
    _ ≤ s.card + (t.biUnion (fun b => (f b) \ s)).card := Finset.card_union_le _ _
    _ ≤ s.card + ∑ b ∈ t, ((f b) \ s).card := by
        have h := Finset.card_biUnion_le (s := t) (t := fun b => (f b) \ s)
        omega

/-- A path of length `ℓ` whose initial vertex already lies in `s` contributes at most `ℓ` vertices
outside `s`. -/
theorem path_vertices_sdiff_card_le {V : Type u} [Quiver V] [DecidableEq V] {a b : V}
    (p : Quiver.Path a b) (s : Finset V) (ha : a ∈ s) :
    (p.vertices.toFinset \ s).card ≤ p.length := by
  have hmem : a ∈ p.vertices := by
    induction p with
    | nil => simp
    | cons p e ih =>
        rw [Quiver.Path.vertices_cons, List.concat_eq_append]
        exact List.mem_append_left _ ih
  have hsub : p.vertices.toFinset \ s ⊆ p.vertices.toFinset.erase a := by
    intro x hx
    rw [Finset.mem_sdiff] at hx
    simp only [Finset.mem_erase]
    exact ⟨fun hxa => hx.2 (by rw [hxa]; exact ha), hx.1⟩
  have h1 : (p.vertices.toFinset \ s).card ≤ (p.vertices.toFinset.erase a).card :=
    Finset.card_le_card hsub
  have h2 : (p.vertices.toFinset.erase a).card = (p.vertices.toFinset).card - 1 :=
    Finset.card_erase_of_mem (by simpa using hmem)
  have h3 : (p.vertices.toFinset).card ≤ p.vertices.length := List.toFinset_card_le _
  have h4 : p.vertices.length = p.length + 1 := Quiver.Path.vertices_length p
  omega

/-- The endpoint of a path belongs to its vertex list. -/
theorem mem_vertices_getLast {V : Type u} [Quiver V] {a b : V} (p : Quiver.Path a b) :
    b ∈ p.vertices := by
  induction p with
  | nil => simp
  | cons p e ih =>
      rw [Quiver.Path.vertices_cons, List.concat_eq_append]
      exact List.mem_append_right _ (List.mem_singleton_self _)

/-- The sum over the distinct elements of a list is at most the sum with multiplicities (for
non-negative values). -/
theorem sum_toFinset_le {α : Type*} [DecidableEq α] (l : List α) (f : α → ℕ) :
    l.toFinset.sum f ≤ (l.map f).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    by_cases h : a ∈ l
    · rw [List.toFinset_cons, Finset.insert_eq_of_mem (by simpa using h)]
      rw [List.map_cons, List.sum_cons]
      exact le_trans ih (Nat.le_add_left _ _)
    · rw [List.toFinset_cons, Finset.sum_insert (by simpa using h)]
      rw [List.map_cons, List.sum_cons]
      exact Nat.add_le_add_left ih _

/-- Distributing a set difference over a `biUnion`. -/
theorem biUnion_sdiff_subset {α β : Type*} [DecidableEq α] (A : Finset β) (g : β → Finset α)
    (s : Finset α) : A.biUnion g \ s ⊆ A.biUnion (fun a => g a \ s) := by
  intro x hx
  rw [Finset.mem_sdiff, Finset.mem_biUnion] at hx
  obtain ⟨⟨a, ha, hxa⟩, hxs⟩ := hx
  exact Finset.mem_biUnion.mpr ⟨a, ha, Finset.mem_sdiff.mpr ⟨hxa, hxs⟩⟩

/-- `toFinset` of a `flatMap` is the `biUnion` of the `toFinset`s. -/
theorem toFinset_flatMap {α β : Type*} [DecidableEq α] [DecidableEq β]
    (l : List α) (f : α → List β) :
    (l.flatMap f).toFinset = l.toFinset.biUnion (fun a => (f a).toFinset) := by
  induction l with
  | nil => simp
  | cons a l ih =>
      rw [List.flatMap_cons, List.toFinset_append, ih, List.toFinset_cons, Finset.biUnion_insert]

end Aux

theorem M_le_L_add_one {V : Type u} [Quiver V] [Quiver.HasInvolutiveReverse V] [DecidableEq V]
    {P : Work.ORLocInd.Howie.Presentation V} {v : V} {n : ℕ}
    (D : Work.ORLocInd.Howie.Datum P v n) :
    D.M ≤ D.L + 1 := by
  classical
  set G : Finset V := Finset.univ.biUnion (fun j : Fin n => ((D.γ j).1.vertices).toFinset) with hG
  set Ds : Finset V := Finset.univ.biUnion (fun j : Fin n =>
      (D.terms j).toFinset.biUnion (fun t : RelatorTerm P v => t.δ.vertices.toFinset)) with hDs
  set Rs : Finset V := Finset.univ.biUnion (fun j : Fin n =>
      (D.terms j).toFinset.biUnion (fun t : RelatorTerm P v => (P.path t.i).vertices.toFinset))
    with hRs
  -- the visited vertices are exactly the base vertex together with the vertices of all paths
  have hA : D.visitedList.toFinset = insert v (G ∪ Ds ∪ Rs) := by
    rw [hG, hDs, hRs]
    simp only [Datum.visitedList, List.toFinset_append, List.toFinset_cons, List.toFinset_nil,
      List.toFinset_finRange, toFinset_flatMap, Finset.biUnion_union, RelatorTerm.visitedList]
    ext x
    simp only [Finset.mem_union, Finset.mem_insert, Finset.notMem_empty, or_false]
    tauto
  -- the `γ_j`
  have hS1 : (insert v G).card ≤ 1 + ∑ j : Fin n, ((D.γ j).1).length := by
    rw [Finset.insert_eq]
    have h := card_union_biUnion_le ({v} : Finset V) (Finset.univ : Finset (Fin n))
      (fun j : Fin n => ((D.γ j).1.vertices).toFinset)
    rw [Finset.card_singleton, ← hG] at h
    refine le_trans h (add_le_add_right ?_ 1)
    refine Finset.sum_le_sum (fun j _ => ?_)
    exact path_vertices_sdiff_card_le ((D.γ j).1) {v} (Finset.mem_singleton_self v)
  -- the `δ` of the terms
  have hS2 : (insert v (G ∪ Ds)).card ≤ (insert v G).card +
      ∑ j : Fin n, ∑ t ∈ (D.terms j).toFinset, t.δ.length := by
    rw [← Finset.insert_union]
    have h := card_union_biUnion_le (insert v G) (Finset.univ : Finset (Fin n))
      (fun j : Fin n =>
        (D.terms j).toFinset.biUnion (fun t : RelatorTerm P v => t.δ.vertices.toFinset))
    rw [← hDs] at h
    refine le_trans h (add_le_add_right ?_ _)
    refine Finset.sum_le_sum (fun j _ => ?_)
    refine le_trans (Finset.card_le_card (biUnion_sdiff_subset _ _ _)) ?_
    refine le_trans Finset.card_biUnion_le ?_
    refine Finset.sum_le_sum (fun t _ => ?_)
    exact path_vertices_sdiff_card_le t.δ (insert v G) (Finset.mem_insert_self v G)
  -- the relator paths of the terms
  have hS3 : (insert v (G ∪ Ds) ∪ Rs).card ≤ (insert v (G ∪ Ds)).card +
      ∑ j : Fin n, ∑ t ∈ (D.terms j).toFinset, (P.path t.i).length := by
    have h := card_union_biUnion_le (insert v (G ∪ Ds)) (Finset.univ : Finset (Fin n))
      (fun j : Fin n =>
        (D.terms j).toFinset.biUnion (fun t : RelatorTerm P v => (P.path t.i).vertices.toFinset))
    rw [← hRs] at h
    refine le_trans h (add_le_add_right ?_ _)
    refine Finset.sum_le_sum (fun j _ => ?_)
    refine le_trans (Finset.card_le_card (biUnion_sdiff_subset _ _ _)) ?_
    refine le_trans Finset.card_biUnion_le ?_
    refine Finset.sum_le_sum (fun t ht => ?_)
    refine path_vertices_sdiff_card_le (P.path t.i) (insert v (G ∪ Ds)) ?_
    refine Finset.mem_insert.mpr (Or.inr ?_)
    refine Finset.mem_union.mpr (Or.inr ?_)
    rw [hDs]
    exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ j, Finset.mem_biUnion.mpr ⟨t, ht, by
      rw [List.mem_toFinset]; exact mem_vertices_getLast t.δ⟩⟩
  have hM : D.M = D.visitedList.toFinset.card := by
    rw [Datum.M]
    exact (List.card_toFinset _).symm
  have hsum : (∑ j : Fin n, ∑ t ∈ (D.terms j).toFinset, t.δ.length)
        + (∑ j : Fin n, ∑ t ∈ (D.terms j).toFinset, (P.path t.i).length)
      ≤ ∑ j : Fin n, ((D.terms j).map RelatorTerm.weight).sum := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum (fun j _ => ?_)
    rw [← Finset.sum_add_distrib]
    exact sum_toFinset_le (D.terms j) RelatorTerm.weight
  rw [hM, hA, ← Finset.insert_union, Datum.L]
  omega

end Work.ORLocInd.Howie
