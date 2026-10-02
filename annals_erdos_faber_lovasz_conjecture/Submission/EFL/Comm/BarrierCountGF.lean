import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.SetTheory.Cardinal.Finite

/-!
# The barrier count identity for the Erdős–Faber–Lovász proof

For a graph `G`, a spanning subgraph `R ≤ G`, finite vertex sets `X`, `Y`, and a
function `h : V → ℕ` such that every `y ∈ Y` has exactly `h y + 1` neighbours in `R`,
all of which lie in `X` (`hcl1`), and every `G`-neighbour of `x ∈ X` that is not an
`R`-neighbour lies in `Y` (`hcl2`), the number of adjacent ordered pairs `(y,x) ∈ Y × X`
equals

  `Σ_{y∈Y} (h y + 1) + Σ_{x∈X} (d_G x − h x) + Σ_{x∈X} (h x − d_R x)`.

The two `X`-sums telescope to `Σ_{x∈X} (d_G x − d_R x)`, and the resulting identity is
the statement that the `G`-edges between `X` and `Y` split into the `R`-edges between
them and the non-`R` `G`-edges incident to `X`.
-/

namespace Commons.Combinatorics.SimpleGraph

open Finset

/-- Row decomposition of a filtered product: the number of pairs `(x,y) ∈ s × t`
satisfying `P (x,y)` equals the sum over `x ∈ s` of the number of `y ∈ t` in the fibre. -/
private lemma card_filter_prod {α : Type*} (s t : Finset α) (P : α × α → Prop)
    [DecidablePred P] :
    ((s.product t).filter P).card = ∑ x ∈ s, (t.filter (fun y => P (x, y))).card := by
  classical
  rw [Finset.card_filter]
  rw [show (∑ i ∈ s.product t, (if P i then (1 : ℕ) else 0))
        = ∑ x ∈ s, ∑ y ∈ t, (if P (x, y) then 1 else 0) from Finset.sum_product s t _]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.card_filter]

/-- Swapping the two coordinates is a bijection between the adjacent pairs counted in
`A × B` and in `B × A`. -/
private lemma card_filter_product_swap {α β : Type*}
    (s : Finset α) (t : Finset β) (Q : α → β → Prop) (P : β → α → Prop)
    [∀ a, DecidablePred (Q a)] [DecidablePred (fun p : α × β => Q p.1 p.2)]
    [∀ b, DecidablePred (P b)] [DecidablePred (fun p : β × α => P p.1 p.2)]
    (h : ∀ a b, Q a b ↔ P b a) :
    ((s.product t).filter (fun p => Q p.1 p.2)).card
      = ((t.product s).filter (fun p => P p.1 p.2)).card := by
  apply Finset.card_bij (fun p _ => (p.2, p.1))
  · intro p hp
    rw [Finset.mem_filter] at hp
    have hp' := Finset.mem_product.mp hp.1
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_product.mpr ⟨hp'.2, hp'.1⟩, (h p.1 p.2).mp hp.2⟩
  · intro p1 _ p2 _ heq
    have h1 : p1.1 = p2.1 := by simpa using congrArg Prod.snd heq
    have h2 : p1.2 = p2.2 := by simpa using congrArg Prod.fst heq
    exact Prod.ext h1 h2
  · intro q hq
    rw [Finset.mem_filter] at hq
    have hq' := Finset.mem_product.mp hq.1
    refine ⟨(q.2, q.1), ?_, rfl⟩
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_product.mpr ⟨hq'.2, hq'.1⟩, (h q.2 q.1).mpr hq.2⟩

/-- The barrier count identity. -/
theorem barrier_count_gf {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (R : G.Subgraph) (X Y : Finset V) (h : V → ℕ)
    (hYsat : ∀ y ∈ Y, Nat.card {z : V // R.Adj y z} = h y + 1)
    (hcl1 : ∀ y ∈ Y, ∀ z : V, R.Adj y z → z ∈ X)
    (hcl2 : ∀ x ∈ X, ∀ z : V, G.Adj x z → ¬ R.Adj x z → z ∈ Y) :
    (((Y.product X).filter (fun p => G.Adj p.1 p.2)).card : ℤ)
      = Y.sum (fun y => ((h y : ℤ) + 1))
        + X.sum (fun x => ((Nat.card {w : V // G.Adj x w} : ℤ) - (h x : ℤ)))
        + X.sum (fun x => ((h x : ℤ) - (Nat.card {w : V // R.Adj x w} : ℤ))) := by
  classical
  have hGcard : ∀ x : V,
      Nat.card {w : V // G.Adj x w} = (Finset.univ.filter (fun w => G.Adj x w)).card := by
    intro x
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hRcard : ∀ x : V,
      Nat.card {w : V // R.Adj x w} = (Finset.univ.filter (fun w => R.Adj x w)).card := by
    intro x
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  set P := (Y.product X).filter (fun p => G.Adj p.1 p.2) with hPdef
  set Q := (Y.product X).filter (fun p => R.Adj p.1 p.2) with hQdef
  set S := (Y.product X).filter (fun p => G.Adj p.1 p.2 ∧ ¬ R.Adj p.1 p.2) with hSdef
  set S' := (X.product Y).filter (fun p => G.Adj p.1 p.2 ∧ ¬ R.Adj p.1 p.2) with hS'def
  have hdisj : Disjoint Q S := by
    rw [Finset.disjoint_left]
    intro p hp hq
    rw [hQdef] at hp; rw [hSdef] at hq
    simp only [Finset.mem_filter] at hp hq
    exact hq.2.2 hp.2
  have hPQS : P = Q ∪ S := by
    rw [hPdef, hQdef, hSdef]
    ext p
    simp only [Finset.mem_filter, Finset.mem_union]
    constructor
    · rintro ⟨hpY, hG⟩
      by_cases hR : R.Adj p.1 p.2
      · exact Or.inl ⟨hpY, hR⟩
      · exact Or.inr ⟨hpY, hG, hR⟩
    · rintro (⟨hpY, hR⟩ | ⟨hpY, hG, _⟩)
      · exact ⟨hpY, R.adj_sub hR⟩
      · exact ⟨hpY, hG⟩
  have hcardP : P.card = Q.card + S.card := by
    rw [hPQS, Finset.card_union_of_disjoint hdisj]
  have hQterm : ∀ y ∈ Y, (X.filter (fun z => R.Adj y z)).card = h y + 1 := by
    intro y hy
    have hf : X.filter (fun z => R.Adj y z) = Finset.univ.filter (fun w => R.Adj y w) := by
      apply Finset.Subset.antisymm
      · intro z hz; rw [Finset.mem_filter] at hz ⊢; exact ⟨Finset.mem_univ _, hz.2⟩
      · intro z hz; rw [Finset.mem_filter] at hz ⊢; exact ⟨hcl1 y hy z hz.2, hz.2⟩
    rw [hf, ← hRcard y, hYsat y hy]
  have hQcard : Q.card = ∑ y ∈ Y, (h y + 1) := by
    rw [hQdef, card_filter_prod]; exact Finset.sum_congr rfl hQterm
  have hsymm : ∀ a b : V, R.Adj a b ↔ R.Adj b a :=
    fun a b => ⟨fun hh => R.symm.symm a b hh, fun hh => R.symm.symm b a hh⟩
  have hSS' : S.card = S'.card := by
    rw [hSdef, hS'def]
    exact card_filter_product_swap Y X (fun y x => G.Adj y x ∧ ¬ R.Adj y x)
      (fun x y => G.Adj x y ∧ ¬ R.Adj x y)
      (fun y x => and_congr (G.adj_comm y x) (not_congr (hsymm y x)))
  have hS'sub : ∀ x : V,
      Finset.univ.filter (fun w => R.Adj x w) ⊆ Finset.univ.filter (fun w => G.Adj x w) := by
    intro x w hw
    rw [Finset.mem_filter] at hw ⊢
    exact ⟨Finset.mem_univ _, R.adj_sub hw.2⟩
  have hS'card : S'.card = ∑ x ∈ X,
      ((Finset.univ.filter (fun w => G.Adj x w)).card
        - (Finset.univ.filter (fun w => R.Adj x w)).card) := by
    rw [hS'def, card_filter_prod]
    apply Finset.sum_congr rfl
    intro x hx
    have heq : Y.filter (fun y => G.Adj x y ∧ ¬ R.Adj x y)
        = (Finset.univ.filter (fun w => G.Adj x w))
          \ (Finset.univ.filter (fun w => R.Adj x w)) := by
      ext y
      simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨hy, hG, hnR⟩; exact ⟨hG, hnR⟩
      · rintro ⟨hG, hnR⟩; exact ⟨hcl2 x hx y hG hnR, hG, hnR⟩
    rw [heq, Finset.card_sdiff_of_subset (hS'sub x)]
  have hScardZ : (S.card : ℤ) = X.sum (fun x =>
      ((Nat.card {w : V // G.Adj x w} : ℤ) - (Nat.card {w : V // R.Adj x w} : ℤ))) := by
    rw [hSS', hS'card, Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro x hx
    rw [Nat.cast_sub (Finset.card_le_card (hS'sub x)), ← hGcard x, ← hRcard x]
  have hQZ : (Q.card : ℤ) = Y.sum (fun y => (h y : ℤ) + 1) := by
    rw [hQcard, Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro y _
    rw [Nat.cast_add, Nat.cast_one]
  have hcombine : X.sum (fun x => ((Nat.card {w : V // G.Adj x w} : ℤ) - (h x : ℤ)))
      + X.sum (fun x => ((h x : ℤ) - (Nat.card {w : V // R.Adj x w} : ℤ)))
      = X.sum (fun x =>
          ((Nat.card {w : V // G.Adj x w} : ℤ) - (Nat.card {w : V // R.Adj x w} : ℤ))) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x _
    exact sub_add_sub_cancel _ _ _
  have hPZ : (P.card : ℤ) = (Q.card : ℤ) + (S.card : ℤ) := by rw [hcardP, Nat.cast_add]
  rw [hPZ, hQZ, hScardZ]
  rw [add_assoc, hcombine]

end Commons.Combinatorics.SimpleGraph