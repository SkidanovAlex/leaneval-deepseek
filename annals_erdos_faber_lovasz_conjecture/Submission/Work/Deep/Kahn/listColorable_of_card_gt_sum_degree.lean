import Submission.Work.ConeSwitch.MathlibNoHG
import Submission.Work.Deep.Kahn.Defs
import Submission.Work.Deep.Kahn.card_intersecting_le
import Submission.Work.Deep.Kahn.listColorable_of_deleted_edge

/-!
# Greedy list edge-colouring of a hypergraph

A hypergraph whose every edge `e` has a list `L e` of more than
`∑_{v ∈ e} (d(v) − 1)` colours admits a proper edge colouring respecting the
lists.  This is the elementary greedy bound: every edge `e` meets at most
`∑_{v ∈ e} (d(v) − 1)` other edges (each other edge through a vertex `v` of
`e` is counted by `v`), so one of the colours of `L e` is unused on the
neighbours of `e`.

The proof is an induction on the number of edges.  Deleting an edge `e₀`
leaves a hypergraph `𝓗 \ {e₀}` with strictly fewer edges and weakly smaller
degrees, so the hypothesis is inherited (`hypergraphDegree_mono`) and the
induction hypothesis colours `𝓗 \ {e₀}`.  The free colour for `e₀` exists by
`card_intersecting_le`, which counts the neighbours of `e₀` by the degree
sum, and `listColorable_of_deleted_edge` performs the one-edge extension.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace Work.Deep.Kahn

open ErdosFaberLovaszConjecture

/-- **Greedy list edge-colouring, induction on the number of edges.**

If every edge `e` of `𝓗` has more than `∑_{v ∈ e} (d(v) − 1)` colours
available in its list `L e`, then `𝓗` admits a proper edge colouring
respecting `L`, provided `𝓗` has at most `k` edges. -/
private theorem listColorable_aux {n : ℕ} {α : Type*} :
    ∀ (k : ℕ) (𝓗 : ErdosFaberLovaszConjecture.Hypergraph (Fin n)) (L : 𝓗 → Finset α),
      Nat.card 𝓗 ≤ k →
      (∀ e : 𝓗, (∑ v ∈ ErdosFaberLovaszConjecture.verts (e : Set (Fin n)),
        (ErdosFaberLovaszConjecture.hypergraphDegree 𝓗 v - 1)) < (L e).card) →
      ErdosFaberLovaszConjecture.Hypergraph.ListColorable L := by
  intro k
  induction k with
  | zero =>
    -- `𝓗` has no edges: the empty colouring works
    intro 𝓗 L hk _
    haveI : IsEmpty 𝓗 := (Finite.card_eq_zero_iff.mp (Nat.le_zero.mp hk))
    exact ⟨⟨fun e => (IsEmpty.false e).elim, fun e₁ _ _ => (IsEmpty.false e₁).elim⟩,
      fun e => (IsEmpty.false e).elim⟩
  | succ k ih =>
    intro 𝓗 L hk h
    by_cases hk' : Nat.card 𝓗 ≤ k
    · -- fewer than `k + 1` edges: apply the induction hypothesis directly
      exact ih 𝓗 L hk' h
    · -- `𝓗` has exactly `k + 1` edges: delete one edge and extend
      have hpos : 0 < Nat.card 𝓗 := by omega
      obtain ⟨e₀⟩ : Nonempty 𝓗 := (Nat.card_pos_iff.mp hpos).1
      set s₀ : Set (Fin n) := (e₀ : Set (Fin n)) with hs₀
      have hsub : ErdosFaberLovaszConjecture.Hypergraph.edgeDiff 𝓗 {s₀} ⊆ 𝓗 :=
        Set.sdiff_subset
      -- the hypergraph with `e₀` deleted is strictly smaller
      have hcardlt : Nat.card ↥(ErdosFaberLovaszConjecture.Hypergraph.edgeDiff 𝓗 {s₀})
          < Nat.card 𝓗 := by
        have h1 : Nat.card ↥(ErdosFaberLovaszConjecture.Hypergraph.edgeDiff 𝓗 {s₀})
            = (𝓗 \ {s₀}).ncard := Nat.card_coe_set_eq _
        have h2 : Nat.card 𝓗 = 𝓗.ncard := Nat.card_coe_set_eq _
        rw [h1, h2, Set.ncard_sdiff (Set.singleton_subset_iff.mpr e₀.2), Set.ncard_singleton]
        omega
      -- the lists restricted to the smaller hypergraph
      let L' : ↥(ErdosFaberLovaszConjecture.Hypergraph.edgeDiff 𝓗 {s₀}) → Finset α :=
        fun f => L ⟨(f : Set (Fin n)), f.2.1⟩
      -- the hypothesis is inherited: degrees only decrease
      have hL' : ∀ f : ↥(ErdosFaberLovaszConjecture.Hypergraph.edgeDiff 𝓗 {s₀}),
          (∑ v ∈ ErdosFaberLovaszConjecture.verts (f : Set (Fin n)),
            (ErdosFaberLovaszConjecture.hypergraphDegree
              (ErdosFaberLovaszConjecture.Hypergraph.edgeDiff 𝓗 {s₀}) v - 1))
            < (L' f).card := by
        intro f
        have hsum : (∑ v ∈ ErdosFaberLovaszConjecture.verts (f : Set (Fin n)),
              (ErdosFaberLovaszConjecture.hypergraphDegree
                (ErdosFaberLovaszConjecture.Hypergraph.edgeDiff 𝓗 {s₀}) v - 1))
            ≤ (∑ v ∈ ErdosFaberLovaszConjecture.verts (f : Set (Fin n)),
              (ErdosFaberLovaszConjecture.hypergraphDegree 𝓗 v - 1)) := by
          refine Finset.sum_le_sum (fun v _ => ?_)
          have := ErdosFaberLovaszConjecture.hypergraphDegree_mono hsub v
          omega
        exact lt_of_le_of_lt hsum (h ⟨(f : Set (Fin n)), f.2.1⟩)
      obtain ⟨χ, hχ⟩ := ih (ErdosFaberLovaszConjecture.Hypergraph.edgeDiff 𝓗 {s₀}) L'
        (by omega) hL'
      -- the number of edges meeting `e₀` is smaller than `|L e₀|`
      have hcount : Nat.card
          {f : 𝓗 // f ≠ e₀ ∧ ((f : Set (Fin n)) ∩ (e₀ : Set (Fin n))).Nonempty}
          < (L e₀).card := lt_of_le_of_lt (card_intersecting_le e₀) (h e₀)
      exact listColorable_of_deleted_edge 𝓗 e₀ L hcount χ hχ

/-- **Greedy list edge-colouring.**  A hypergraph on `Fin n` whose every edge
`e` has a list `L e` of more than `∑_{v ∈ e} (deg v − 1)` colours admits a
proper edge colouring respecting the lists `L`. -/
theorem listColorable_of_card_gt_sum_degree {n : ℕ} {α : Type*}
    (𝓗 : ErdosFaberLovaszConjecture.Hypergraph (Fin n)) [Fintype 𝓗] (L : 𝓗 → Finset α)
    (h : ∀ e : 𝓗, (∑ v ∈ ErdosFaberLovaszConjecture.verts (e : Set (Fin n)),
        (ErdosFaberLovaszConjecture.hypergraphDegree 𝓗 v - 1)) < (L e).card) :
    ErdosFaberLovaszConjecture.Hypergraph.ListColorable L :=
  listColorable_aux (Fintype.card 𝓗) 𝓗 L (le_of_eq Nat.card_eq_fintype_card) h

end Work.Deep.Kahn
