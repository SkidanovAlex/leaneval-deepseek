import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.ZMod.Defs
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.Preorder.Finite
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.TypeStar

/-!
# A maximal pairwise-disjoint pairing in a finite hypergraph

Given a hypergraph `𝓗` on the finite vertex set `Fin n`, there is a maximal family of
pairwise disjoint pairs `{e, f}` of hyperedges with `e ∩ f = ∅`: a family of such pairs
which is maximal with respect to the property that no further pair can be added.

This is the statement that the *disjointness graph* on the hyperedges (with an edge between
two distinct hyperedges whenever they are disjoint as vertex sets) admits a maximal matching.
The proof below establishes the more general fact that every finite relation graph admits a
maximal matching (`exists_maximal_rel_matching`), encoded through functions
`Fin t → Fin 2 → V`, and then specialises it to the hypergraph setting.
-/

set_option autoImplicit false

namespace Commons.Combinatorics.Hypergraph

open Classical

/-- The `b`-th endpoint of an ordered pair `p` (`b = 0` the first coordinate, `b = 1` the second). -/
def pairVal {V : Type*} (p : V × V) : Fin 2 → V := ![p.1, p.2]

@[simp] lemma pairVal_zero {V : Type*} (p : V × V) : pairVal p 0 = p.1 := by
  simp [pairVal]

@[simp] lemma pairVal_one {V : Type*} (p : V × V) : pairVal p 1 = p.2 := by
  simp [pairVal]

lemma pairVal_mem {V : Type*} (p : V × V) (b : Fin 2) :
    pairVal p b ∈ ({(p.1 : V), p.2} : Set V) := by
  fin_cases b <;> simp [pairVal]

/-- A finite set `P` of ordered pairs is a matching for the relation `R` if its members are
`R`-related and the endpoints of distinct members are pairwise distinct. -/
def RelMatching {V : Type*} (R : V → V → Prop) (P : Finset (V × V)) : Prop :=
  (∀ p ∈ P, R p.1 p.2) ∧
  (∀ p ∈ P, ∀ q ∈ P, ∀ a b : Fin 2, pairVal p a = pairVal q b → p = q ∧ a = b)

/-- Every finite relation graph has a maximal matching, presented as a partial pairing
`σ : Fin t → Fin 2 → V` whose `t` pairs are `R`-related and whose `2t` endpoints are distinct,
and which is maximal: any two distinct vertices outside the range are not `R`-related. -/
theorem exists_maximal_rel_matching {V : Type*} [Fintype V] [DecidableEq V]
    (R : V → V → Prop) [DecidableRel R] :
    ∃ (t : ℕ) (σ : Fin t → Fin 2 → V),
      Function.Injective (fun p : Fin t × Fin 2 => σ p.1 p.2) ∧
      (∀ i, R (σ i 0) (σ i 1)) ∧
      (∀ x y, x ∉ Set.range (fun p : Fin t × Fin 2 => σ p.1 p.2) →
              y ∉ Set.range (fun p : Fin t × Fin 2 => σ p.1 p.2) → x ≠ y → ¬ R x y) := by
  classical
  -- A maximal finite set of pairwise compatible pairs.
  obtain ⟨P, hPmax⟩ := Finset.exists_maximal
      (s := Finset.univ.filter (RelMatching R))
      (by
        refine ⟨∅, ?_⟩
        rw [Finset.mem_filter]
        exact ⟨Finset.mem_univ _, by simp [RelMatching]⟩)
  have hPgood : RelMatching R P := (Finset.mem_filter.mp hPmax.1).2
  -- `e` enumerates the pairs of `P` and `σ` reads off their endpoints.
  let e : Fin P.card ≃ ↥P := P.equivFin.symm
  let σ : Fin P.card → Fin 2 → V := fun i b => pairVal ((e i).val) b
  have hσinj : Function.Injective (fun p : Fin P.card × Fin 2 => σ p.1 p.2) := by
    rintro ⟨i, a⟩ ⟨j, b⟩ hab
    simp only [Prod.mk.injEq]
    have h1 : pairVal ((e i).val) a = pairVal ((e j).val) b := hab
    have h2 := hPgood.2 ((e i).val) (e i).property ((e j).val) (e j).property a b h1
    have heq : e i = e j := Subtype.ext h2.1
    exact ⟨e.injective heq, h2.2⟩
  have hσR : ∀ i, R (σ i 0) (σ i 1) := by
    intro i
    have h := hPgood.1 ((e i).val) (e i).property
    simpa [σ, pairVal] using h
  have hrange_fwd : ∀ p ∈ P, p.1 ∈ Set.range (fun p : Fin P.card × Fin 2 => σ p.1 p.2) ∧
      p.2 ∈ Set.range (fun p : Fin P.card × Fin 2 => σ p.1 p.2) := by
    intro p hp
    obtain ⟨i, hi⟩ := e.surjective ⟨p, hp⟩
    refine ⟨⟨(i, 0), ?_⟩, ⟨(i, 1), ?_⟩⟩ <;> simp [σ, pairVal, hi]
  refine ⟨P.card, σ, hσinj, hσR, ?_⟩
  intro x y hx hy hxy hRxy
  -- Neither `x` nor `y` is an endpoint of a pair of `P`.
  have hnew_notin : ∀ a : Fin 2, pairVal (x, y) a ∉
      Set.range (fun p : Fin P.card × Fin 2 => σ p.1 p.2) := by
    intro a
    have h := pairVal_mem (x, y) a
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
    rcases h with h | h
    · rw [h]; exact hx
    · rw [h]; exact hy
  -- Adding the pair `(x, y)` to `P` keeps it a matching.
  have hgood' : RelMatching R (insert (x, y) P) := by
    constructor
    · intro p hp
      rcases Finset.mem_insert.mp hp with rfl | hp'
      · exact hRxy
      · exact hPgood.1 p hp'
    · intro p hp q hq a b hab
      rcases Finset.mem_insert.mp hp with rfl | hp'
      · rcases Finset.mem_insert.mp hq with rfl | hq'
        · refine ⟨rfl, ?_⟩
          by_contra hab'
          exact hxy (by fin_cases a <;> fin_cases b <;> simp_all [pairVal])
        · exfalso
          have hqmem : pairVal q b ∈ Set.range (fun p : Fin P.card × Fin 2 => σ p.1 p.2) := by
            fin_cases b
            · simpa [pairVal] using (hrange_fwd q hq').1
            · simpa [pairVal] using (hrange_fwd q hq').2
          exact hnew_notin a (by rw [hab]; exact hqmem)
      · rcases Finset.mem_insert.mp hq with rfl | hq'
        · exfalso
          have hpmem : pairVal p a ∈ Set.range (fun p : Fin P.card × Fin 2 => σ p.1 p.2) := by
            fin_cases a
            · simpa [pairVal] using (hrange_fwd p hp').1
            · simpa [pairVal] using (hrange_fwd p hp').2
          exact hnew_notin b (by rw [← hab]; exact hpmem)
        · exact hPgood.2 p hp' q hq' a b hab
  -- Maximality of `P` forbids this, so `(x, y) ∈ P` and `x` would be an endpoint.
  have hsub : insert (x, y) P ⊆ P :=
    hPmax.2 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hgood'⟩) (Finset.subset_insert _ _)
  have hxyP : (x, y) ∈ P := hsub (Finset.mem_insert_self _ _)
  obtain ⟨i, hi⟩ := e.surjective ⟨(x, y), hxyP⟩
  exact hx ⟨(i, 0), by simp [σ, pairVal, hi]⟩

/-- **Maximal pairwise-disjoint pairing.** For any hypergraph `𝓗` on `Fin n` there is a maximal
collection of pairwise disjoint pairs of hyperedges: a family `{e_i, f_i}` (`i : Fin t`) of
pairs with `e_i` disjoint from `f_i`, all `2t` hyperedges distinct, such that any two distinct
hyperedges outside the family meet. -/
theorem exists_maximal_disjoint_pairing {n : ℕ} (𝓗 : Set (Set (Fin n))) :
    ∃ (t : ℕ) (σ : Fin t → Fin 2 → {e : Set (Fin n) // e ∈ 𝓗}),
      Function.Injective (fun p : Fin t × Fin 2 => σ p.1 p.2) ∧
      (∀ i : Fin t, Disjoint ((σ i 0).1 : Set (Fin n)) ((σ i 1).1 : Set (Fin n))) ∧
      (∀ x : {e : Set (Fin n) // e ∈ 𝓗},
        x ∉ Set.range (fun p : Fin t × Fin 2 => σ p.1 p.2) →
        ∀ y : {e : Set (Fin n) // e ∈ 𝓗},
          y ∉ Set.range (fun p : Fin t × Fin 2 => σ p.1 p.2) → x ≠ y →
          ((x.1 : Set (Fin n)) ∩ y.1).Nonempty) := by
  classical
  obtain ⟨t, σ, hinj, hR, hmax⟩ :=
    exists_maximal_rel_matching (V := {e : Set (Fin n) // e ∈ 𝓗})
      (fun x y : {e : Set (Fin n) // e ∈ 𝓗} =>
        x ≠ y ∧ Disjoint (x.1 : Set (Fin n)) (y.1 : Set (Fin n)))
  refine ⟨t, σ, hinj, ?_, ?_⟩
  · intro i
    exact (hR i).2
  · intro x hx y hy hxy
    have hnd : ¬ Disjoint (x.1 : Set (Fin n)) (y.1 : Set (Fin n)) :=
      fun hd => hmax x y hx hy hxy ⟨hxy, hd⟩
    rwa [Set.not_disjoint_iff] at hnd

end Commons.Combinatorics.Hypergraph
