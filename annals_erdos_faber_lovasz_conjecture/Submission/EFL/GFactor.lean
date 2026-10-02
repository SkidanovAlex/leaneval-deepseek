import Submission.EFL.Reservoir
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Int.Basic
import Mathlib.SetTheory.Cardinal.NatCard

/-!
# Subgraphs on a vertex set, and the Lovász `(g,f)`-factor theorem

This module supplies

* `nbrsIn R W v` / `degIn R W v` — the neighbourhood and degree of `v` in the
  2-graph `R` *restricted to the vertex set* `W`, i.e. the degree in the
  induced graph `R[W]` (when `R` is a family of 2-element edges and `v ∈ W`);
* `GFactorStatement` — the paper's Theorem `thm:gf_factor` (Lovász's
  `(g,f)`-factor theorem) in the form in which §11 consumes it, stated as an
  *input statement* in the style of `KahnStatement`/`MolloyReedStatement`.

The paper's statement (Lovász, *Subgraphs with prescribed valencies*, Theorem
7.3) is: if `G` is a graph and `f, g : V(G) → ℤ` satisfy
`0 ≤ g(x) < f(x) ≤ d_G(x)` for every `x`, then a `(g,f)`-factor exists
*given that* for every two disjoint sets `S, T ⊆ V(G)`

  `∑_{s ∈ S} f(s) + ∑_{t ∈ T} (d_G(t) − g(t)) ≥ e_G(S,T)`

(and conversely).  Below the graph `G` is a family `G` of 2-element edges and
the "graph" is the induced graph on the vertex set `W`; the functions live on
`Fin n` and are only constrained on `W`.
-/

set_option autoImplicit false

open scoped BigOperators

namespace ErdosFaberLovaszConjecture

noncomputable section

variable {n : ℕ}

/-- `N_{R[W]}(v)`: the neighbours of `v` inside `W`, i.e. the vertices `w ∈ W`
such that `{v,w}` is a 2-edge of `R`. -/
def nbrsIn (R : Hypergraph (Fin n)) (W : Set (Fin n)) (v : Fin n) : Set (Fin n) :=
  {w | w ∈ W ∧ ({v, w} : Set (Fin n)) ∈ R}

/-- The degree of `v` in the 2-graph `R` restricted to `W`. -/
def degIn (R : Hypergraph (Fin n)) (W : Set (Fin n)) (v : Fin n) : ℕ :=
  (nbrsIn R W v).ncard

@[simp]
theorem mem_nbrsIn {R : Hypergraph (Fin n)} {W : Set (Fin n)} {v w : Fin n} :
    w ∈ nbrsIn R W v ↔ w ∈ W ∧ ({v, w} : Set (Fin n)) ∈ R := Iff.rfl

theorem nbrsIn_subset_nbrs (R : Hypergraph (Fin n)) (W : Set (Fin n)) (v : Fin n) :
    nbrsIn R W v ⊆ nbrs R v := fun _ h => h.2

theorem degIn_le_degAt (R : Hypergraph (Fin n)) (W : Set (Fin n)) (v : Fin n) :
    degIn R W v ≤ degAt R v :=
  Set.ncard_le_ncard (nbrsIn_subset_nbrs R W v) (Set.toFinite _)

theorem nbrsIn_mono_fam {R R' : Hypergraph (Fin n)} (h : R ⊆ R') (W : Set (Fin n))
    (v : Fin n) : nbrsIn R W v ⊆ nbrsIn R' W v :=
  fun _ hw => ⟨hw.1, h hw.2⟩

theorem degIn_mono_fam {R R' : Hypergraph (Fin n)} (h : R ⊆ R') (W : Set (Fin n))
    (v : Fin n) : degIn R W v ≤ degIn R' W v :=
  Set.ncard_le_ncard (nbrsIn_mono_fam h W v) (Set.toFinite _)

theorem nbrsIn_mono_set (R : Hypergraph (Fin n)) {W W' : Set (Fin n)} (h : W ⊆ W')
    (v : Fin n) : nbrsIn R W v ⊆ nbrsIn R W' v :=
  fun _ hw => ⟨h hw.1, hw.2⟩

theorem degIn_mono_set (R : Hypergraph (Fin n)) {W W' : Set (Fin n)} (h : W ⊆ W')
    (v : Fin n) : degIn R W v ≤ degIn R W' v :=
  Set.ncard_le_ncard (nbrsIn_mono_set R h v) (Set.toFinite _)

@[simp]
theorem nbrsIn_univ (R : Hypergraph (Fin n)) (v : Fin n) : nbrsIn R Set.univ v = nbrs R v := by
  ext w; simp [nbrsIn, nbrs]

@[simp]
theorem degIn_univ (R : Hypergraph (Fin n)) (v : Fin n) : degIn R Set.univ v = degAt R v := by
  simp only [degIn, degAt, nbrsIn_univ]

theorem degIn_le_card (R : Hypergraph (Fin n)) (W : Set (Fin n)) (v : Fin n) :
    degIn R W v ≤ W.ncard :=
  Set.ncard_le_ncard (fun _ hw => hw.1) (Set.toFinite W)

/-- **Lovász's `(g,f)`-factor theorem** (paper Theorem `thm:gf_factor`), in the
form used in §11: for a family `G` of 2-element edges, a vertex set `W`, and
integer functions `f, g` with `0 ≤ g(x) < f(x) ≤ d_{G[W]}(x)` on `W` such that
for all disjoint `S, T ⊆ W` the Lovász condition holds, there is a subfamily
`R ⊆ G[W]` with `g(x) ≤ d_{R[W]}(x) ≤ f(x)` for every `x ∈ W`. -/
def GFactorStatement : Prop :=
  ∀ {n : ℕ} (G : Hypergraph (Fin n)) (W : Set (Fin n)) (f g : Fin n → ℤ),
    (∀ e ∈ G, edgeSize e = 2) →
    (∀ x ∈ W, 0 ≤ g x) → (∀ x ∈ W, g x < f x) →
    (∀ x ∈ W, f x ≤ (degIn G W x : ℤ)) →
    (∀ S T : Finset (Fin n), (∀ x ∈ S, x ∈ W) → (∀ x ∈ T, x ∈ W) → Disjoint S T →
        (edgeCount G S T : ℤ) ≤ (∑ s ∈ S, f s) + ∑ t ∈ T, ((degIn G W t : ℤ) - g t)) →
    ∃ R : Hypergraph (Fin n), R ⊆ G ∧ (∀ e ∈ R, e ⊆ W) ∧
      ∀ x ∈ W, g x ≤ (degIn R W x : ℤ) ∧ (degIn R W x : ℤ) ≤ f x

end

end ErdosFaberLovaszConjecture
