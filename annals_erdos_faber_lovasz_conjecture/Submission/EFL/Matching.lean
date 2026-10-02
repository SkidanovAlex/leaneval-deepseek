import Submission.EFL.Basic
import Submission.EFL.LineGraph
import Mathlib.Logic.Pairwise
import Mathlib.Data.Set.Disjoint
import Mathlib.Order.Disjoint

/-!
# Colour classes are matchings; colourings as matching decompositions

Throughout the proof of the Erdős–Faber–Lovász conjecture the paper works
with edge-colourings in the following form (see §12): *find `n` pairwise
edge-disjoint matchings which together contain all the edges*.  This file
formalises that vocabulary and proves that it is exactly equivalent to the
`ChallengeDeps` notion of an `n`-colouring:

* `IsMatching 𝓗 M`: a *matching* in a hypergraph is a family `M ⊆ 𝓗` of
  pairwise vertex-disjoint edges;
* the colour classes of a colouring `C` (fibres `{e | C.labels e = c}`) are
  matchings (`Coloring.colorClass_isMatching`), are pairwise disjoint
  (`Coloring.colorClass_disjoint`) and cover all the edges
  (`Coloring.colorClass_cover`);
* conversely a map whose fibres are matchings is a proper colouring
  (`coloring_of_matching_fibers`);
* hence `𝓗.Colorable n ↔ HasMatchingDecomposition n 𝓗`, where
  `HasMatchingDecomposition` is the paper's formulation ("n pairwise
  edge-disjoint matchings containing all the edges");
* finally, the bridge to the line graph: `IsMatching 𝓗 M` iff `M` is an
  independent set of `lineGraph 𝓗` (`isMatching_iff_isIndepSet`), which is
  why the proof in the paper is equivalently a graph-colouring problem.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace ErdosFaberLovaszConjecture

variable {V : Type*}

/-- A *matching* in a hypergraph `𝓗` is a family `M ⊆ 𝓗` of edges, any two of
which are vertex-disjoint (share no vertex). -/
def IsMatching (𝓗 : Hypergraph V) (M : Set 𝓗) : Prop :=
  M.Pairwise fun e₁ e₂ => Disjoint (e₁ : Set V) (e₂ : Set V)

/-- Matchings are preserved under taking subfamilies. -/
theorem IsMatching.subset {𝓗 : Hypergraph V} {M N : Set 𝓗} (hMN : N ⊆ M)
    (hM : IsMatching 𝓗 M) : IsMatching 𝓗 N :=
  hM.mono hMN

/-- The empty family is a matching. -/
theorem isMatching_empty (𝓗 : Hypergraph V) : IsMatching 𝓗 ∅ := by
  intro e he
  exact he.elim

/-- A family consisting of a single edge is a matching. -/
theorem isMatching_singleton (𝓗 : Hypergraph V) (e : 𝓗) : IsMatching 𝓗 {e} := by
  intro e₁ he₁ e₂ he₂ hne
  simp at he₁ he₂
  subst e₁
  subst e₂
  exact (hne rfl).elim

/-- The *colour class* of a colour `c` in a colouring `C`: all edges coloured `c`. -/
def Hypergraph.Coloring.colorClass {α : Type*} {𝓗 : Hypergraph V} (C : 𝓗.Coloring α)
    (c : α) : Set 𝓗 :=
  {e : 𝓗 | C.labels e = c}

/-- An edge is in the colour class `c` of `C` exactly when `C` gives it colour `c`. -/
@[simp]
theorem mem_colorClass {α : Type*} {𝓗 : Hypergraph V} (C : 𝓗.Coloring α) (c : α)
    (e : 𝓗) : e ∈ C.colorClass c ↔ C.labels e = c := by
  rfl

/-- The colour classes of a colouring are matchings: two distinct intersecting
edges cannot share a colour. -/
theorem Hypergraph.Coloring.colorClass_isMatching {α : Type*} {𝓗 : Hypergraph V}
    (C : 𝓗.Coloring α) (c : α) : IsMatching 𝓗 (C.colorClass c) := by
  intro e₁ he₁ e₂ he₂ hne
  by_contra hd
  rw [Set.not_disjoint_iff] at hd
  rcases hd with ⟨x, hx₁, hx₂⟩
  have h₁ : C.labels e₁ = c := he₁
  have h₂ : C.labels e₂ = c := he₂
  exact C.isColoring e₁ e₂ hne ⟨x, hx₁, hx₂⟩ (by simpa [h₁, h₂])

/-- The colour classes of a colouring with colour set `α` cover all edges. -/
theorem Hypergraph.Coloring.colorClass_cover {α : Type*} {𝓗 : Hypergraph V}
    (C : 𝓗.Coloring α) : ∀ e : 𝓗, ∃ c : α, e ∈ C.colorClass c := by
  intro e
  exact ⟨C.labels e, rfl⟩

/-- Distinct colour classes of a colouring are disjoint. -/
theorem Hypergraph.Coloring.colorClass_disjoint {α : Type*} {𝓗 : Hypergraph V}
    (C : 𝓗.Coloring α) {c₁ c₂ : α} (hne : c₁ ≠ c₂) :
    Disjoint (C.colorClass c₁) (C.colorClass c₂) := by
  rw [Set.disjoint_left]
  intro e he₁ he₂
  have h₁ : C.labels e = c₁ := he₁
  have h₂ : C.labels e = c₂ := he₂
  exact hne (h₁.symm.trans h₂)

/-- A map `f : 𝓗 → Fin n` whose fibres are matchings is a proper colouring. -/
theorem coloring_of_matching_fibers {n : ℕ} {𝓗 : Hypergraph V}
    (f : 𝓗 → Fin n) (hfib : ∀ c : Fin n, IsMatching 𝓗 {e : 𝓗 | f e = c}) :
    Nonempty (𝓗.Coloring (Fin n)) := by
  refine ⟨⟨f, ?_⟩⟩
  intro e₁ e₂ hne hnon
  by_contra hsame
  let c : Fin n := f e₁
  have hmem₁ : e₁ ∈ {e : 𝓗 | f e = c} := by simpa [c]
  have hmem₂ : e₂ ∈ {e : 𝓗 | f e = c} := by
    -- hsame : f e₁ = f e₂
    simp [c, hsame]
  exact (Set.not_disjoint_iff_nonempty_inter.mpr hnon) (hfib c hmem₁ hmem₂ hne)

/-- The *paper's formulation* of an `n`-colouring: `n` pairwise edge-disjoint
matchings which together contain all the edges of `𝓗`.  (Some of the
matchings may be empty, corresponding to unused colours.) -/
def HasMatchingDecomposition (n : ℕ) (𝓗 : Hypergraph V) : Prop :=
  ∃ M : Fin n → Set 𝓗,
    (∀ c : Fin n, IsMatching 𝓗 (M c)) ∧
    (∀ ⦃c₁ c₂ : Fin n⦄, c₁ ≠ c₂ → Disjoint (M c₁) (M c₂)) ∧
    (∀ e : 𝓗, ∃ c : Fin n, e ∈ M c)

/-- The colour classes of an `n`-colouring form a matching decomposition. -/
theorem Hypergraph.Coloring.hasMatchingDecomposition {n : ℕ} {𝓗 : Hypergraph V}
    (C : 𝓗.Coloring (Fin n)) : HasMatchingDecomposition n 𝓗 := by
  refine ⟨C.colorClass, ?_, ?_, ?_⟩
  · exact fun c => C.colorClass_isMatching c
  · intro c₁ c₂ hne
    exact C.colorClass_disjoint hne
  · exact C.colorClass_cover

/-- Given a matching decomposition we can colour each edge by the (chosen)
matching containing it. -/
noncomputable def matchingDecompositionColoring {n : ℕ} {𝓗 : Hypergraph V}
    {M : Fin n → Set 𝓗} (hmat : ∀ c : Fin n, IsMatching 𝓗 (M c))
    (hcov : ∀ e : 𝓗, ∃ c : Fin n, e ∈ M c) : 𝓗.Coloring (Fin n) := by
  classical
  refine ⟨fun e => Classical.choose (hcov e), ?_⟩
  intro e₁ e₂ hne hnon
  by_contra hsame
  let c : Fin n := Classical.choose (hcov e₁)
  have hmem₁ : e₁ ∈ M c := Classical.choose_spec (hcov e₁)
  have hmem₂ : e₂ ∈ M c := by
    simpa [c, hsame] using (Classical.choose_spec (hcov e₂))
  exact (Set.not_disjoint_iff_nonempty_inter.mpr hnon) (hmat c hmem₁ hmem₂ hne)

/-- A hypergraph has an `n`-colouring iff its edge set has a matching
decomposition into `n` parts (the paper's working formulation). -/
theorem colorable_iff_hasMatchingDecomposition {n : ℕ} {𝓗 : Hypergraph V} :
    𝓗.Colorable n ↔ HasMatchingDecomposition n 𝓗 := by
  constructor
  · rintro ⟨C⟩
    exact C.hasMatchingDecomposition
  · rintro ⟨M, hmat, _hdisj, hcov⟩
    classical
    exact ⟨matchingDecompositionColoring (M := M) hmat hcov⟩

/-- In the line graph of `𝓗` (whose vertices are the edges of `𝓗`), a family
of edges is a matching (pairwise vertex-disjoint) exactly when it is an
independent set. -/
theorem isMatching_iff_isIndepSet {𝓗 : Hypergraph V} (M : Set 𝓗) :
    IsMatching 𝓗 M ↔ (𝓗.lineGraph).IsIndepSet M := by
  constructor
  · intro h
    intro e₁ he₁ e₂ he₂ hne
    intro hadj
    exact (Set.not_disjoint_iff_nonempty_inter.mpr hadj.2) (h he₁ he₂ hadj.1)
  · intro h
    intro e₁ he₁ e₂ he₂ hne
    by_contra hd
    exact h he₁ he₂ hne ⟨hne, (Set.not_disjoint_iff_nonempty_inter.mp hd)⟩

/-- Colour classes of the line-graph colouring induced by a hypergraph
colouring are matchings. -/
theorem lineGraph_colorClass_isMatching {n : ℕ} {𝓗 : Hypergraph V}
    (C : 𝓗.Coloring (Fin n)) (c : Fin n) :
    IsMatching 𝓗 (C.colorClass c) :=
  C.colorClass_isMatching c

end ErdosFaberLovaszConjecture
