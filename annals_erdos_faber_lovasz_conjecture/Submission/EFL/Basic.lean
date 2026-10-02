import ChallengeDeps
import Mathlib.Data.Fintype.Powerset
import Mathlib.Order.Lattice.Nat

/-!
# Basic API for hypergraph colourings and the chromatic index

This file develops the elementary theory of the notions introduced in
`ChallengeDeps.lean` (statement of Theorem 1.1 of D. Y. Kang, T. Kelly,
D. Kühn, A. Methuku and D. Osthus, *A proof of the Erdős–Faber–Lovász
conjecture*, Annals of Math. 198 (2) (2023)):

* `Hypergraph V := Set (Set V)`: a hypergraph is a collection of edges,
  each edge a subset of the vertex set `V`;
* `Hypergraph.Coloring α 𝓗`: an `α`-colouring of the *edges* of `𝓗` such
  that intersecting distinct edges receive different colours;
* `Hypergraph.chromaticIndex 𝓗`: the least number of colours needed.

The main mathematical content of this file is the interplay between the
*existence* of a colouring with `Fin k` colours and the *number*
`chromaticIndex`: over hypergraphs with finitely many edges these two
notions are equivalent (`ErdosFaberLovaszConjecture.chromaticIndex_le_iff_colorable`).

Everything here is elementary and reusable; it is the scaffolding on which
the deep proof of the theorem must be built.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

noncomputable section

namespace ErdosFaberLovaszConjecture

variable {V : Type*}

/-- A hypergraph `𝓗` is `k`-colourable when its edges can be coloured with the
`k` colours `Fin k` so that intersecting distinct edges get different colours. -/
def Hypergraph.Colorable (k : ℕ) (𝓗 : Hypergraph V) : Prop :=
  Nonempty (𝓗.Coloring (Fin k))

/-- Given a colouring with `Fin k` and a larger number of colours `n ≥ k` we can
extend it: relabel colours through the embedding `Fin k ↪ Fin n`. -/
def Hypergraph.Coloring.ofLeColors {𝓗 : Hypergraph V} {k n : ℕ} (hkn : k ≤ n)
    (C : 𝓗.Coloring (Fin k)) : 𝓗.Coloring (Fin n) where
  labels e := Fin.castLE hkn (C.labels e)
  isColoring e₁ e₂ he hnon := by
    intro hcol
    exact C.isColoring e₁ e₂ he hnon ((Fin.castLE_injective hkn) hcol)

/-- Colourings are invariant under a bijective renaming of the colours. -/
def Hypergraph.Coloring.recolor {𝓗 : Hypergraph V} {α β : Type*}
    (C : 𝓗.Coloring α) (e : α ≃ β) : 𝓗.Coloring β where
  labels e' := e (C.labels e')
  isColoring e₁ e₂ he hnon := by
    intro hcol
    exact C.isColoring e₁ e₂ he hnon (e.injective hcol)

/-- Restricting a colouring of `𝓗` to a subhypergraph `𝓖 ⊆ 𝓗`. -/
def Hypergraph.Coloring.restrict {𝓖 𝓗 : Hypergraph V} (hsub : 𝓖 ⊆ 𝓗) {α : Type*}
    (C : 𝓗.Coloring α) : 𝓖.Coloring α where
  labels e := C.labels ⟨e.1, hsub e.2⟩
  isColoring e₁ e₂ he hnon := by
    apply C.isColoring ⟨e₁.1, hsub e₁.2⟩ ⟨e₂.1, hsub e₂.2⟩
    · intro hEq
      apply he
      apply Subtype.ext
      simpa using congrArg (fun x : 𝓗 => x.1) hEq
    · simpa using hnon

/-- If a colouring exists with `k` colours then a colouring exists with any
`n ≥ k` colours. -/
theorem Hypergraph.Colorable.mono {𝓗 : Hypergraph V} {k n : ℕ} (hkn : k ≤ n)
    (hc : 𝓗.Colorable k) : 𝓗.Colorable n := by
  rcases hc with ⟨C⟩
  exact ⟨Hypergraph.Coloring.ofLeColors hkn C⟩

/-- If a colouring exists for `𝓗` then one exists for every subhypergraph. -/
theorem Hypergraph.Colorable.restrict {𝓖 𝓗 : Hypergraph V} (hsub : 𝓖 ⊆ 𝓗) {k : ℕ}
    (hc : 𝓗.Colorable k) : 𝓖.Colorable k := by
  rcases hc with ⟨C⟩
  exact ⟨Hypergraph.Coloring.restrict hsub C⟩

/-- If a colouring exists with `k` colours then the chromatic index is at most `k`
(since the chromatic index is the least number of colours that works). -/
theorem Hypergraph.chromaticIndex_le_of_colorable (𝓗 : Hypergraph V) {k : ℕ}
    (h : 𝓗.Colorable k) : 𝓗.chromaticIndex ≤ k := by
  unfold Hypergraph.chromaticIndex
  unfold Hypergraph.Colorable at h
  exact Nat.sInf_le (by simpa using h)

/-- If `𝓗` admits a colouring with some finite number of colours then
`chromaticIndex 𝓗` itself is a number of colours that works. -/
theorem Hypergraph.colorable_chromaticIndex {𝓗 : Hypergraph V}
    (hcol : ∃ k : ℕ, 𝓗.Colorable k) : 𝓗.Colorable 𝓗.chromaticIndex := by
  unfold Hypergraph.chromaticIndex Hypergraph.Colorable
  rcases hcol with ⟨k₀, hk₀⟩
  unfold Hypergraph.Colorable at hk₀
  have hmem :
      sInf {n : ℕ | Nonempty (𝓗.Coloring (Fin n))} ∈
        {n : ℕ | Nonempty (𝓗.Coloring (Fin n))} := by
    apply Nat.sInf_mem
    exact ⟨k₀, by simpa using hk₀⟩
  simpa using hmem

/-- Provided that a colouring with some finite number of colours exists, the
chromatic index is at most `k` if and only if a colouring with `k` colours exists. -/
theorem Hypergraph.chromaticIndex_le_iff_colorable (𝓗 : Hypergraph V)
    (hcol : ∃ k : ℕ, 𝓗.Colorable k) {k : ℕ} :
    𝓗.chromaticIndex ≤ k ↔ 𝓗.Colorable k := by
  constructor
  · intro hle
    exact Hypergraph.Colorable.mono hle (Hypergraph.colorable_chromaticIndex hcol)
  · exact Hypergraph.chromaticIndex_le_of_colorable 𝓗

/-- Every hypergraph with finitely many edges admits a colouring in which all
edges have different colours. -/
def Hypergraph.coloring_distinct {𝓗 : Hypergraph V} [Fintype 𝓗] :
    𝓗.Coloring (Fin (Fintype.card 𝓗)) where
  labels e := Fintype.equivFin 𝓗 e
  isColoring e₁ e₂ he hnon := by
    intro hcol
    exact he ((Fintype.equivFin 𝓗).injective hcol)

/-- A hypergraph with finitely many edges is colourable with finitely many colours. -/
theorem Hypergraph.colorable_of_fintype {𝓗 : Hypergraph V} [Fintype 𝓗] :
    𝓗.Colorable (Fintype.card 𝓗) :=
  ⟨Hypergraph.coloring_distinct⟩

/-- A hypergraph on a finite vertex type has finitely many edges, hence is
finitely colourable. -/
theorem Hypergraph.colorable_of_finite_vertices [Fintype V] (𝓗 : Hypergraph V) :
    ∃ k : ℕ, 𝓗.Colorable k := by
  classical
  letI : Fintype (Set V) := Fintype.ofFinite (Set V)
  letI : Fintype 𝓗 := Fintype.ofFinite 𝓗
  exact ⟨Fintype.card 𝓗, Hypergraph.colorable_of_fintype⟩

/-- The chromatic index is monotone in the hypergraph: if `𝓖 ⊆ 𝓗` and `𝓗` is
finitely colourable, then `𝓖` needs no more colours than `𝓗`. -/
theorem Hypergraph.chromaticIndex_le_chromaticIndex_of_subset {𝓖 𝓗 : Hypergraph V}
    (hsub : 𝓖 ⊆ 𝓗) (h𝓗c : ∃ k : ℕ, 𝓗.Colorable k) :
    𝓖.chromaticIndex ≤ 𝓗.chromaticIndex := by
  have hr : 𝓖.Colorable 𝓗.chromaticIndex :=
    Hypergraph.Colorable.restrict hsub (Hypergraph.colorable_chromaticIndex h𝓗c)
  have h𝓖c : ∃ k : ℕ, 𝓖.Colorable k := ⟨_, hr⟩
  rw [Hypergraph.chromaticIndex_le_iff_colorable 𝓖 h𝓖c]
  exact hr

end ErdosFaberLovaszConjecture

end
