import Submission.EFL.Basic
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex

/-!
# The line graph of a hypergraph

The *line graph* `lineGraph 𝓗` of a hypergraph `𝓗` is the simple graph whose
vertices are the edges of `𝓗`, two of them being adjacent exactly when they are
distinct and intersect.

An (edge-)colouring of a hypergraph is exactly the same thing as a (vertex-)
colouring of its line graph (`ErdosFaberLovaszConjecture.lineGraph_coloring_iff`).
Consequently the chromatic index of `𝓗` is at most `n` iff its line graph is
`n`-colourable iff `chromaticNumber (lineGraph 𝓗) ≤ n`.

This reformulation is the point of view taken throughout the proof of the
Erdős–Faber–Lovász conjecture (colouring the line graph of a linear hypergraph),
and it lets us reuse the graph-colouring library of Mathlib.
-/

set_option autoImplicit false

namespace ErdosFaberLovaszConjecture

variable {V : Type*}

/-- The line graph of a hypergraph: vertices are the edges of `𝓗`, and two
distinct edges are adjacent when they intersect. -/
def Hypergraph.lineGraph (𝓗 : Hypergraph V) : SimpleGraph 𝓗 where
  Adj e₁ e₂ := e₁ ≠ e₂ ∧ (e₁.1 ∩ e₂.1 : Set V).Nonempty
  symm := ⟨fun e₁ e₂ h => ⟨h.1.symm, by simpa [Set.inter_comm] using h.2⟩⟩
  loopless := ⟨fun e h => h.1 rfl⟩

/-- A hypergraph colouring is the same as a colouring of the line graph. -/
def Hypergraph.lineGraphColoring {α : Type*} {𝓗 : Hypergraph V}
    (C : 𝓗.Coloring α) : (𝓗.lineGraph).Coloring α where
  toFun e := C.labels e
  map_rel' := by
    intro e₁ e₂ h
    exact C.isColoring e₁ e₂ h.1 h.2

/-- A colouring of the line graph gives a hypergraph colouring. -/
def Hypergraph.ofLineGraphColoring {α : Type*} {𝓗 : Hypergraph V}
    (C : (𝓗.lineGraph).Coloring α) : 𝓗.Coloring α where
  labels e := C.toFun e
  isColoring e₁ e₂ he hnon := by
    apply C.map_rel'
    exact ⟨he, hnon⟩

/-- Hypergraph colourings with colour set `α` are in bijection with colourings
of the line graph with colour set `α`. -/
def Hypergraph.lineGraphColoringEquiv (α : Type*) (𝓗 : Hypergraph V) :
    𝓗.Coloring α ≃ (𝓗.lineGraph).Coloring α where
  toFun := Hypergraph.lineGraphColoring
  invFun := Hypergraph.ofLineGraphColoring
  left_inv := by
    intro C
    cases C
    rfl
  right_inv := by
    intro C
    cases C
    rfl

/-- A hypergraph is `n`-colourable iff its line graph is `n`-colourable. -/
theorem Hypergraph.colorable_iff_lineGraph_colorable (n : ℕ) (𝓗 : Hypergraph V) :
    𝓗.Colorable n ↔ (𝓗.lineGraph).Colorable n := by
  unfold Hypergraph.Colorable
  unfold SimpleGraph.Colorable
  constructor
  · rintro ⟨C⟩
    exact ⟨Hypergraph.lineGraphColoringEquiv (Fin n) 𝓗 C⟩
  · rintro ⟨C⟩
    exact ⟨(Hypergraph.lineGraphColoringEquiv (Fin n) 𝓗).symm C⟩

/-- For a hypergraph with finitely many edges, the chromatic index is at most
`n` iff its line graph is `n`-colourable. -/
theorem Hypergraph.chromaticIndex_le_iff_lineGraph_colorable (𝓗 : Hypergraph V) [Fintype 𝓗]
    (n : ℕ) :
    𝓗.chromaticIndex ≤ n ↔ (𝓗.lineGraph).Colorable n := by
  rw [Hypergraph.chromaticIndex_le_iff_colorable 𝓗 ⟨Fintype.card 𝓗, Hypergraph.colorable_of_fintype⟩]
  exact Hypergraph.colorable_iff_lineGraph_colorable n 𝓗

/-- For a hypergraph on a finite vertex set, the chromatic index is at most `n`
iff its line graph is `n`-colourable. -/
theorem Hypergraph.chromaticIndex_le_iff_lineGraph_colorable_of_finite (𝓗 : Hypergraph V)
    [Fintype V] (n : ℕ) :
    𝓗.chromaticIndex ≤ n ↔ (𝓗.lineGraph).Colorable n := by
  classical
  rw [Hypergraph.chromaticIndex_le_iff_colorable 𝓗 (Hypergraph.colorable_of_finite_vertices 𝓗)]
  exact Hypergraph.colorable_iff_lineGraph_colorable n 𝓗

/-- The chromatic index of a hypergraph on a finite vertex set is at most `n` iff the
chromatic number of its line graph is at most `n`. -/
theorem Hypergraph.chromaticIndex_le_iff_chromaticNumber {V : Type*} [Fintype V]
    (n : ℕ) (𝓗 : Hypergraph V) :
    𝓗.chromaticIndex ≤ n ↔ (𝓗.lineGraph).chromaticNumber ≤ n := by
  rw [Hypergraph.chromaticIndex_le_iff_lineGraph_colorable_of_finite 𝓗]
  exact (SimpleGraph.chromaticNumber_le_iff_colorable).symm

/-- The chromatic index of a hypergraph on `Fin n` is at most `n` iff the chromatic number
of its line graph is at most `n`. -/
theorem chromaticIndex_le_iff_chromaticNumber_fin (n : ℕ) (𝓗 : Hypergraph (Fin n)) :
    𝓗.chromaticIndex ≤ n ↔ (𝓗.lineGraph).chromaticNumber ≤ n := by
  classical
  exact Hypergraph.chromaticIndex_le_iff_chromaticNumber n 𝓗

end ErdosFaberLovaszConjecture
