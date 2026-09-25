import Mathlib
import Submission.Work.Defs.Basic
import Submission.Work.Geometry.Basic

/-!
# The counting functions of the geometric core

For a coset `a + Λ` of the lattice `Λ = Lattice K I` of a fractional ideal `I` and a radius `R`:

* `Xset K I R a` is the set of points of `a + Λ` lying in the window `B_R`;
* `PairSet K I R U a` is the set of ordered pairs of points of `Xset` whose difference is the
  image of an element of `U ⊆ K`;
* `pointCount`, `pairCount` are the `ℝ≥0∞`-valued cardinalities of these sets, written as
  sums of indicators over the lattice, which makes them convenient for the unfolding
  identity over a fundamental domain.
-/

set_option linter.unusedSectionVars false

open MeasureTheory NumberField
open scoped Classical nonZeroDivisors Pointwise

namespace Work
namespace Geometry

variable (K : Type*) [Field K] [NumberField K]

/-- The intersection `B_R ∩ (B_R - v)` of two windows shifted by `v`. -/
def WindowShift (R : ℝ) (v : mixedEmbedding.mixedSpace K) : Set (mixedEmbedding.mixedSpace K) :=
  Window K R ∩ {x | x + v ∈ Window K R}

/-- The lattice points of the coset `a + Λ` that lie in the window `B_R`. -/
def Xset (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (R : ℝ) (a : mixedEmbedding.mixedSpace K) :
    Set (mixedEmbedding.mixedSpace K) :=
  {x | x - a ∈ Lattice K I ∧ x ∈ Window K R}

/-- Ordered pairs of points of `Xset K I R a` whose difference is the image of an element of `U`. -/
def PairSet (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (R : ℝ) (U : Finset K)
    (a : mixedEmbedding.mixedSpace K) :
    Set (mixedEmbedding.mixedSpace K × mixedEmbedding.mixedSpace K) :=
  {p | p.1 ∈ Xset K I R a ∧ p.2 ∈ Xset K I R a ∧ ∃ u ∈ U, p.2 - p.1 = mixedEmbedding K u}

/-- The number of lattice points of the coset `a + Λ` in the window, as an `ℝ≥0∞`-valued sum of
indicators over the lattice. -/
noncomputable def pointCount (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (R : ℝ)
    (a : mixedEmbedding.mixedSpace K) : ENNReal :=
  ∑' l : Lattice K I, (Window K R).indicator (fun _ => (1 : ENNReal))
    (a + (l : mixedEmbedding.mixedSpace K))

/-- The number of `l` with both `a + l` and `a + l + Φ u` in the window. -/
noncomputable def pairCountOne (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (R : ℝ)
    (a : mixedEmbedding.mixedSpace K) (u : K) : ENNReal :=
  ∑' l : Lattice K I,
    (Window K R).indicator (fun _ => (1 : ENNReal)) (a + (l : mixedEmbedding.mixedSpace K)) *
    (Window K R).indicator (fun _ => (1 : ENNReal))
      (a + (l : mixedEmbedding.mixedSpace K) + mixedEmbedding K u)

/-- The pair count `E_a`, summed over `u ∈ U`. -/
noncomputable def pairCount (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (R : ℝ) (U : Finset K)
    (a : mixedEmbedding.mixedSpace K) : ENNReal :=
  ∑ u ∈ U, pairCountOne K I R a u

/-- The cardinality of `Xset K I R a`, as a natural number. -/
noncomputable def pointCard (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (R : ℝ)
    (a : mixedEmbedding.mixedSpace K) : ℕ :=
  (Xset K I R a).ncard

/-- The cardinality of `PairSet K I R U a`, as a natural number. -/
noncomputable def pairCard (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (R : ℝ) (U : Finset K)
    (a : mixedEmbedding.mixedSpace K) : ℕ :=
  (PairSet K I R U a).ncard

variable {K}

theorem mem_Xset {I : (FractionalIdeal (𝓞 K)⁰ K)ˣ} {R : ℝ} {a x : mixedEmbedding.mixedSpace K} :
    x ∈ Xset K I R a ↔ x - a ∈ Lattice K I ∧ x ∈ Window K R := Iff.rfl

theorem mem_Xset' {I : (FractionalIdeal (𝓞 K)⁰ K)ˣ} {R : ℝ} {a x : mixedEmbedding.mixedSpace K} :
    x ∈ Xset K I R a ↔ ∃ l : Lattice K I, x = a + (l : mixedEmbedding.mixedSpace K) ∧
      x ∈ Window K R := by
  rw [mem_Xset]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨⟨x - a, h1⟩, by simp, h2⟩
  · rintro ⟨l, rfl, h2⟩
    exact ⟨by simpa using l.2, h2⟩

theorem mem_PairSet {I : (FractionalIdeal (𝓞 K)⁰ K)ˣ} {R : ℝ} {U : Finset K}
    {a : mixedEmbedding.mixedSpace K} {p : mixedEmbedding.mixedSpace K × mixedEmbedding.mixedSpace K} :
    p ∈ PairSet K I R U a ↔
      p.1 ∈ Xset K I R a ∧ p.2 ∈ Xset K I R a ∧ ∃ u ∈ U, p.2 - p.1 = mixedEmbedding K u :=
  Iff.rfl

theorem Xset_eq_vadd (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (R : ℝ)
    (a : mixedEmbedding.mixedSpace K) :
    Xset K I R a =
      a +ᵥ ((Lattice K I : Set (mixedEmbedding.mixedSpace K)) ∩ {y | a + y ∈ Window K R}) := by
  ext x
  rw [mem_Xset, Set.mem_vadd_set]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨x - a, ⟨h1, by simpa using h2⟩, by simp [vadd_eq_add]⟩
  · rintro ⟨y, ⟨h1, h2⟩, rfl⟩
    exact ⟨by simpa using h1, h2⟩

theorem Xset_subset_window (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (R : ℝ)
    (a : mixedEmbedding.mixedSpace K) : Xset K I R a ⊆ Window K R :=
  fun _ hx => hx.2

end Geometry
end Work
