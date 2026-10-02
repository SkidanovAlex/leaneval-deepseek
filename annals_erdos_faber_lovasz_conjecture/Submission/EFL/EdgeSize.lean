import Submission.EFL.Counting
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Real.Sqrt

/-!
# Classes of edges by their size

Following Definition `def:edgesize` of the paper, for a linear hypergraph
`𝓗` on `n` vertices we partition the edges into *small*, *medium* and *large*
edges by their size:

* `small` : `edgeSize e ≤ r₁`
* `medium`: `r₁ < edgeSize e ∧ edgeSize e ≤ r₀`
* `large` : `r₀ < edgeSize e`

and single out the *FPP-extremal* edges (size close to `√n`) and the *huge*
edges (size at least `βn/4`).  Each class is a sub-hypergraph preserving
linearity.  When `r₁ ≤ r₀` the three size classes are pairwise disjoint
(`small_large_disjoint`) and together partition the edge set
(`partition_small_medium_large`), so that a colouring problem on `𝓗` can be
split into the same problem on the three classes.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace ErdosFaberLovaszConjecture

noncomputable section

variable {n : ℕ}

/-- The *small* edges of `𝓗`: edges of size at most `r₁`. -/
def Hypergraph.smallEdges (𝓗 : Hypergraph (Fin n)) (r₁ : ℕ) : Hypergraph (Fin n) :=
  {e : Set (Fin n) | e ∈ 𝓗 ∧ edgeSize e ≤ r₁}

/-- The *medium* edges of `𝓗`: edges of size strictly between `r₁` and `r₀`. -/
def Hypergraph.medEdges (𝓗 : Hypergraph (Fin n)) (r₁ r₀ : ℕ) : Hypergraph (Fin n) :=
  {e : Set (Fin n) | e ∈ 𝓗 ∧ r₁ < edgeSize e ∧ edgeSize e ≤ r₀}

/-- The *large* edges of `𝓗`: edges of size strictly greater than `r₀`. -/
def Hypergraph.largeEdges (𝓗 : Hypergraph (Fin n)) (r₀ : ℕ) : Hypergraph (Fin n) :=
  {e : Set (Fin n) | e ∈ 𝓗 ∧ r₀ < edgeSize e}

/-- The *FPP-extremal* edges of `𝓗`: edges of size within `δ·√n` of `√n`. -/
def Hypergraph.exEdges (𝓗 : Hypergraph (Fin n)) (δ : ℝ) : Hypergraph (Fin n) :=
  {e : Set (Fin n) | e ∈ 𝓗 ∧
    (1 - δ) * Real.sqrt n ≤ (edgeSize e : ℝ) ∧ (edgeSize e : ℝ) ≤ (1 + δ) * Real.sqrt n}

/-- The *huge* edges of `𝓗`: edges of size at least `βn/4`. -/
def Hypergraph.hugeEdges (𝓗 : Hypergraph (Fin n)) (β : ℝ) : Hypergraph (Fin n) :=
  {e : Set (Fin n) | e ∈ 𝓗 ∧ β * (n : ℝ) / 4 ≤ (edgeSize e : ℝ)}

/-- Membership in `smallEdges`. -/
@[simp]
theorem mem_smallEdges (𝓗 : Hypergraph (Fin n)) (r₁ : ℕ) (e : Set (Fin n)) :
    e ∈ 𝓗.smallEdges r₁ ↔ e ∈ 𝓗 ∧ edgeSize e ≤ r₁ := by
  rfl

/-- Membership in `medEdges`. -/
@[simp]
theorem mem_medEdges (𝓗 : Hypergraph (Fin n)) (r₁ r₀ : ℕ) (e : Set (Fin n)) :
    e ∈ 𝓗.medEdges r₁ r₀ ↔ e ∈ 𝓗 ∧ r₁ < edgeSize e ∧ edgeSize e ≤ r₀ := by
  rfl

/-- Membership in `largeEdges`. -/
@[simp]
theorem mem_largeEdges (𝓗 : Hypergraph (Fin n)) (r₀ : ℕ) (e : Set (Fin n)) :
    e ∈ 𝓗.largeEdges r₀ ↔ e ∈ 𝓗 ∧ r₀ < edgeSize e := by
  rfl

/-- Membership in `exEdges`. -/
@[simp]
theorem mem_exEdges (𝓗 : Hypergraph (Fin n)) (δ : ℝ) (e : Set (Fin n)) :
    e ∈ 𝓗.exEdges δ ↔ e ∈ 𝓗 ∧
      (1 - δ) * Real.sqrt n ≤ (edgeSize e : ℝ) ∧ (edgeSize e : ℝ) ≤ (1 + δ) * Real.sqrt n := by
  rfl

/-- Membership in `hugeEdges`. -/
@[simp]
theorem mem_hugeEdges (𝓗 : Hypergraph (Fin n)) (β : ℝ) (e : Set (Fin n)) :
    e ∈ 𝓗.hugeEdges β ↔ e ∈ 𝓗 ∧ β * (n : ℝ) / 4 ≤ (edgeSize e : ℝ) := by
  rfl

/-- The small edges form a sub-hypergraph of `𝓗`. -/
theorem smallEdges_subset (𝓗 : Hypergraph (Fin n)) (r₁ : ℕ) : 𝓗.smallEdges r₁ ⊆ 𝓗 := by
  intro e he
  exact (mem_smallEdges 𝓗 r₁ e).1 he |>.1

/-- The medium edges form a sub-hypergraph of `𝓗`. -/
theorem medEdges_subset (𝓗 : Hypergraph (Fin n)) (r₁ r₀ : ℕ) : 𝓗.medEdges r₁ r₀ ⊆ 𝓗 := by
  intro e he
  exact (mem_medEdges 𝓗 r₁ r₀ e).1 he |>.1

/-- The large edges form a sub-hypergraph of `𝓗`. -/
theorem largeEdges_subset (𝓗 : Hypergraph (Fin n)) (r₀ : ℕ) : 𝓗.largeEdges r₀ ⊆ 𝓗 := by
  intro e he
  exact (mem_largeEdges 𝓗 r₀ e).1 he |>.1

/-- The FPP-extremal edges form a sub-hypergraph of `𝓗`. -/
theorem exEdges_subset (𝓗 : Hypergraph (Fin n)) (δ : ℝ) : 𝓗.exEdges δ ⊆ 𝓗 := by
  intro e he
  exact (mem_exEdges 𝓗 δ e).1 he |>.1

/-- The huge edges form a sub-hypergraph of `𝓗`. -/
theorem hugeEdges_subset (𝓗 : Hypergraph (Fin n)) (β : ℝ) : 𝓗.hugeEdges β ⊆ 𝓗 := by
  intro e he
  exact (mem_hugeEdges 𝓗 β e).1 he |>.1

/-- Linearity is inherited by the small edges. -/
theorem IsLinear.smallEdges {𝓗 : Hypergraph (Fin n)} (hlin : 𝓗.IsLinear) (r₁ : ℕ) :
    (𝓗.smallEdges r₁).IsLinear :=
  hlin.mono (smallEdges_subset 𝓗 r₁)

/-- Linearity is inherited by the medium edges. -/
theorem IsLinear.medEdges {𝓗 : Hypergraph (Fin n)} (hlin : 𝓗.IsLinear) (r₁ r₀ : ℕ) :
    (𝓗.medEdges r₁ r₀).IsLinear :=
  hlin.mono (medEdges_subset 𝓗 r₁ r₀)

/-- Linearity is inherited by the large edges. -/
theorem IsLinear.largeEdges {𝓗 : Hypergraph (Fin n)} (hlin : 𝓗.IsLinear) (r₀ : ℕ) :
    (𝓗.largeEdges r₀).IsLinear :=
  hlin.mono (largeEdges_subset 𝓗 r₀)

/-- Linearity is inherited by the FPP-extremal edges. -/
theorem IsLinear.exEdges {𝓗 : Hypergraph (Fin n)} (hlin : 𝓗.IsLinear) (δ : ℝ) :
    (𝓗.exEdges δ).IsLinear :=
  hlin.mono (exEdges_subset 𝓗 δ)

/-- Linearity is inherited by the huge edges. -/
theorem IsLinear.hugeEdges {𝓗 : Hypergraph (Fin n)} (hlin : 𝓗.IsLinear) (β : ℝ) :
    (𝓗.hugeEdges β).IsLinear :=
  hlin.mono (hugeEdges_subset 𝓗 β)

/-- In a hypergraph on `Fin n` every edge is small, medium or large. -/
theorem mem_small_or_med_or_large (𝓗 : Hypergraph (Fin n)) (r₁ r₀ : ℕ)
    (e : Set (Fin n)) (he : e ∈ 𝓗) :
    e ∈ 𝓗.smallEdges r₁ ∨ e ∈ 𝓗.medEdges r₁ r₀ ∨ e ∈ 𝓗.largeEdges r₀ := by
  by_cases h₁ : edgeSize e ≤ r₁
  · exact Or.inl (by simp [he, h₁])
  · by_cases h₂ : edgeSize e ≤ r₀
    · have hgt : r₁ < edgeSize e := by omega
      exact Or.inr (Or.inl (by simp [he, hgt, h₂]))
    · have hgt : r₀ < edgeSize e := by omega
      exact Or.inr (Or.inr (by simp [he, hgt]))

/-- The small, medium and large edges of a hypergraph cover its edge set. -/
theorem union_small_medium_large (𝓗 : Hypergraph (Fin n)) (r₁ r₀ : ℕ) :
    𝓗.smallEdges r₁ ∪ 𝓗.medEdges r₁ r₀ ∪ 𝓗.largeEdges r₀ = 𝓗 := by
  ext e
  constructor
  · intro he
    simp only [Set.mem_union, or_assoc] at he
    rcases he with he | he | he
    · exact (mem_smallEdges 𝓗 r₁ e).1 he |>.1
    · exact (mem_medEdges 𝓗 r₁ r₀ e).1 he |>.1
    · exact (mem_largeEdges 𝓗 r₀ e).1 he |>.1
  · intro he
    simpa [Set.mem_union, or_assoc] using mem_small_or_med_or_large 𝓗 r₁ r₀ e he

/-- An edge cannot be both small and medium. -/
theorem disjoint_small_medium (𝓗 : Hypergraph (Fin n)) (r₁ r₀ : ℕ) :
    Disjoint (𝓗.smallEdges r₁) (𝓗.medEdges r₁ r₀) := by
  rw [Set.disjoint_left]
  intro e he₁ he₂
  have hs : edgeSize e ≤ r₁ := (mem_smallEdges 𝓗 r₁ e).1 he₁ |>.2
  have hm : r₁ < edgeSize e := (mem_medEdges 𝓗 r₁ r₀ e).1 he₂ |>.2.1
  exact (not_lt_of_ge hs) hm

/-- If `r₁ ≤ r₀`, an edge cannot be both small and large. -/
theorem small_large_disjoint (𝓗 : Hypergraph (Fin n)) (r₁ r₀ : ℕ) (hr : r₁ ≤ r₀) :
    Disjoint (𝓗.smallEdges r₁) (𝓗.largeEdges r₀) := by
  rw [Set.disjoint_left]
  intro e he₁ he₂
  have hs : edgeSize e ≤ r₁ := (mem_smallEdges 𝓗 r₁ e).1 he₁ |>.2
  have hl : r₀ < edgeSize e := (mem_largeEdges 𝓗 r₀ e).1 he₂ |>.2
  exact (not_lt_of_ge (le_trans hs hr)) hl

/-- An edge cannot be both medium and large. -/
theorem disjoint_medium_large (𝓗 : Hypergraph (Fin n)) (r₁ r₀ : ℕ) :
    Disjoint (𝓗.medEdges r₁ r₀) (𝓗.largeEdges r₀) := by
  rw [Set.disjoint_left]
  intro e he₁ he₂
  have hm : edgeSize e ≤ r₀ := (mem_medEdges 𝓗 r₁ r₀ e).1 he₁ |>.2.2
  have hl : r₀ < edgeSize e := (mem_largeEdges 𝓗 r₀ e).1 he₂ |>.2
  exact (not_lt_of_ge hm) hl

end
