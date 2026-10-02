import Submission.EFL.Matching
import Submission.EFL.LargeEdge
import Submission.EFL.FewLargeColourClasses
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Finset.Union
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Lifting matchings and colour classes to edge families

Connects the matching/colour vocabulary (`IsMatching`, `Coloring.colorClass`,
from `Matching.lean`, and colour-class vertex coverage from `LargeEdge.lean`)
to the finite-family machinery of `FewLargeColourClasses.lean`.  The central
result is the paper's bound `few-large-colour-classes`(i) *in colour-class
language*: for a proper edge-colouring of a linear hypergraph whose edges all
have size at least `r+1`, the number of colours whose colour class covers at
least `αn` vertices is at most `n/(αr)` (`card_bigColourClasses_le`).
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

open scoped BigOperators

namespace ErdosFaberLovaszConjecture

noncomputable section

variable {n : ℕ}

/-- The finite family of vertex sets underlying a set `M` of edges of `𝓗`
(all of `𝓗`'s edges lie in `Fin n`, so `M` is finite). -/
def EdgeSetFamily {𝓗 : Hypergraph (Fin n)} (M : Set 𝓗) : Finset (Set (Fin n)) := by
  classical
  exact ((Finset.univ : Finset 𝓗).filter (fun e : 𝓗 => e ∈ M)).image
    (fun e : 𝓗 => (e : Set (Fin n)))

/-- Membership in `EdgeSetFamily M`. -/
theorem mem_EdgeSetFamily {𝓗 : Hypergraph (Fin n)} (M : Set 𝓗) (e : Set (Fin n)) :
    e ∈ EdgeSetFamily M ↔ ∃ x : 𝓗, x ∈ M ∧ (x : Set (Fin n)) = e := by
  classical
  simp [EdgeSetFamily]

/-- The vertex sets of a family of edges of `𝓗` are themselves edges of `𝓗`. -/
theorem EdgeSetFamily_subset {𝓗 : Hypergraph (Fin n)} (M : Set 𝓗) :
    FamilyInHypergraph 𝓗 (EdgeSetFamily M) := by
  intro e he
  rcases (mem_EdgeSetFamily M e).1 he with ⟨x, _hx, hx'⟩
  rw [← hx']
  exact x.2

/-- A matching `M ⊆ 𝓗` gives a matching family of vertex sets. -/
theorem IsMatchingFamily_of_IsMatching {𝓗 : Hypergraph (Fin n)} {M : Set 𝓗}
    (hM : IsMatching 𝓗 M) : IsMatchingFamily (EdgeSetFamily M) := by
  intro e₁ e₂ he₁ he₂ hne
  rcases (mem_EdgeSetFamily M e₁).1 he₁ with ⟨x₁, hx₁, hx₁'⟩
  rcases (mem_EdgeSetFamily M e₂).1 he₂ with ⟨x₂, hx₂, hx₂'⟩
  have hxx : x₁ ≠ x₂ := by
    intro h
    apply hne
    calc
      e₁ = (x₁ : Set (Fin n)) := hx₁'.symm
      _ = (x₂ : Set (Fin n)) := by rw [h]
      _ = e₂ := hx₂'
  simpa [hx₁', hx₂'] using hM hx₁ hx₂ hxx

/-- The vertices covered by a family of edges of `𝓗`. -/
theorem FamilyVertices_EdgeSetFamily {𝓗 : Hypergraph (Fin n)} (M : Set 𝓗) :
    FamilyVertices (EdgeSetFamily M) =
      {v : Fin n | ∃ e : 𝓗, e ∈ M ∧ v ∈ (e : Set (Fin n))} := by
  classical
  ext v
  simp [FamilyVertices, mem_EdgeSetFamily]

/-- The number of vertices covered by the colour class `c` equals the number
of vertices covered by its edge family. -/
theorem classVertexCount_eq_FamilyVertexCount {𝓗 : Hypergraph (Fin n)}
    (φ : 𝓗.Coloring (Fin n)) (c : Fin n) :
    φ.classVertexCount c = FamilyVertexCount (EdgeSetFamily (φ.colorClass c)) := by
  classical
  unfold Hypergraph.Coloring.classVertexCount FamilyVertexCount
  congr 1
  ext v
  simp [Hypergraph.Coloring.classVertices, FamilyVertices_EdgeSetFamily]

/-- Disjoint sets of edges give disjoint edge families. -/
theorem EdgeSetFamily_disjoint {𝓗 : Hypergraph (Fin n)} {M₁ M₂ : Set 𝓗}
    (hdisj : Disjoint M₁ M₂) : Disjoint (EdgeSetFamily M₁) (EdgeSetFamily M₂) := by
  classical
  rw [Finset.disjoint_left]
  intro e he₁ he₂
  rcases (mem_EdgeSetFamily M₁ e).1 he₁ with ⟨x₁, hx₁, hx₁'⟩
  rcases (mem_EdgeSetFamily M₂ e).1 he₂ with ⟨x₂, hx₂, _hx₂'⟩
  have hx : x₁ = x₂ := by
    apply Subtype.ext
    calc
      (x₁ : Set (Fin n)) = e := hx₁'
      _ = (x₂ : Set (Fin n)) := by
        have hx₂'' : (x₂ : Set (Fin n)) = e := ‹_›
        exact hx₂''.symm
  rw [Set.disjoint_left] at hdisj
  exact hdisj hx₁ (by simpa [hx] using hx₂)

/-- In a linear hypergraph, edges of any two colour classes intersect in at
most one vertex. -/
theorem linear_inter_colorClasses {𝓗 : Hypergraph (Fin n)} (hlin : 𝓗.IsLinear)
    {φ : 𝓗.Coloring (Fin n)} (i j : Fin n) :
    ∀ ⦃e₁ e₂ : Set (Fin n)⦄, e₁ ∈ EdgeSetFamily (φ.colorClass i) →
      e₂ ∈ EdgeSetFamily (φ.colorClass j) → e₁ ≠ e₂ →
      (e₁ ∩ e₂ : Set (Fin n)).Subsingleton := by
  intro e₁ e₂ he₁ he₂ hne
  rcases (mem_EdgeSetFamily (φ.colorClass i) e₁).1 he₁ with ⟨x₁, _hx₁, hx₁'⟩
  rcases (mem_EdgeSetFamily (φ.colorClass j) e₂).1 he₂ with ⟨x₂, _hx₂, hx₂'⟩
  have hval : (x₁ : Set (Fin n)) ≠ (x₂ : Set (Fin n)) := by
    intro h
    apply hne
    calc
      e₁ = (x₁ : Set (Fin n)) := hx₁'.symm
      _ = (x₂ : Set (Fin n)) := h
      _ = e₂ := hx₂'
  rw [← hx₁', ← hx₂']
  exact hlin x₁.2 x₂.2 hval

/-- `few-large-colour-classes` in colour-class language, for an injective list
`cs` of colours whose classes each cover at least `αn` vertices. -/
theorem fewLargeColourClasses_of_colorClasses {n t r : ℕ} {α : ℝ} (h2n : 2 ≤ n)
    (hα : 0 < α) (hr : 1 ≤ r) {𝓗 : Hypergraph (Fin n)} (hlin : 𝓗.IsLinear)
    (hbig : ∀ e : 𝓗, (r + 1 : ℕ) ≤ edgeSize (e : Set (Fin n)))
    {φ : 𝓗.Coloring (Fin n)} {cs : Fin t → Fin n} (hcs : Function.Injective cs)
    (hcover : ∀ i : Fin t, (α : ℝ) * (n : ℝ) ≤ (φ.classVertexCount (cs i) : ℝ)) :
    (t : ℝ) ≤ (n : ℝ) / (α * (r : ℝ)) := by
  classical
  let M : Fin t → Finset (Set (Fin n)) := fun i => EdgeSetFamily (φ.colorClass (cs i))
  have hlinfam : ∀ ⦃e₁ e₂ : Set (Fin n)⦄, (∃ i : Fin t, e₁ ∈ M i) →
      (∃ i : Fin t, e₂ ∈ M i) → e₁ ≠ e₂ → (e₁ ∩ e₂ : Set (Fin n)).Subsingleton := by
    intro e₁ e₂ hi hj hne
    rcases hi with ⟨i, he₁⟩
    rcases hj with ⟨j, he₂⟩
    dsimp [M] at he₁ he₂ ⊢
    exact linear_inter_colorClasses hlin (cs i) (cs j) he₁ he₂ hne
  have hsizes : ∀ (i : Fin t) (e : Set (Fin n)), e ∈ M i → r + 1 ≤ edgeSize e := by
    intro i e he
    rcases (mem_EdgeSetFamily (φ.colorClass (cs i)) e).1 he with ⟨x, _hx, hx'⟩
    simpa [hx'] using hbig x
  have hcover' : ∀ i : Fin t, (α : ℝ) * (n : ℝ) ≤ (sumEdgeSizes (M i) : ℝ) := by
    intro i
    have hEq : φ.classVertexCount (cs i) = FamilyVertexCount (M i) := by
      dsimp [M]
      exact classVertexCount_eq_FamilyVertexCount φ (cs i)
    have hle : FamilyVertexCount (M i) ≤ sumEdgeSizes (M i) :=
      FamilyVertexCount_le_sumEdgeSizes (M i)
    calc
      (α : ℝ) * (n : ℝ) ≤ (φ.classVertexCount (cs i) : ℝ) := hcover i
      _ = (FamilyVertexCount (M i) : ℝ) := by exact_mod_cast hEq
      _ ≤ (sumEdgeSizes (M i) : ℝ) := by exact_mod_cast hle
  have hdisj : ∀ (i j : Fin t), i ≠ j → Disjoint (M i) (M j) := by
    intro i j hij
    have hne : cs i ≠ cs j := hcs.ne hij
    have hcl := Hypergraph.Coloring.colorClass_disjoint φ hne
    dsimp [M]
    exact EdgeSetFamily_disjoint hcl
  exact fewLargeColourClasses_le (h2n := h2n) (hα := hα) (hr := hr) (M := M)
    hlinfam hsizes hcover' hdisj

/-- *Few large colour classes* (i) in colour-class language: for a proper
edge-colouring of a linear hypergraph whose edges all have size at least
`r+1`, the number of colours whose class covers at least `αn` vertices is at
most `n/(αr)`. -/
theorem card_bigColourClasses_le {n r : ℕ} {α : ℝ} (h2n : 2 ≤ n) (hα : 0 < α) (hr : 1 ≤ r)
    {𝓗 : Hypergraph (Fin n)} (hlin : 𝓗.IsLinear)
    (hbig : ∀ e : 𝓗, (r + 1 : ℕ) ≤ edgeSize (e : Set (Fin n)))
    {φ : 𝓗.Coloring (Fin n)} :
    (((Finset.univ : Finset (Fin n)).filter
        (fun c : Fin n => (α : ℝ) * (n : ℝ) ≤ (φ.classVertexCount c : ℝ))).card : ℝ) ≤
      (n : ℝ) / (α * (r : ℝ)) := by
  classical
  let Cbig : Finset (Fin n) := (Finset.univ : Finset (Fin n)).filter
    (fun c : Fin n => (α : ℝ) * (n : ℝ) ≤ (φ.classVertexCount c : ℝ))
  let B := {c : Fin n // c ∈ Cbig}
  haveI : Fintype B := Fintype.ofFinite B
  let eB : Fin (Fintype.card B) ≃ B := (Fintype.equivFin B).symm
  let cs : Fin (Fintype.card B) → Fin n := fun i => (eB i).1
  have hfilter : (Finset.univ : Finset (Fin n)).filter (fun c : Fin n => c ∈ Cbig) = Cbig := by
    ext c
    simp [Cbig]
  have hcard : Fintype.card B = Cbig.card := by
    calc
      Fintype.card B = ((Finset.univ : Finset (Fin n)).filter (fun c : Fin n => c ∈ Cbig)).card := by
        rw [Fintype.card_subtype]
      _ = Cbig.card := by rw [hfilter]
  have hcs : Function.Injective cs := by
    intro i j hij
    apply eB.injective
    apply Subtype.ext
    exact hij
  have hcover : ∀ i : Fin (Fintype.card B),
      (α : ℝ) * (n : ℝ) ≤ (φ.classVertexCount (cs i) : ℝ) := by
    intro i
    exact (Finset.mem_filter.mp (eB i).2).2
  have hmain := fewLargeColourClasses_of_colorClasses (n := n) (t := Fintype.card B)
    (r := r) (α := α) h2n hα hr hlin hbig (φ := φ) (cs := cs) hcs hcover
  rw [hcard] at hmain
  exact hmain
