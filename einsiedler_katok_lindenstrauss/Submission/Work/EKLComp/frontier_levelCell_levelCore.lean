import Mathlib
import Submission.Work.EKLComp.FinPartLevel

/-!
# Null frontiers for the staircase cells and the core

`Work.EKLComp.levelCell e U C m` is the `m`-th staircase cell `U (e.symm m) ∩ ⋂_{j < m} C (e.symm j)`
and `Work.EKLComp.levelCore C = ⋂ i, C i` is the residual core (see
`Submission/Work/EKLComp/FinPartLevel.lean`).

The point of this file is that a finite intersection of sets with null frontier again has null
frontier: the frontier of an intersection is contained in the union of the frontiers, and a finite
union of null sets is null.  Since both the cells and the core are finite intersections of the
given families `U`, `C`, this gives that every cell and the core have null frontier as soon as
all the `U i` and `C i` do.
-/

namespace Work.EKLComp

open Set MeasureTheory

/-- The frontier of an intersection is contained in the union of the frontiers.  (The index type
only needs to be finite, so that `interior` commutes with the intersection.) -/
theorem frontier_iInter_subset_iUnion {X : Type*} [TopologicalSpace X] {ι : Type*} [Finite ι]
    (s : ι → Set X) : frontier (⋂ i, s i) ⊆ ⋃ i, frontier (s i) := by
  intro x hx
  obtain ⟨hcl, hni⟩ := hx
  rw [interior_iInter_of_finite] at hni
  simp only [mem_iInter] at hni
  push Not at hni
  obtain ⟨i, hi⟩ := hni
  exact mem_iUnion.mpr ⟨i, closure_mono (iInter_subset s i) hcl, hi⟩

/-- A finite intersection of sets with null frontier has null frontier. -/
theorem measure_frontier_iInter_eq_zero {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    {ι : Type*} [Fintype ι] (μ : MeasureTheory.Measure X) (s : ι → Set X)
    (h : ∀ i, μ (frontier (s i)) = 0) : μ (frontier (⋂ i, s i)) = 0 :=
  measure_mono_null (frontier_iInter_subset_iUnion s) (measure_iUnion_null h)

/-- A binary intersection of sets with null frontier has null frontier. -/
theorem measure_frontier_inter_eq_zero {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    (μ : MeasureTheory.Measure X) {s t : Set X} (hs : μ (frontier s) = 0)
    (ht : μ (frontier t) = 0) : μ (frontier (s ∩ t)) = 0 := by
  refine measure_mono_null (frontier_inter_subset s t |>.trans ?_) (measure_union_null hs ht)
  rintro x (h | h)
  · exact Or.inl h.1
  · exact Or.inr h.2

theorem frontier_levelCell_levelCore {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    {ι : Type*} [Fintype ι] (μ : MeasureTheory.Measure X)
    (e : ι ≃ Fin (Fintype.card ι)) (U C : ι → Set X)
    (hU : ∀ i, μ (frontier (U i)) = 0) (hC : ∀ i, μ (frontier (C i)) = 0) :
    (∀ m, μ (frontier (Work.EKLComp.levelCell e U C m)) = 0) ∧
      μ (frontier (Work.EKLComp.levelCore C)) = 0 := by
  constructor
  · intro m
    have h2 : μ (frontier (⋂ j : {j : Fin (Fintype.card ι) // j < m}, C (e.symm j.1))) = 0 :=
      measure_frontier_iInter_eq_zero μ _ (fun j => hC _)
    have h1 : μ (frontier (U (e.symm m))) = 0 := hU _
    simpa only [Work.EKLComp.levelCell] using measure_frontier_inter_eq_zero μ h1 h2
  · simpa only [Work.EKLComp.levelCore] using measure_frontier_iInter_eq_zero μ C hC

end Work.EKLComp
