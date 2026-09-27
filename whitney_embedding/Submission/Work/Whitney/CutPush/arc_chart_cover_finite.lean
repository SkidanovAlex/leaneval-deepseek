import Mathlib

/-!
# The finite chart cover of an arc (M1, piece (ii), first half)

`Work.Whitney.CutPush.exists_finite_arc_chart_cover`: for a continuous arc `δ : ℝ → M` in a charted
`n`-manifold and a compact parameter interval `[a,b]`, there are finitely many parameter points
`i : ↥t` (a `Finset` of the interval) and open parameter-neighbourhoods `s i ∋ i` such that the
`δ (s i)` all lie in the source of the chart `chartAt (EuclideanSpace ℝ (Fin n)) (δ i)`.

This is the cover that M1's frame-field construction consumes: on each `s i` the chart representation
`u ↦ A₁ (f (c_i.symm u))` provides the transverse derivative family, and
`Work.Whitney.CutPush.range_mfderiv_eq_range_fderiv_chartAt` identifies its range with the tangent
plane of the finger.  The frames produced locally are then glued along the cover by
`Work.Whitney.CutPush.exists_smooth_frame_of_blendOn` (the remaining half of (ii)).
-/

namespace Work.Whitney.CutPush

open scoped Manifold ContDiff Topology
open Set

/-- **The finite chart cover of an arc.** -/
theorem exists_finite_arc_chart_cover {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [T2Space M] [LocallyCompactSpace M]
    (δ : ℝ → M) (hδ : Continuous δ) (a b : ℝ) (hab : a ≤ b) :
    ∃ (t : Finset ↥(Set.Icc a b)) (s : ↥t → Set ℝ),
      (∀ i, IsOpen (s i)) ∧ Set.Icc a b ⊆ ⋃ i, s i ∧
      (∀ i, ∀ u ∈ s i,
        δ u ∈ (chartAt (EuclideanSpace ℝ (Fin n))
          (δ ((i.1 : ↥(Set.Icc a b)) : ℝ))).source) := by
  classical
  have hUopen : ∀ u : ↥(Set.Icc a b),
      IsOpen (δ ⁻¹' (chartAt (EuclideanSpace ℝ (Fin n)) (δ (u : ℝ))).source) :=
    fun u => (chartAt (EuclideanSpace ℝ (Fin n)) (δ (u : ℝ))).open_source.preimage hδ
  have hcov : Set.Icc a b ⊆ ⋃ u : ↥(Set.Icc a b),
      δ ⁻¹' (chartAt (EuclideanSpace ℝ (Fin n)) (δ (u : ℝ))).source := by
    intro u hu
    exact Set.mem_iUnion.mpr
      ⟨(⟨u, hu⟩ : ↥(Set.Icc a b)), mem_chart_source (EuclideanSpace ℝ (Fin n)) (δ u)⟩
  obtain ⟨t, ht⟩ := isCompact_Icc.elim_finite_subcover
    (fun u : ↥(Set.Icc a b) => δ ⁻¹' (chartAt (EuclideanSpace ℝ (Fin n)) (δ (u : ℝ))).source)
    hUopen hcov
  refine ⟨t, fun i => δ ⁻¹' (chartAt (EuclideanSpace ℝ (Fin n))
      (δ ((i.1 : ↥(Set.Icc a b)) : ℝ))).source, fun i => hUopen i.1, ?_, ?_⟩
  · intro u hu
    rcases Set.mem_iUnion.mp (ht hu) with ⟨i, hi⟩
    rcases Set.mem_iUnion.mp hi with ⟨hit, hmem⟩
    exact Set.mem_iUnion.mpr ⟨(⟨i, hit⟩ : ↥t), hmem⟩
  · intro i u hu
    exact hu

end Work.Whitney.CutPush
