import Mathlib
import Submission.Work.Diff.STE.B3.Data

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.B3

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

/-- **The within-derivative of the flat-coordinate transition.**  If `χ i` does not vanish on `s`
and `ζ j (pt i y) ≠ 0`, then on `s` the map `y' ↦ coord (x₀ j) (pt i y')` (the flat coordinate of
the chart-`i` point in the chart `j`) has derivative the composition of the coordinate
identification with the chart transition `tangentCoordChange (x₀ i) (x₀ j)` at `pt i y`. -/
theorem hasFDerivWithinAt_coord_pt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (i j : ι₀)
    (s : Set (Fin (Module.finrank ℝ E) → ℝ))
    (hs : ∀ y' ∈ s, D.χ i y' ≠ 0 ∧ D.ζ j (D.pt i y') ≠ 0)
    {y : Fin (Module.finrank ℝ E) → ℝ} (hy : y ∈ s) :
    HasFDerivWithinAt (fun y' => Work.Diff.STE.coord (I := I) (D.x₀ j) (D.pt i y'))
      (((Module.finBasis ℝ E).equivFun.toContinuousLinearMap) ∘L
        (tangentCoordChange (I := I) (D.x₀ i) (D.x₀ j) (D.pt i y)) ∘L
        ((Module.finBasis ℝ E).equivFun.symm.toContinuousLinearMap)) s y := by
  classical
  -- smooth manifolds are `C¹`
  have hMf : IsManifold I 1 M :=
    IsManifold.of_le (m := 1) (n := ((⊤ : ENat) : WithTop ENat)) (by simp)
  -- the point `y` has nonvanishing cut-off, hence its flat coordinate lies in the chart target
  have hχy : D.χ i y ≠ 0 := (hs y hy).1
  have hζy : D.ζ j (D.pt i y) ≠ 0 := (hs y hy).2
  have hty : Work.Diff.STE.flatToE (I := I) (D.x₀ i) y ∈ (extChartAt I (D.x₀ i)).target :=
    D.hχtsup i y (subset_closure (Function.mem_support.mpr hχy))
  have hpty : (extChartAt I (D.x₀ i)) (D.pt i y)
      = Work.Diff.STE.flatToE (I := I) (D.x₀ i) y :=
    (extChartAt I (D.x₀ i)).right_inv hty
  have hsrc_i : D.pt i y ∈ (extChartAt I (D.x₀ i)).source :=
    (extChartAt I (D.x₀ i)).map_target hty
  have hsrc_j : D.pt i y ∈ (extChartAt I (D.x₀ j)).source := (D.hζsupp j _ hζy).1
  -- the change of chart, as a map on the model space, within `range I`
  have h1 : HasFDerivWithinAt
      (fun z : E => (extChartAt I (D.x₀ j)) ((extChartAt I (D.x₀ i)).symm z))
      (tangentCoordChange (I := I) (D.x₀ i) (D.x₀ j) (D.pt i y)) (Set.range I)
      (Work.Diff.STE.flatToE (I := I) (D.x₀ i) y) := by
    have h := hasFDerivWithinAt_tangentCoordChange (I := I) (x := D.x₀ i) (y := D.x₀ j)
      (z := D.pt i y) ⟨hsrc_i, hsrc_j⟩
    simpa only [Function.comp_def, hpty] using h
  -- postcompose with the coordinate identification `E ≃ ℝⁿ`
  have h2 : HasFDerivWithinAt
      (fun z : E => (Module.finBasis ℝ E).equivFun
        ((extChartAt I (D.x₀ j)) ((extChartAt I (D.x₀ i)).symm z)))
      (((Module.finBasis ℝ E).equivFun.toContinuousLinearMap) ∘L
        (tangentCoordChange (I := I) (D.x₀ i) (D.x₀ j) (D.pt i y)))
      (Set.range I) (Work.Diff.STE.flatToE (I := I) (D.x₀ i) y) :=
    (ContinuousLinearMap.hasFDerivAt
      (((Module.finBasis ℝ E).equivFun.toContinuousLinearMap) :
        E →L[ℝ] (Fin (Module.finrank ℝ E) → ℝ))
      ).comp_hasFDerivWithinAt _ h1
  -- the affine parametrisation of the chart at `x₀ i` by the flat coordinates
  have hG : HasFDerivWithinAt (fun z : Fin (Module.finrank ℝ E) → ℝ =>
      Work.Diff.STE.flatToE (I := I) (D.x₀ i) z)
      ((Module.finBasis ℝ E).equivFun.symm.toContinuousLinearMap) s y := by
    have h1' : HasFDerivAt (fun z : Fin (Module.finrank ℝ E) → ℝ =>
        (Module.finBasis ℝ E).equivFun ((extChartAt I (D.x₀ i)) (D.x₀ i)) + z)
        (ContinuousLinearMap.id ℝ (Fin (Module.finrank ℝ E) → ℝ)) y :=
      (hasFDerivAt_id y).const_add _
    have h2' := (ContinuousLinearMap.hasFDerivAt
      (((Module.finBasis ℝ E).equivFun.symm.toContinuousLinearMap) :
        (Fin (Module.finrank ℝ E) → ℝ) →L[ℝ] E)).comp _ h1'
    have h3 : HasFDerivWithinAt (fun z : Fin (Module.finrank ℝ E) → ℝ =>
        ((Module.finBasis ℝ E).equivFun.symm.toContinuousLinearMap)
          ((Module.finBasis ℝ E).equivFun ((extChartAt I (D.x₀ i)) (D.x₀ i)) + z))
        ((Module.finBasis ℝ E).equivFun.symm.toContinuousLinearMap) s y := by
      simpa only [Function.comp_def, ContinuousLinearMap.comp_id] using h2'.hasFDerivWithinAt
    exact h3.congr (fun z _ => rfl) rfl
  -- the parametrisation lands in `range I` on `s`
  have hmap : Set.MapsTo (fun z : Fin (Module.finrank ℝ E) → ℝ =>
      Work.Diff.STE.flatToE (I := I) (D.x₀ i) z) s (Set.range I) := by
    intro y' hy'
    exact extChartAt_target_subset_range (I := I) (D.x₀ i)
      (D.hχtsup i y' (subset_closure (Function.mem_support.mpr (hs y' hy').1)))
  have hmain : HasFDerivWithinAt
      (fun y' => (Module.finBasis ℝ E).equivFun ((extChartAt I (D.x₀ j)) (D.pt i y')))
      (((Module.finBasis ℝ E).equivFun.toContinuousLinearMap) ∘L
        (tangentCoordChange (I := I) (D.x₀ i) (D.x₀ j) (D.pt i y)) ∘L
        ((Module.finBasis ℝ E).equivFun.symm.toContinuousLinearMap)) s y :=
    h2.comp y hG hmap
  -- pass from `equivFun (extChartAt _ _)` to `coord`, which differs by a constant
  refine (hmain.sub_const ((Module.finBasis ℝ E).equivFun
    ((extChartAt I (D.x₀ j)) (D.x₀ j)))).congr ?_ ?_
  · intro y' _
    simp only [Work.Diff.STE.coord_apply]
  · simp only [Work.Diff.STE.coord_apply]

end Work.Diff.STE.B3
