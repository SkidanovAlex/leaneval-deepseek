import Mathlib
import Submission.Work.Diff.STE.B3.Comp

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.D

/-- **The inverse of the affine flat coordinates.**  For any vector `x` of the model space, the
`flatToE`-image of the difference of the `finBasis`-coordinates of `x` and of the chart centre is
`x` itself.  (This is the pointwise form of `flatToE_coord`, valid for an arbitrary `x : E`.) -/
lemma flatToE_sub_chartCentre {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    (x₀ : M) (x : E) :
    flatToE (I := I) x₀ ((Module.finBasis ℝ E).equivFun x
      - (Module.finBasis ℝ E).equivFun ((extChartAt I x₀) x₀)) = x := by
  rw [flatToE]
  have h : (Module.finBasis ℝ E).equivFun ((extChartAt I x₀) x₀)
      + ((Module.finBasis ℝ E).equivFun x
        - (Module.finBasis ℝ E).equivFun ((extChartAt I x₀) x₀))
      = (Module.finBasis ℝ E).equivFun x := by abel
  rw [h, LinearEquiv.symm_apply_apply]

/-- **A point whose flat coordinate is within `σ` of a chart centre is an interior point.**

Let `x₀ : M` and `σ > 0`, and suppose that the flat `2σ`-ball around the chart centre maps into the
chart target of `x₀` (`hball`).  If the flat coordinate of `p'` is within `σ` of `0` (`hbound`),
then the chart value of `p'` is an *interior* point of `Set.range I`.

Proof hint: with `Φ := (Module.finBasis ℝ E).equivFun` and `q := (extChartAt I x₀) x₀`, the open set
`W := {x : E | ‖Φ x - Φ q‖ < 2 * σ}` contains `p := (extChartAt I x₀) p'` (by `hbound` and
`0 < σ`) and is contained in `Set.range I`: for `x ∈ W`, the vector `z := Φ x - Φ q` has norm
`< 2σ`, so `flatToE x₀ z ∈ (extChartAt I x₀).target ⊆ Set.range I` by `hball`, and
`flatToE x₀ z = Φ.symm (Φ q + z) = Φ.symm (Φ x) = x`.  `W` is open (`isOpen_lt` plus continuity of
`Φ`), so `p ∈ interior (Set.range I)` by `interior_maximal`.  (Useful existing lemma:
`Work.Diff.STE.B3.flatToE_coord`, `Submission/Work/Diff/STE/B3/continuousAt_mat_Rstar.lean`.)

This is the crux of the smoothness of the chart transition `z ↦ coord (x₀ i) (pt j z)`: combined
with the chart-independence of interior points (`ModelWithCorners.isInteriorPoint_iff_of_mem_atlas`,
`mem_interior_range_iff_of_mem_atlas`) it shows that the chart value of such a point lies in the
*interior* of the chart target, so that the inverse chart is genuinely smooth there. -/
theorem interior_of_flatBall
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    (x₀ : M) (σ : ℝ) (hσ : 0 < σ) (p' : M)
    (hball : ∀ z : Fin (Module.finrank ℝ E) → ℝ, ‖z‖ ≤ 2 * σ →
      Work.Diff.STE.flatToE (I := I) x₀ z ∈ (extChartAt I x₀).target)
    (hbound : ‖Work.Diff.STE.coord (I := I) x₀ p'‖ ≤ σ) :
    (extChartAt I x₀) p' ∈ interior (Set.range I) := by
  set Φ : E ≃ₗ[ℝ] (Fin (Module.finrank ℝ E) → ℝ) := (Module.finBasis ℝ E).equivFun with hΦ
  set q : E := (extChartAt I x₀) x₀ with hq
  set W : Set E := {x : E | ‖Φ x - Φ q‖ < 2 * σ} with hW
  have hcoord : Φ ((extChartAt I x₀) p') - Φ q = coord (I := I) x₀ p' := by
    rw [hΦ, hq]
    rfl
  have hpW : (extChartAt I x₀) p' ∈ W := by
    rw [hW]
    change ‖Φ ((extChartAt I x₀) p') - Φ q‖ < 2 * σ
    rw [hcoord]
    linarith
  have hsub : W ⊆ Set.range I := by
    intro x hx
    rw [hW] at hx
    have hxle : ‖Φ x - Φ q‖ ≤ 2 * σ := le_of_lt hx
    have hm : flatToE (I := I) x₀ (Φ x - Φ q) ∈ (extChartAt I x₀).target := hball _ hxle
    have hfx : flatToE (I := I) x₀ (Φ x - Φ q) = x := by
      rw [hΦ, hq]
      exact flatToE_sub_chartCentre (I := I) x₀ x
    rw [hfx] at hm
    exact extChartAt_target_subset_range x₀ hm
  have hopen : IsOpen W := by
    rw [hW]
    exact isOpen_lt (continuous_norm.comp
      (((Φ : E →ₗ[ℝ] (Fin (Module.finrank ℝ E) → ℝ)).continuous_of_finiteDimensional).sub
        continuous_const)) continuous_const
  exact interior_maximal hsub hopen hpW

end Work.Diff.STE.D
