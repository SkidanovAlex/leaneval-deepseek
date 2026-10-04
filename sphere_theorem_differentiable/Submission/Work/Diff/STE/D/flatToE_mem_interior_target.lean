import Mathlib
import Submission.Work.Diff.STE.B3.Comp

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The `σ`-ball of flat coordinates lies in the *interior* of the chart target

The Layer B3 data `D : B3Data ι₀ g₀` of the short-time-existence scheme carries the hypothesis
`D.htarget i` that the **closed** flat coordinate ball of radius `2 σ i` around the chart centre
`D.x₀ i` is mapped into the chart target of `D.x₀ i`:

`∀ z, ‖z‖ ≤ 2 * D.σ i → flatToE (x₀ i) z ∈ (extChartAt I (x₀ i)).target`.

Several places in Layer D need more: smoothness of the chart inverse *near* the point, i.e. that
the image of the (smaller) `σ i`-ball lies in the **interior** of the target.  This file proves
exactly that.

The mathematical point is that `htarget` is stated on a *strictly larger* ball than the one used:
the affine chart coordinate `flatToE x₀` is an open map of the flat coordinate space onto `E`
(it is a translation composed with the linear inverse of `Module.finBasis ℝ E`, hence an open map
between finite-dimensional real vector spaces).  Therefore the image of the **open** flat ball of
radius `2 σ i` is an open subset of `E` contained in the chart target, and it contains the image of
the whole `σ i`-ball.  So `flatToE x₀ z` is an interior point of the target for every `‖z‖ ≤ σ i`.

(Note that no boundarylessness assumption on `I` is needed: the hypothesis `htarget` on the larger
ball *forces* the flat ball to be an interior part of the chart target.)
-/

namespace Work.Diff.STE.D

open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle Set Metric Filter

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- The flat coordinate map `flatToE x₀` of a chart is an **open map**: it is the composition of
the translation `z ↦ (finBasis.coord of the chart centre) + z` with the linear equivalence
`(Module.finBasis ℝ E).equivFun.symm : (Fin n → ℝ) ≃ₗ[ℝ] E`, which is a surjective linear map with
finite-dimensional codomain. -/
lemma isOpenMap_flatToE (x₀ : M) : IsOpenMap (flatToE (I := I) x₀) := by
  unfold flatToE
  exact (LinearMap.isOpenMap_of_finiteDimensional _
      (Module.finBasis ℝ E).equivFun.symm.surjective).comp (isOpenMap_add_left _)

/-- **The `s`-ball of flat coordinates of a chart lies in the interior of the chart target**, as
soon as the whole `2s`-ball (with `s > 0`) is mapped into the target.

This is the quantitative form of `B3Data.htarget` that the smoothness arguments of Layer D need:
the hypothesis on the strictly larger ball pins the chart centre away from the boundary of the
target, so the `s`-ball consists of interior points of the target. -/
lemma flatToE_mem_interior_target_of (x₀ : M) {s : ℝ} (hs : 0 < s)
    (ht : ∀ w : Fin (Module.finrank ℝ E) → ℝ, ‖w‖ ≤ 2 * s →
      flatToE (I := I) x₀ w ∈ (extChartAt I x₀).target)
    (z : Fin (Module.finrank ℝ E) → ℝ) (hz : ‖z‖ ≤ s) :
    flatToE (I := I) x₀ z ∈ interior ((extChartAt I x₀).target) := by
  -- the flat coordinate `z` lies in the open ball of radius `2s`, on which `ht` holds
  have hzK : z ∈ ball (0 : Fin (Module.finrank ℝ E) → ℝ) (2 * s) := by
    rw [mem_ball_iff_norm, sub_zero]; linarith
  -- hence the image of that open ball is contained in the chart target
  have hsub : flatToE (I := I) x₀ '' ball (0 : Fin (Module.finrank ℝ E) → ℝ) (2 * s)
      ⊆ (extChartAt I x₀).target := by
    rintro y ⟨w, hw, rfl⟩
    rw [mem_ball_iff_norm, sub_zero] at hw
    exact ht w (le_of_lt hw)
  -- `z` is an interior point of the open ball, and `flatToE x₀` is an open map
  have hz' : z ∈ interior (ball (0 : Fin (Module.finrank ℝ E) → ℝ) (2 * s)) := by
    rw [isOpen_ball.interior_eq]; exact hzK
  exact interior_mono hsub
    ((IsOpenMap.image_interior_subset (isOpenMap_flatToE (I := I) x₀) _) ⟨z, hz', rfl⟩)

theorem flatToE_mem_interior_target
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (i : ι₀)
    (z : Fin (Module.finrank ℝ E) → ℝ) (hz : ‖z‖ ≤ D.σ i) :
    Work.Diff.STE.flatToE (I := I) (D.x₀ i) z ∈
      interior ((extChartAt I (D.x₀ i)).target) :=
  flatToE_mem_interior_target_of (I := I) (M := M) (s := D.σ i)
    (D.x₀ i) (D.hσ i) (D.htarget i) z hz

end Work.Diff.STE.D
