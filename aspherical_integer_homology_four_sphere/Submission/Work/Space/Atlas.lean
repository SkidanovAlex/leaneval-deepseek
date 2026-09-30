/-
# Finite atlases and the chart-at structure of `M̂`

This file is the second layer of the area `Space/`: how a **finite** list of charts on a topological
space `M` produces the `ChartedSpace` structure used everywhere in the project, with the *priority*
convention for `chartAt`.

## Conventions

* `E4 := EuclideanSpace ℝ (Fin 4)` and `I4 := 𝓘(ℝ, E4)`.
* `FinAtlas M` is a finite list `chart : Fin n → OpenPartialHomeomorph M E4` whose sources cover
  `M`; it is a **class**, so a space with a finite atlas automatically carries the
  `ChartedSpace E4 M` structure `Work.Space.instChartedSpaceOfFinAtlas`.
* the priority index `indexOf x` of a point is the **least** index `i` with `x ∈ (chart i).source`;
  `chartAt x := chart (indexOf x)`.  By construction `chartAt E4 x = A.pchartAt x` (`rfl`).

## Main results

* `Work.Space.instChartedSpaceOfFinAtlas` — the `ChartedSpace E4 M` instance,
  `atlas = Set.range chart`, `chartAt = chart ∘ indexOf`.
* `Work.Space.FinAtlas.indexOf_le`, `indexOf_mem` — the priority index is the least.
* `Work.Space.isManifold_of_contDiffOn_transitions` — `IsManifold I4 n M` from the smoothness of
  the finitely many transitions.
* `Work.Space.secondCountable_of_finAtlas` — `SecondCountableTopology M` for a compact `M`.
* `Work.Space.tangentCoordChange_eq_one_of_chartAt_eq` — the tangent coordinate change between two
  points with the same preferred chart is the identity.
-/
import Mathlib
import Submission.Work.Space.Assembly

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open Set Topology Function Filter
open scoped Manifold ContDiff Topology

namespace Work.Space

/-- The chart model `ℝ⁴` of the whole project. -/
abbrev E4 := EuclideanSpace ℝ (Fin 4)

/-- The model-with-corners structure of the chart model. -/
abbrev I4 := 𝓘(ℝ, E4)

/-- A **finite atlas** on a topological space `M`, modelled on `E4`: a finite list of charts whose
sources cover `M`. -/
class FinAtlas (M : Type*) [TopologicalSpace M] where
  /-- The number of charts. -/
  n : ℕ
  /-- The charts. -/
  chart : Fin n → OpenPartialHomeomorph M E4
  /-- The charts cover `M`. -/
  cover : ∀ x : M, ∃ i, x ∈ (chart i).source

namespace FinAtlas

variable {M : Type*} [TopologicalSpace M] (A : FinAtlas M)

/-- The finite set of chart indices whose source contains `x`. -/
def idxSet (x : M) : Finset (Fin A.n) := by
  classical
  exact Finset.univ.filter (fun i => x ∈ (A.chart i).source)

theorem mem_idxSet {x : M} {i : Fin A.n} : i ∈ A.idxSet x ↔ x ∈ (A.chart i).source := by
  classical
  simp [idxSet]

theorem idxSet_nonempty (x : M) : (A.idxSet x).Nonempty := by
  obtain ⟨i, hi⟩ := A.cover x
  exact ⟨i, (A.mem_idxSet).mpr hi⟩

/-- The **priority index** of a point: the least chart index whose source contains it. -/
def indexOf (x : M) : Fin A.n := (A.idxSet x).min' (A.idxSet_nonempty x)

theorem indexOf_mem (x : M) : x ∈ (A.chart (A.indexOf x)).source :=
  (A.mem_idxSet).mp (Finset.min'_mem _ _)

theorem indexOf_le {x : M} {i : Fin A.n} (hi : x ∈ (A.chart i).source) : A.indexOf x ≤ i :=
  Finset.min'_le _ _ ((A.mem_idxSet).mpr hi)

/-- The preferred chart of a point, as a member of the atlas. -/
def pchartAt (x : M) : OpenPartialHomeomorph M E4 := A.chart (A.indexOf x)

theorem pchartAt_mem_source (x : M) : x ∈ (A.pchartAt x).source := A.indexOf_mem x

/-- The charted space structure of a finite atlas, with the priority convention. -/
@[reducible]
def toChartedSpace : ChartedSpace E4 M where
  atlas := Set.range A.chart
  chartAt := A.pchartAt
  mem_chart_source := A.pchartAt_mem_source
  chart_mem_atlas x := ⟨A.indexOf x, rfl⟩

@[simp] theorem pchartAt_eq_chart (x : M) : A.pchartAt x = A.chart (A.indexOf x) := rfl

theorem pchartAt_mem_range (x : M) : A.pchartAt x ∈ Set.range A.chart := ⟨A.indexOf x, rfl⟩

theorem iUnion_source : (⋃ i, (A.chart i).source) = univ := by
  ext x
  simp only [mem_iUnion, mem_univ, iff_true]
  exact ⟨A.indexOf x, A.indexOf_mem x⟩

/-- **The priority index is locally constant, provided the sources of the strictly
lower-priority charts do not accumulate at `x`.** -/
theorem indexOf_eventually_eq (x : M)
    (h : ∀ i : Fin A.n, i < A.indexOf x → x ∉ closure (A.chart i).source) :
    ∀ᶠ y in 𝓝 x, A.indexOf y = A.indexOf x := by
  set i₀ := A.indexOf x with hi₀
  have hsource : ∀ᶠ y in 𝓝 x, y ∈ (A.chart i₀).source :=
    (A.chart i₀).open_source.mem_nhds (A.indexOf_mem x)
  have hnotmem : ∀ᶠ y in 𝓝 x, ∀ i : Fin A.n, i < i₀ → y ∉ (A.chart i).source := by
    refine Filter.eventually_all.mpr fun i => ?_
    by_cases hi : i < i₀
    · have hcl : x ∈ (closure (A.chart i).source)ᶜ := h i hi
      filter_upwards [isOpen_compl_iff.mpr isClosed_closure |>.mem_nhds hcl] with y hy _
      exact fun hs => hy (subset_closure hs)
    · filter_upwards with y hy
      exact absurd hy hi
  filter_upwards [hsource, hnotmem] with y hy hyn
  have hmem : i₀ ∈ A.idxSet y := (A.mem_idxSet).mpr hy
  refine le_antisymm (Finset.min'_le _ _ hmem) ?_
  refine le_of_not_gt fun hlt => ?_
  exact hyn (A.indexOf y) hlt (A.indexOf_mem y)

end FinAtlas

/-- **A space with a finite atlas is a charted space**, with the priority chart convention. -/
@[reducible]
instance instChartedSpaceOfFinAtlas {M : Type*} [TopologicalSpace M] [A : FinAtlas M] :
    ChartedSpace E4 M :=
  A.toChartedSpace

section Instances

variable {M : Type*} [TopologicalSpace M] [A : FinAtlas M] [IsManifold I4 1 M]

theorem chartAt_finAtlas (x : M) :
    (chartAt E4 x : OpenPartialHomeomorph M E4) = A.pchartAt x := rfl

theorem atlas_finAtlas : atlas E4 M = Set.range A.chart := rfl

/-- **The tangent coordinate change between two points with the same preferred chart is the
identity.** -/
theorem tangentCoordChange_eq_one_of_chartAt_eq {x p : M}
    (h : chartAt E4 p = chartAt E4 x) (hp : p ∈ (chartAt E4 x).source) :
    tangentCoordChange I4 x p p = 1 := by
  have h2 : achart E4 p = achart E4 x := by
    refine Subtype.ext ?_
    rw [coe_achart, coe_achart, h]
  have hsrc : p ∈ (extChartAt I4 x).source := by
    simpa [extChartAt_coe, modelWithCornersSelf_coe] using hp
  refine ContinuousLinearMap.ext fun v => ?_
  rw [show tangentCoordChange I4 x p = tangentCoordChange I4 x x from by
        simp only [tangentCoordChange, h2]]
  simpa using tangentCoordChange_self (v := v) hsrc

/-- The same statement in the form used for the metric: the coordinate tangent vector of the
chart at `x` is carried to itself by the tangent coordinate change. -/
theorem tangentCoordChange_apply_of_chartAt_eq {x p : M}
    (h : chartAt E4 p = chartAt E4 x) (hp : p ∈ (chartAt E4 x).source) (a : E4) :
    tangentCoordChange I4 x p p a = a := by
  rw [tangentCoordChange_eq_one_of_chartAt_eq h hp]
  rfl

/-- **The chart-frame vector is the tangent coordinate change.** -/
theorem symmL_trivializationAt_eq (x p : M) (hp : p ∈ (chartAt E4 x).source) (a : E4) :
    ((trivializationAt E4 (TangentSpace I4) x).symmL ℝ p a : TangentSpace I4 p) =
      (tangentCoordChange I4 x p p a : TangentSpace I4 p) := by
  rw [TangentBundle.symmL_trivializationAt_eq_core (I := I4) hp]
  rfl

end Instances

section Manifold

variable {M : Type*} [TopologicalSpace M] [A : FinAtlas M]

/-- **A compact space with a finite atlas is second countable.** -/
theorem secondCountable_of_finAtlas [CompactSpace M] : SecondCountableTopology M :=
  ChartedSpace.secondCountable_of_sigmaCompact E4 M

end Manifold

section ManifoldTransitions

variable {M : Type*} [TopologicalSpace M] (A : FinAtlas M)

/-- **`IsManifold` from the smoothness of the finite list of transitions.** -/
theorem isManifold_of_contDiffOn_transitions (n : ℕ∞ω)
    (h : ∀ i j : Fin A.n, ContDiffOn ℝ n ((A.chart j : M → E4) ∘ (A.chart i).symm)
      ((A.chart i).symm ≫ₕ A.chart j).source) :
    IsManifold I4 n M := by
  refine isManifold_of_contDiffOn I4 n M ?_
  rintro e e' ⟨i, rfl⟩ ⟨j, rfl⟩
  simpa [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, ModelWithCorners.range_eq_univ,
    Function.comp_assoc] using h i j

/-- The `C^∞` form of `isManifold_of_contDiffOn_transitions`. -/
theorem isManifold_of_contDiffOn_transitions_infty
    (h : ∀ i j : Fin A.n, ContDiffOn ℝ ∞ ((A.chart j : M → E4) ∘ (A.chart i).symm)
      ((A.chart i).symm ≫ₕ A.chart j).source) :
    IsManifold I4 ∞ M :=
  isManifold_of_contDiffOn_transitions A ∞ h

end ManifoldTransitions

end Work.Space
