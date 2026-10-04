import Mathlib
import Submission.Work.Diff.STE.D.R_Rstar_expansion2
import Submission.Work.Diff.STE.B3.hasFDerivWithinAt_coord_pt
import Submission.Work.Diff.STE.B3.BPair_Rstar
import Submission.Work.Diff.STE.B3.BPairDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The flat chart transition `tMapFun D i j` is injective on `goodSet`, with nowhere-vanishing
Jacobian

`Work.Diff.STE.D.tMapFun D i j z = coord i (pt j z)` is the transition map, in flat coordinates,
from the chart `j` to the chart `i`.  The set `Work.Diff.STE.D.goodSet D i j` is the region on which
*all* the chart expressions are genuine:

* `flatToE (x₀ j) z` lies in the **interior** of the chart-`j` target (so that `pt j` is smooth at
  `z` and the chart `j` is genuine there),
* `pt j z` lies in the source of the chart `i` (so that `coord i (pt j z)` is genuine), and
* the chart-`i` image of `pt j z` lies in the interior of the chart-`i` target.

The content of this file is the pair of facts needed for the change-of-variables formula on
`goodSet` (see `Work.Diff.STE.B3.CSq_period_comp_arg_le_of_isOpen`):

* `injOn_tMapFun_goodSet` — the transition is injective on `goodSet`;
* `tMapFun_det_ne_zero` — at every point of `goodSet` the Jacobian determinant of the transition is
  non-zero.

Both statements are made **without** a `[T2Space M]` hypothesis (the target statement has none), so
the existing T2Space-tainted `Work.Diff.STE.D.isOpen_goodSet` / `tMapFun_contDiffOn` cannot be used;
the proofs below are self-contained in this respect.

## The proof of the two halves

*Injectivity.*  If `coord i (pt j z) = coord i (pt j z')`, then the `finBasis`-coordinates agree,
hence (the two points lying in the source of the chart `i`) `pt j z = pt j z'`; applying the
(injective on its target) chart `j` gives `flatToE (x₀ j) z = flatToE (x₀ j) z'`, and the affine
map `flatToE (x₀ j)` is injective.

*Non-vanishing Jacobian.*  `pt j = (extChartAt I (x₀ j)).symm ∘ flatToE (x₀ j)`, so on `goodSet`
the transition is the composite of the affine chart parametrisation with the *change of chart*
`(extChartAt I (x₀ i)) ∘ (extChartAt I (x₀ j)).symm`, read in the `finBasis` coordinates.  The chain
rule (`hasFDerivWithinAt_tangentCoordChange` for the change of chart, the affine derivative for
`flatToE`) gives

`fderiv ℝ (tMapFun D i j) z = L ∘L tangentCoordChange I (x₀ j) (x₀ i) (pt j z) ∘L L⁻¹`

with `L = (finBasis ℝ E).equivFun.toContinuousLinearMap`; this is exactly
`Work.Diff.STE.B3.transDeriv D j i z`.  Its determinant is that of `tangentCoordChange`, which is
non-zero because `tangentCoordChange I (x₀ j) (x₀ i) (pt j z)` and
`tangentCoordChange I (x₀ i) (x₀ j) (pt j z)` compose to the identity
(`tangentCoordChange_comp` at the triple `(x₀ j, x₀ i, x₀ j)` followed by `tangentCoordChange_self`),
and the determinant is multiplicative.
-/

namespace Work.Diff.STE.B3

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
  {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}

/-- **`goodSet` is a neighbourhood of each of its points.**  This is the `[T2Space M]`-free
counterpart of the openness statement `Work.Diff.STE.D.isOpen_goodSet`: the three defining conditions
are preimages of open sets under maps that are continuous at `z` (the chart parametrisation
`flatToE (x₀ j)`; `pt j`, whose smoothness at an *interior* target point is
`Work.Diff.STE.D.pt_contMDiffAt_of_mem_interior`; and the chart `extChartAt I (x₀ i)` on its
source). -/
lemma tMapFun_goodSet_mem_nhds (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (i j : ι₀)
    {z : Fin (Module.finrank ℝ E) → ℝ}
    (hz : z ∈ Work.Diff.STE.D.goodSet (I := I) (M := M) D i j) :
    Work.Diff.STE.D.goodSet (I := I) (M := M) D i j ∈ 𝓝 z := by
  have hpt : ContinuousAt (fun w => D.pt j w) z :=
    (Work.Diff.STE.D.pt_contMDiffAt_of_mem_interior (I := I) D j z hz.1).continuousAt
  have hflat : ContinuousAt (Work.Diff.STE.flatToE (I := I) (D.x₀ j)) z :=
    (Work.Diff.STE.B3.flatToE_contDiff (I := I) (D.x₀ j)).continuous.continuousAt
  have h1 : Work.Diff.STE.flatToE (I := I) (D.x₀ j) ⁻¹'
      interior ((extChartAt I (D.x₀ j)).target) ∈ 𝓝 z :=
    hflat.preimage_mem_nhds (isOpen_interior.mem_nhds hz.1)
  have h2 : D.pt j ⁻¹' (extChartAt I (D.x₀ i)).source ∈ 𝓝 z :=
    hpt.preimage_mem_nhds ((isOpen_extChartAt_source (I := I) (D.x₀ i)).mem_nhds hz.2.1)
  have h3 : (fun w => (extChartAt I (D.x₀ i)) (D.pt j w)) ⁻¹'
      interior ((extChartAt I (D.x₀ i)).target) ∈ 𝓝 z :=
    ((continuousAt_extChartAt' (I := I) hz.2.1).comp hpt).preimage_mem_nhds
      (isOpen_interior.mem_nhds hz.2.2)
  refine Filter.mem_of_superset (Filter.inter_mem (Filter.inter_mem h1 h2) h3) ?_
  intro w hw
  exact ⟨hw.1.1, hw.1.2, hw.2⟩

/-- **The derivative of the flat chart transition on `goodSet`.**  At a point `z` of the good set the
transition `y ↦ coord i (pt j y)` is differentiable within `goodSet` with derivative
`transDeriv D j i z`, i.e. the change of chart `tangentCoordChange I (x₀ j) (x₀ i) (pt j z)`
conjugated by the `finBasis`-identification of `E` with `Fin (finrank ℝ E) → ℝ`.

This is `Work.Diff.STE.B3.hasFDerivWithinAt_coord_pt` re-proved for the set `goodSet`, whose defining
conditions are the ones available here (the source membership of the two charts, plus the chart-`j`
target interiority that makes `pt j` genuine); the standing version of that lemma asks instead for
`χ i ≠ 0` and `ζ j (pt i ·) ≠ 0`, which `goodSet` does not provide. -/
lemma hasFDerivWithinAt_tMapFun (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (i j : ι₀)
    {z : Fin (Module.finrank ℝ E) → ℝ}
    (hz : z ∈ Work.Diff.STE.D.goodSet (I := I) (M := M) D i j) :
    HasFDerivWithinAt (Work.Diff.STE.D.tMapFun (I := I) (M := M) D i j)
      (Work.Diff.STE.B3.transDeriv (I := I) (M := M) D j i z)
      (Work.Diff.STE.D.goodSet (I := I) (M := M) D i j) z := by
  classical
  -- `pt j z` lies in the sources of the two charts, and the chart `j` is genuine at `z`
  have hsrc_j : D.pt j z ∈ (extChartAt I (D.x₀ j)).source :=
    (extChartAt I (D.x₀ j)).map_target (interior_subset hz.1)
  have hsrc_i : D.pt j z ∈ (extChartAt I (D.x₀ i)).source := hz.2.1
  have hroot : (extChartAt I (D.x₀ j)) (D.pt j z)
      = Work.Diff.STE.flatToE (I := I) (D.x₀ j) z :=
    (extChartAt I (D.x₀ j)).right_inv (interior_subset hz.1)
  -- the change of chart, as a map on the model space, within `range I`
  have h1 : HasFDerivWithinAt
      (fun u : E => (extChartAt I (D.x₀ i)) ((extChartAt I (D.x₀ j)).symm u))
      (tangentCoordChange (I := I) (D.x₀ j) (D.x₀ i) (D.pt j z)) (Set.range I)
      (Work.Diff.STE.flatToE (I := I) (D.x₀ j) z) := by
    have h := hasFDerivWithinAt_tangentCoordChange (I := I) (x := D.x₀ j) (y := D.x₀ i)
      (z := D.pt j z) ⟨hsrc_j, hsrc_i⟩
    simpa only [Function.comp_def, hroot] using h
  -- postcompose with the coordinate identification `E ≃ ℝⁿ`
  have h2 : HasFDerivWithinAt
      (fun u : E => (Module.finBasis ℝ E).equivFun
        ((extChartAt I (D.x₀ i)) ((extChartAt I (D.x₀ j)).symm u)))
      (((Module.finBasis ℝ E).equivFun.toContinuousLinearMap) ∘L
        (tangentCoordChange (I := I) (D.x₀ j) (D.x₀ i) (D.pt j z)))
      (Set.range I) (Work.Diff.STE.flatToE (I := I) (D.x₀ j) z) :=
    (ContinuousLinearMap.hasFDerivAt
      (((Module.finBasis ℝ E).equivFun.toContinuousLinearMap) :
        E →L[ℝ] (Fin (Module.finrank ℝ E) → ℝ))).comp_hasFDerivWithinAt _ h1
  -- the affine parametrisation of the chart at `x₀ j` by the flat coordinates
  have hG : HasFDerivWithinAt (fun w : Fin (Module.finrank ℝ E) → ℝ =>
      Work.Diff.STE.flatToE (I := I) (D.x₀ j) w)
      ((Module.finBasis ℝ E).equivFun.symm.toContinuousLinearMap)
      (Work.Diff.STE.D.goodSet (I := I) (M := M) D i j) z := by
    have h1' : HasFDerivAt (fun w : Fin (Module.finrank ℝ E) → ℝ =>
        (Module.finBasis ℝ E).equivFun ((extChartAt I (D.x₀ j)) (D.x₀ j)) + w)
        (ContinuousLinearMap.id ℝ (Fin (Module.finrank ℝ E) → ℝ)) z :=
      (hasFDerivAt_id z).const_add _
    have h2' := (ContinuousLinearMap.hasFDerivAt
      (((Module.finBasis ℝ E).equivFun.symm.toContinuousLinearMap) :
        (Fin (Module.finrank ℝ E) → ℝ) →L[ℝ] E)).comp _ h1'
    have h3 : HasFDerivWithinAt (fun w : Fin (Module.finrank ℝ E) → ℝ =>
        ((Module.finBasis ℝ E).equivFun.symm.toContinuousLinearMap)
          ((Module.finBasis ℝ E).equivFun ((extChartAt I (D.x₀ j)) (D.x₀ j)) + w))
        ((Module.finBasis ℝ E).equivFun.symm.toContinuousLinearMap)
        (Work.Diff.STE.D.goodSet (I := I) (M := M) D i j) z := by
      simpa only [Function.comp_def, ContinuousLinearMap.comp_id] using h2'.hasFDerivWithinAt
    exact h3.congr (fun w _ => rfl) rfl
  -- the parametrisation lands in `range I` on `goodSet`
  have hmap : Set.MapsTo (fun w : Fin (Module.finrank ℝ E) → ℝ =>
      Work.Diff.STE.flatToE (I := I) (D.x₀ j) w)
      (Work.Diff.STE.D.goodSet (I := I) (M := M) D i j) (Set.range I) :=
    fun w hw => extChartAt_target_subset_range (I := I) (D.x₀ j) (interior_subset hw.1)
  have hmain := h2.comp z hG hmap
  -- pass from `equivFun (extChartAt _ _)` to `coord`, which differs by a constant
  have hcongr : (Work.Diff.STE.D.tMapFun (I := I) (M := M) D i j)
      = fun w => (Module.finBasis ℝ E).equivFun
          ((extChartAt I (D.x₀ i)) ((extChartAt I (D.x₀ j)).symm
            (Work.Diff.STE.flatToE (I := I) (D.x₀ j) w)))
          - (Module.finBasis ℝ E).equivFun ((extChartAt I (D.x₀ i)) (D.x₀ i)) := by
    funext w
    simp only [Work.Diff.STE.D.tMapFun, Work.Diff.STE.B3Data.pt, Work.Diff.STE.coord_apply]
  rw [hcongr]
  exact hmain.sub_const _

/-- **The transition is differentiable at every point of `goodSet`**, with derivative
`transDeriv D j i`. -/
lemma hasFDerivAt_tMapFun (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (i j : ι₀)
    {z : Fin (Module.finrank ℝ E) → ℝ}
    (hz : z ∈ Work.Diff.STE.D.goodSet (I := I) (M := M) D i j) :
    HasFDerivAt (Work.Diff.STE.D.tMapFun (I := I) (M := M) D i j)
      (Work.Diff.STE.B3.transDeriv (I := I) (M := M) D j i z) z :=
  (hasFDerivWithinAt_tMapFun (I := I) (M := M) D i j hz).hasFDerivAt
    (tMapFun_goodSet_mem_nhds (I := I) (M := M) D i j hz)

/-- **`fderiv` of the flat chart transition on `goodSet`.** -/
lemma fderiv_tMapFun (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (i j : ι₀)
    {z : Fin (Module.finrank ℝ E) → ℝ}
    (hz : z ∈ Work.Diff.STE.D.goodSet (I := I) (M := M) D i j) :
    fderiv ℝ (Work.Diff.STE.D.tMapFun (I := I) (M := M) D i j) z
      = Work.Diff.STE.B3.transDeriv (I := I) (M := M) D j i z :=
  (hasFDerivAt_tMapFun (I := I) (M := M) D i j hz).fderiv

/-- **The transition is injective on `goodSet`.**  The chart `j` is genuine at both points (their
`flatToE`-values lie in its target), the chart `i` is injective on its own source, and the affine
parametrisation `flatToE (x₀ j)` is injective. -/
lemma injOn_tMapFun_goodSet (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (i j : ι₀) :
    Set.InjOn (Work.Diff.STE.D.tMapFun (I := I) (M := M) D i j)
      (Work.Diff.STE.D.goodSet (I := I) (M := M) D i j) := by
  intro z hz z' hz' h
  -- the chart-`i` coordinates of `pt j z` and `pt j z'` agree
  have hcoord : (extChartAt I (D.x₀ i)) (D.pt j z) = (extChartAt I (D.x₀ i)) (D.pt j z') := by
    have h2 : (Module.finBasis ℝ E).equivFun ((extChartAt I (D.x₀ i)) (D.pt j z))
        = (Module.finBasis ℝ E).equivFun ((extChartAt I (D.x₀ i)) (D.pt j z')) := by
      have h3 : Work.Diff.STE.coord (I := I) (D.x₀ i) (D.pt j z)
          = Work.Diff.STE.coord (I := I) (D.x₀ i) (D.pt j z') := h
      simp only [Work.Diff.STE.coord, sub_left_inj] at h3
      exact h3
    exact (Module.finBasis ℝ E).equivFun.injective h2
  -- both points lie in the source of the chart `i`, which is injective there
  have hpt : D.pt j z = D.pt j z' := by
    have h3 := congrArg (extChartAt I (D.x₀ i)).symm hcoord
    rwa [(extChartAt I (D.x₀ i)).left_inv hz.2.1,
      (extChartAt I (D.x₀ i)).left_inv hz'.2.1] at h3
  -- the chart `j` is genuine at both points, so the flat coordinates agree
  have hF : Work.Diff.STE.flatToE (I := I) (D.x₀ j) z
      = Work.Diff.STE.flatToE (I := I) (D.x₀ j) z' := by
    have h1 : (extChartAt I (D.x₀ j)) (D.pt j z) = (extChartAt I (D.x₀ j)) (D.pt j z') := by
      rw [hpt]
    rw [← (extChartAt I (D.x₀ j)).right_inv (interior_subset hz.1),
      ← (extChartAt I (D.x₀ j)).right_inv (interior_subset hz'.1)]
    exact h1
  -- `flatToE (x₀ j)` is affine with invertible linear part
  have hF' : (Module.finBasis ℝ E).equivFun ((extChartAt I (D.x₀ j)) (D.x₀ j)) + z
      = (Module.finBasis ℝ E).equivFun ((extChartAt I (D.x₀ j)) (D.x₀ j)) + z' :=
    (Module.finBasis ℝ E).equivFun.symm.injective hF
  exact add_left_cancel hF'

/-- **The Jacobian determinant of the transition does not vanish on `goodSet`.**  The two chart
transitions `tangentCoordChange I (x₀ j) (x₀ i)` and `tangentCoordChange I (x₀ i) (x₀ j)` at
`pt j z` are mutually inverse (`tangentCoordChange_comp` at the triple `(x₀ j, x₀ i, x₀ j)`, then
`tangentCoordChange_self`), so the determinant of either of them is non-zero. -/
lemma tMapFun_det_ne_zero (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (i j : ι₀)
    {z : Fin (Module.finrank ℝ E) → ℝ}
    (hz : z ∈ Work.Diff.STE.D.goodSet (I := I) (M := M) D i j) :
    (fderiv ℝ (Work.Diff.STE.D.tMapFun (I := I) (M := M) D i j) z).det ≠ 0 := by
  rw [fderiv_tMapFun (I := I) (M := M) D i j hz,
    Work.Diff.STE.B3.det_transDeriv]
  have hsrc_j : D.pt j z ∈ (extChartAt I (D.x₀ j)).source :=
    (extChartAt I (D.x₀ j)).map_target (interior_subset hz.1)
  have hsrc_i : D.pt j z ∈ (extChartAt I (D.x₀ i)).source := hz.2.1
  -- the two chart transitions at `pt j z` are mutually inverse
  have hcomp : (tangentCoordChange (I := I) (D.x₀ i) (D.x₀ j) (D.pt j z)).toLinearMap.comp
      (tangentCoordChange (I := I) (D.x₀ j) (D.x₀ i) (D.pt j z)).toLinearMap = 1 := by
    ext v
    change (tangentCoordChange (I := I) (D.x₀ i) (D.x₀ j) (D.pt j z))
        ((tangentCoordChange (I := I) (D.x₀ j) (D.x₀ i) (D.pt j z)) v) = v
    rw [tangentCoordChange_comp (w := D.x₀ j) (x := D.x₀ i) (y := D.x₀ j) (z := D.pt j z)
        (v := v) ⟨⟨hsrc_j, hsrc_i⟩, hsrc_j⟩,
      tangentCoordChange_self (x := D.x₀ j) (z := D.pt j z) (v := v) hsrc_j]
  have hdet : (tangentCoordChange (I := I) (D.x₀ i) (D.x₀ j) (D.pt j z)).det *
      (tangentCoordChange (I := I) (D.x₀ j) (D.x₀ i) (D.pt j z)).det = 1 := by
    have h := LinearMap.det_comp
      (f := (tangentCoordChange (I := I) (D.x₀ i) (D.x₀ j) (D.pt j z)).toLinearMap)
      (g := (tangentCoordChange (I := I) (D.x₀ j) (D.x₀ i) (D.pt j z)).toLinearMap)
    rw [hcomp, map_one] at h
    exact h.symm
  intro hzero
  rw [hzero, mul_zero] at hdet
  exact one_ne_zero hdet.symm

theorem tMapFun_injOn_det
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (i j : ι₀) :
    Set.InjOn (Work.Diff.STE.D.tMapFun (I := I) (M := M) D i j)
        (Work.Diff.STE.D.goodSet (I := I) (M := M) D i j) ∧
      ∀ z, z ∈ Work.Diff.STE.D.goodSet (I := I) (M := M) D i j →
        (fderiv ℝ (Work.Diff.STE.D.tMapFun (I := I) (M := M) D i j) z).det ≠ 0 :=
  ⟨injOn_tMapFun_goodSet (I := I) (M := M) D i j,
    fun _ hz => tMapFun_det_ne_zero (I := I) (M := M) D i j hz⟩

end Work.Diff.STE.B3
