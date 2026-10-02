import Mathlib
import Submission.Work.Glue.Basic
import Submission.Work.Glue.glued_isManifold
import Submission.Work.Morse.Basic

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Nondegenerate Hessians descend along `ιY`, for `C^n` manifolds

This is the `C^n` version of `Submission.Work.Glue.hasNondegHessian_iotaY` (which is stated for
`n = ⊤`).

`Submission.Work.Glue.Basic` glues two `C^n` manifolds `X`, `Y` over a common model `H` along a
diffeomorphism `φ : U ≅ V`, producing the glued space `D.Glued` with its charted space structure,
and `Submission.Work.Glue.glued_isManifold` shows that it is a `C^n` manifold.

The embedding `D.ιY : Y → D.Glued` is an open embedding; the point of this file is that it is also
a *local diffeomorphism*, so that any notion defined by looking at the local behaviour of a
function is transported: if `g : Y → ℝ` has a nondegenerate Hessian at `y`, then any `F` on the
glued space that agrees with `g` on `D.ιY` (that is, `F (D.ιY y) = g y` for all `y`) has a
nondegenerate Hessian at `D.ιY y`.

The proof is by explicit transport of the chart: given a chart `e` of `Y` at `y` witnessing
`HasNondegHessian g y`, the chart

`D.homY.symm ≫ₕ e`

of the glued space is a chart at `D.ιY y`, it lies in the maximal atlas, and the coordinate
expression `F ∘ (D.homY.symm ≫ₕ e).symm ∘ I.symm` is *literally* the coordinate expression
`g ∘ e.symm ∘ I.symm`, because `(D.homY.symm ≫ₕ e).symm = e.symm ≫ₕ D.homY` and
`D.homY = D.ιY` on the nose.  Hence both derivatives — and the nondegeneracy condition — agree.

The only non-trivial ingredient is that `D.homY.symm ≫ₕ e` is in the maximal atlas of the glued
space whenever `e` is in the maximal atlas of `Y`; this is reduced to the auxiliary statement
`homY_comp_mem_maximalAtlas_gen` that composing `D.ιY` (as `D.homY`) with an atlas member of the
glued space gives an element of the maximal atlas of `Y`.  Unlike the `⊤` case these lemmas
mention the groupoid `contDiffGroupoid n I` for a general `n`, so they are reproved here.
-/

open scoped Manifold ContDiff Topology
open Submission.Glue
open OpenPartialHomeomorph (EqOnSource)

namespace Work.Glue

/-- Pulling back an atlas member of the glued space along the open embedding `D.homY : Y → D.Glued`
gives an element of the maximal atlas of `Y`. -/
theorem homY_comp_mem_maximalAtlas_gen
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {X : Type*} [TopologicalSpace X] [ChartedSpace H X] [IsManifold I n X]
    {Y : Type*} [TopologicalSpace Y] [ChartedSpace H Y] [IsManifold I n Y]
    [Nonempty X] [Nonempty Y] (D : Submission.Glue.Data I n X Y)
    {c : OpenPartialHomeomorph D.Glued H} (hc : c ∈ atlas H D.Glued) :
    D.homY ≫ₕ c ∈ IsManifold.maximalAtlas I n Y := by
  obtain ⟨z, rfl⟩ := hc
  rcases hout : Quotient.out z with x | y
  · -- the chart of the glued space comes from `X`
    rw [D.chartAt_of_out_inl hout]
    have h1 : (D.homY ≫ₕ D.chartOfX x) ≈ (D.φ.symm ≫ₕ chartAt H x) := by
      rw [Submission.Glue.Data.chartOfX, ← OpenPartialHomeomorph.trans_assoc]
      exact EqOnSource.trans' (homY_trans_homX_symm D) (Setoid.refl _)
    refine StructureGroupoid.mem_maximalAtlas_of_eqOnSource h1 ?_
    rw [mem_maximalAtlas_iff]
    intro e'' he''
    constructor
    · -- `φ.symm` composed with a chart of `X` is a chart of `Y`
      have hsym : (D.φ.symm ≫ₕ chartAt H x).symm = (chartAt H x).symm ≫ₕ D.φ := by
        rw [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
          OpenPartialHomeomorph.symm_symm]
      rw [hsym]
      rw [OpenPartialHomeomorph.trans_assoc]
      exact D.mem_groupoid (chartAt H x) (chart_mem_atlas H x) e'' he''
    · have hmem := D.mem_groupoid (chartAt H x) (chart_mem_atlas H x) e'' he''
      have h2 : ((chartAt H x).symm ≫ₕ (D.φ ≫ₕ e'')).symm
          = e''.symm ≫ₕ (D.φ.symm ≫ₕ chartAt H x) := by
        rw [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
          OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
          OpenPartialHomeomorph.symm_symm, OpenPartialHomeomorph.trans_assoc]
      rw [← h2]
      exact (contDiffGroupoid n I).symm hmem
  · -- the chart of the glued space comes from `Y`
    rw [D.chartAt_of_out_inr hout]
    have h1 : (D.homY ≫ₕ D.chartOfY y) ≈ (chartAt H y) := by
      rw [Submission.Glue.Data.chartOfY, ← OpenPartialHomeomorph.trans_assoc]
      have h := EqOnSource.trans' (homY_trans_homY_symm D) (Setoid.refl (chartAt H y))
      rwa [OpenPartialHomeomorph.refl_trans] at h
    exact StructureGroupoid.mem_maximalAtlas_of_eqOnSource h1
      (IsManifold.chart_mem_maximalAtlas (I := I) (n := n) y)

/-- If `e` is a chart of `Y` in the maximal atlas, then `D.homY.symm ≫ₕ e` is a chart of the glued
space in the maximal atlas: this is the transport of charts along the open embedding `D.ιY`. -/
theorem homY_symm_comp_mem_maximalAtlas_gen
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {X : Type*} [TopologicalSpace X] [ChartedSpace H X] [IsManifold I n X]
    {Y : Type*} [TopologicalSpace Y] [ChartedSpace H Y] [IsManifold I n Y]
    [Nonempty X] [Nonempty Y] (D : Submission.Glue.Data I n X Y) [IsManifold I n D.Glued]
    {e : OpenPartialHomeomorph Y H} (he : e ∈ IsManifold.maximalAtlas I n Y) :
    D.homY.symm ≫ₕ e ∈ IsManifold.maximalAtlas I n D.Glued := by
  change D.homY.symm ≫ₕ e ∈ (contDiffGroupoid n I).maximalAtlas D.Glued
  rw [mem_maximalAtlas_iff]
  intro c hc
  have hc' := homY_comp_mem_maximalAtlas_gen D hc
  constructor
  · rw [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm, OpenPartialHomeomorph.symm_symm]
    rw [OpenPartialHomeomorph.trans_assoc]
    exact (contDiffGroupoid n I).compatible_of_mem_maximalAtlas he hc'
  · have key : (c.symm ≫ₕ (D.homY.symm ≫ₕ e)) = ((e.symm ≫ₕ (D.homY ≫ₕ c))).symm := by
      rw [← OpenPartialHomeomorph.trans_assoc (c.symm) (D.homY.symm) e]
      rw [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
        OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
        OpenPartialHomeomorph.symm_symm]
    rw [key]
    exact (contDiffGroupoid n I).symm
      ((contDiffGroupoid n I).compatible_of_mem_maximalAtlas he hc')

theorem hasNondegHessian_iotaY_gen
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : WithTop ENat}
    {X : Type*} [TopologicalSpace X] [ChartedSpace H X] [IsManifold I n X]
    {Y : Type*} [TopologicalSpace Y] [ChartedSpace H Y] [IsManifold I n Y]
    [Nonempty X] [Nonempty Y] (D : Submission.Glue.Data I n X Y) [IsManifold I n D.Glued]
    {F : D.Glued → ℝ} {g : Y → ℝ} (h : ∀ y : Y, F (D.ιY y) = g y) {y : Y}
    (hy : HasNondegHessian (I := I) (n := n) g y) :
    HasNondegHessian (I := I) (n := n) F (D.ιY y) := by
  obtain ⟨e, he, hysrc, hd1, hd2⟩ := hy
  -- the chart of the glued space obtained by transporting `e` along `D.ιY`
  refine ⟨D.homY.symm ≫ₕ e, ?_, ?_, ?_, ?_⟩
  · exact homY_symm_comp_mem_maximalAtlas_gen D he
  · -- `D.ιY y` lies in the source of the transported chart
    rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source, D.homY_target]
    refine ⟨⟨y, rfl⟩, ?_⟩
    show D.homY.symm (D.ιY y) ∈ e.source
    rw [D.homY_symm_apply]
    exact hysrc
  · -- the coordinate expression of `F` is literally that of `g`
    have hpt : (D.homY.symm ≫ₕ e) (D.ιY y) = e y := by
      rw [OpenPartialHomeomorph.coe_trans, Function.comp_apply, D.homY_symm_apply]
    have hfun : (fun x : E => F ((D.homY.symm ≫ₕ e).symm (I.symm x)))
        = fun x : E => g (e.symm (I.symm x)) := by
      funext x
      rw [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm, OpenPartialHomeomorph.symm_symm,
        OpenPartialHomeomorph.coe_trans, Function.comp_apply, D.homY_apply]
      exact h (e.symm (I.symm x))
    rw [hfun, hpt]
    exact hd1
  · have hpt : (D.homY.symm ≫ₕ e) (D.ιY y) = e y := by
      rw [OpenPartialHomeomorph.coe_trans, Function.comp_apply, D.homY_symm_apply]
    have hfun : (fun x : E => F ((D.homY.symm ≫ₕ e).symm (I.symm x)))
        = fun x : E => g (e.symm (I.symm x)) := by
      funext x
      rw [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm, OpenPartialHomeomorph.symm_symm,
        OpenPartialHomeomorph.coe_trans, Function.comp_apply, D.homY_apply]
      exact h (e.symm (I.symm x))
    intro v hv
    rw [hfun, hpt] at hv
    exact hd2 v hv

end Work.Glue
