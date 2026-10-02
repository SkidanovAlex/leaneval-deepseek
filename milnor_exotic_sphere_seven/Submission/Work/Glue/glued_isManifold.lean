import Mathlib
import Submission.Work.Glue.Basic

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The glued space is a `C^n` manifold

`Submission.Work.Glue.Basic` constructs, given two `C^n` manifolds `X`, `Y` over a common model
`H` and gluing data `D : Data I n X Y`, the glued space `D.Glued` together with a charted space
structure on it.  This file proves that this charted space is a `C^n` manifold, i.e. that the
transition functions between the charts `D.chartAt z` all lie in `contDiffGroupoid n I`.

The glued space is covered by the two open images of `X` and `Y`; the chart `D.chartOfX x` is the
chart of `X` at `x` transported along the open embedding `D.homX`, and similarly for `Y`.  Hence
every transition is of the form `c.symm ≫ₕ E ≫ₕ c'` where `c`, `c'` are charts of `X` resp. `Y`
and `E` is one of the four "middle" partial homeomorphisms
`D.homX ≫ₕ D.homX.symm ≈ id`, `D.homY ≫ₕ D.homY.symm ≈ id`, `D.homX ≫ₕ D.homY.symm ≈ D.φ` and
`D.homY ≫ₕ D.homX.symm ≈ D.φ.symm`.  Each of these gives an element of the groupoid: the first two
by smoothness of `X` resp. `Y`, the last two by the hypothesis that `φ` is a diffeomorphism.
-/

open scoped Manifold ContDiff Topology
open Submission.Glue
open OpenPartialHomeomorph

set_option linter.unusedSectionVars false

namespace Work.Glue

/-- Associativity of composition of open partial homeomorphisms, in a normal form suited to
splitting a composition of four maps in the middle. -/
theorem trans_trans {A B C D E : Type*} [TopologicalSpace A] [TopologicalSpace B]
    [TopologicalSpace C] [TopologicalSpace D] [TopologicalSpace E]
    (a : OpenPartialHomeomorph A B) (b : OpenPartialHomeomorph B C)
    (d : OpenPartialHomeomorph C D) (g : OpenPartialHomeomorph D E) :
    (a.trans b).trans (d.trans g) = a.trans ((b.trans d).trans g) := by
  rw [OpenPartialHomeomorph.trans_assoc a b (d.trans g),
    OpenPartialHomeomorph.trans_assoc b d g]

section Helpers

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
variable {X : Type*} [TopologicalSpace X] [ChartedSpace H X] [IsManifold I n X]
variable {Y : Type*} [TopologicalSpace Y] [ChartedSpace H Y] [IsManifold I n Y]
variable [Nonempty X] [Nonempty Y] (D : Data I n X Y)

/-- The underlying function of `D.homX` is `D.ιX`. -/
theorem homX_coe : (⇑D.homX : X → D.Glued) = D.ιX := funext D.homX_apply

/-- The underlying function of `D.homY` is `D.ιY`. -/
theorem homY_coe : (⇑D.homY : Y → D.Glued) = D.ιY := funext D.homY_apply

/-- The preimage of the image of `Y` under the image of `X` is `D.U`. -/
theorem preimage_range_ιY : D.ιX ⁻¹' Set.range D.ιY = D.U := by
  ext x
  simp only [Set.mem_preimage, Set.mem_range]
  constructor
  · rintro ⟨y, hy⟩
    exact (D.ιY_eq_ιX_iff.mp hy).choose
  · intro hx
    exact ⟨D.φ x, D.ιY_eq_ιX_iff.mpr ⟨hx, rfl⟩⟩

/-- The preimage of the image of `X` under the image of `Y` is `D.V`. -/
theorem preimage_range_ιX : D.ιY ⁻¹' Set.range D.ιX = D.V := by
  ext y
  simp only [Set.mem_preimage, Set.mem_range]
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨hxU, hφ⟩ := D.ιX_eq_ιY_iff.mp hx
    rw [← hφ, ← D.target_φ]
    exact D.φ.map_source (by rw [D.source_φ]; exact hxU)
  · intro hy
    refine ⟨D.φ.symm y, ?_⟩
    rw [D.ιX_eq_ιY_iff]
    refine ⟨?_, ?_⟩
    · rw [← D.source_φ, ← D.φ.symm_target]
      exact D.φ.symm.map_source (by rw [D.φ.symm_source, D.target_φ]; exact hy)
    · rw [D.φ.right_inv (by rw [D.target_φ]; exact hy)]

/-- The two copies of `X` coincide on the overlap: `homX ≫ₕ homX.symm` is the identity. -/
theorem homX_trans_homX_symm : D.homX.trans D.homX.symm ≈ OpenPartialHomeomorph.refl X := by
  constructor
  · simp only [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
      OpenPartialHomeomorph.refl_source]
    rw [D.homX_source, D.homX_target, homX_coe D, Set.preimage_range, Set.univ_inter]
  · intro x hx
    simp only [OpenPartialHomeomorph.coe_trans, Function.comp_apply,
      OpenPartialHomeomorph.refl_apply]
    rw [homX_coe D, D.homX_symm_apply]
    rfl

/-- The two copies of `Y` coincide on the overlap: `homY ≫ₕ homY.symm` is the identity. -/
theorem homY_trans_homY_symm : D.homY.trans D.homY.symm ≈ OpenPartialHomeomorph.refl Y := by
  constructor
  · simp only [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
      OpenPartialHomeomorph.refl_source]
    rw [D.homY_source, D.homY_target, homY_coe D, Set.preimage_range, Set.univ_inter]
  · intro y hy
    simp only [OpenPartialHomeomorph.coe_trans, Function.comp_apply,
      OpenPartialHomeomorph.refl_apply]
    rw [homY_coe D, D.homY_symm_apply]
    rfl

/-- Going from a copy of `X` to a copy of `Y` is the gluing map `D.φ`. -/
theorem homX_trans_homY_symm : D.homX.trans D.homY.symm ≈ D.φ := by
  have hsrc : (D.homX.trans D.homY.symm).source = D.U := by
    simp only [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source]
    rw [D.homX_source, D.homY_target, homX_coe D, preimage_range_ιY D, Set.univ_inter]
  constructor
  · rw [hsrc, D.source_φ]
  · intro x hx
    rw [hsrc] at hx
    simp only [OpenPartialHomeomorph.coe_trans, Function.comp_apply]
    rw [homX_coe D, D.ιX_eq_ιY_iff.mpr ⟨hx, rfl⟩, D.homY_symm_apply]

/-- Going from a copy of `Y` to a copy of `X` is the inverse gluing map `D.φ.symm`. -/
theorem homY_trans_homX_symm : D.homY.trans D.homX.symm ≈ D.φ.symm := by
  have hsrc : (D.homY.trans D.homX.symm).source = D.V := by
    simp only [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source]
    rw [D.homY_source, D.homX_target, homY_coe D, preimage_range_ιX D, Set.univ_inter]
  constructor
  · rw [hsrc, D.φ.symm_source, D.target_φ]
  · intro y hy
    rw [hsrc] at hy
    simp only [OpenPartialHomeomorph.coe_trans, Function.comp_apply]
    rw [homY_coe D]
    have hxU : D.φ.symm y ∈ D.U := by
      rw [← D.source_φ, ← D.φ.symm_target]
      exact D.φ.symm.map_source (by rw [D.φ.symm_source, D.target_φ]; exact hy)
    have hφ : (D.φ (D.φ.symm y) : Y) = y :=
      D.φ.right_inv (by rw [D.target_φ]; exact hy)
    rw [D.ιY_eq_ιX_iff.mpr ⟨hxU, hφ⟩, D.homX_symm_apply]

/-- The inverse of a chart `D.chartOfX x` of the glued space is a chart of `X` followed by
`D.homX`. -/
theorem chartOfX_symm_eq (x : X) :
    (D.chartOfX x).symm = (chartAt H x).symm ≫ₕ D.homX := by
  simp only [Data.chartOfX, OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
    OpenPartialHomeomorph.symm_symm]

/-- The inverse of a chart `D.chartOfY y` of the glued space is a chart of `Y` followed by
`D.homY`. -/
theorem chartOfY_symm_eq (y : Y) :
    (D.chartOfY y).symm = (chartAt H y).symm ≫ₕ D.homY := by
  simp only [Data.chartOfY, OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
    OpenPartialHomeomorph.symm_symm]

/-- Transition between two charts coming from `X` is a transition of `X`. -/
theorem trans_chartOfX_chartOfX (x x' : X) :
    (D.chartOfX x).symm ≫ₕ D.chartOfX x' ≈ (chartAt H x).symm ≫ₕ chartAt H x' := by
  rw [chartOfX_symm_eq D x]
  simp only [Data.chartOfX]
  rw [trans_trans]
  refine EqOnSource.trans' (Setoid.refl _) ?_
  have h1 : ((D.homX ≫ₕ D.homX.symm) ≫ₕ (chartAt H x')) ≈
      ((OpenPartialHomeomorph.refl X) ≫ₕ (chartAt H x')) :=
    EqOnSource.trans' (homX_trans_homX_symm D) (Setoid.refl _)
  rwa [OpenPartialHomeomorph.refl_trans] at h1

/-- Transition from a chart coming from `X` to a chart coming from `Y` is `φ` composed with
charts of `X` and `Y`. -/
theorem trans_chartOfX_chartOfY (x : X) (y : Y) :
    (D.chartOfX x).symm ≫ₕ D.chartOfY y ≈ (chartAt H x).symm ≫ₕ D.φ ≫ₕ chartAt H y := by
  rw [chartOfX_symm_eq D x]
  simp only [Data.chartOfY]
  rw [trans_trans]
  refine EqOnSource.trans' (Setoid.refl _) ?_
  exact EqOnSource.trans' (homX_trans_homY_symm D) (Setoid.refl _)

/-- Transition from a chart coming from `Y` to a chart coming from `X` is `φ.symm` composed with
charts of `Y` and `X`. -/
theorem trans_chartOfY_chartOfX (y : Y) (x : X) :
    (D.chartOfY y).symm ≫ₕ D.chartOfX x ≈ (chartAt H y).symm ≫ₕ D.φ.symm ≫ₕ chartAt H x := by
  rw [chartOfY_symm_eq D y]
  simp only [Data.chartOfX]
  rw [trans_trans]
  refine EqOnSource.trans' (Setoid.refl _) ?_
  exact EqOnSource.trans' (homY_trans_homX_symm D) (Setoid.refl _)

/-- Transition between two charts coming from `Y` is a transition of `Y`. -/
theorem trans_chartOfY_chartOfY (y y' : Y) :
    (D.chartOfY y).symm ≫ₕ D.chartOfY y' ≈ (chartAt H y).symm ≫ₕ chartAt H y' := by
  rw [chartOfY_symm_eq D y]
  simp only [Data.chartOfY]
  rw [trans_trans]
  refine EqOnSource.trans' (Setoid.refl _) ?_
  have h1 : ((D.homY ≫ₕ D.homY.symm) ≫ₕ (chartAt H y')) ≈
      ((OpenPartialHomeomorph.refl Y) ≫ₕ (chartAt H y')) :=
    EqOnSource.trans' (homY_trans_homY_symm D) (Setoid.refl _)
  rwa [OpenPartialHomeomorph.refl_trans] at h1

end Helpers

open scoped Manifold ContDiff Topology in
open Submission.Glue in
theorem glued_isManifold
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {X : Type*} [TopologicalSpace X] [ChartedSpace H X] [IsManifold I n X]
    {Y : Type*} [TopologicalSpace Y] [ChartedSpace H Y] [IsManifold I n Y]
    [Nonempty X] [Nonempty Y] (D : Data I n X Y) : IsManifold I n D.Glued := by
  refine IsManifold.mk' I n D.Glued (gr := ⟨fun {e e'} he he' => ?_⟩)
  obtain ⟨z, rfl⟩ := he
  obtain ⟨z', rfl⟩ := he'
  rcases hz : Quotient.out z with x | y
  · rw [D.chartAt_of_out_inl hz]
    rcases hz' : Quotient.out z' with x' | y'
    · rw [D.chartAt_of_out_inl hz']
      exact (contDiffGroupoid n I).mem_of_eqOnSource
        ((contDiffGroupoid n I).compatible (chart_mem_atlas H x) (chart_mem_atlas H x'))
        (trans_chartOfX_chartOfX D x x')
    · rw [D.chartAt_of_out_inr hz']
      exact (contDiffGroupoid n I).mem_of_eqOnSource
        (D.mem_groupoid (chartAt H x) (chart_mem_atlas H x) (chartAt H y') (chart_mem_atlas H y'))
        (trans_chartOfX_chartOfY D x y')
  · rw [D.chartAt_of_out_inr hz]
    rcases hz' : Quotient.out z' with x' | y'
    · rw [D.chartAt_of_out_inl hz']
      have hmem := D.mem_groupoid (chartAt H x') (chart_mem_atlas H x')
        (chartAt H y) (chart_mem_atlas H y)
      have heq : ((chartAt H x').symm ≫ₕ D.φ ≫ₕ (chartAt H y)).symm
          = (chartAt H y).symm ≫ₕ D.φ.symm ≫ₕ (chartAt H x') := by
        simp only [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
          OpenPartialHomeomorph.symm_symm, OpenPartialHomeomorph.trans_assoc]
      have hmem' : (chartAt H y).symm ≫ₕ D.φ.symm ≫ₕ (chartAt H x') ∈
          contDiffGroupoid n I := by
        rw [← heq]
        exact (contDiffGroupoid n I).symm hmem
      exact (contDiffGroupoid n I).mem_of_eqOnSource hmem' (trans_chartOfY_chartOfX D y x')
    · rw [D.chartAt_of_out_inr hz']
      exact (contDiffGroupoid n I).mem_of_eqOnSource
        ((contDiffGroupoid n I).compatible (chart_mem_atlas H y) (chart_mem_atlas H y'))
        (trans_chartOfY_chartOfY D y y')

end Work.Glue
