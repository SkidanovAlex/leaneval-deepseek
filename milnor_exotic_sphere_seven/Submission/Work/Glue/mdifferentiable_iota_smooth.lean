import Mathlib
import Submission.Work.Glue.Basic
import Submission.Work.Glue.glued_isManifold

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Smoothness of the two embeddings `ιX`, `ιY` of a glued space (the `∞` case)

`Submission.Work.Glue.Basic` constructs, from gluing data `D : Data I n X Y`, the glued space
`D.Glued`, and `Submission.Work.Glue.glued_isManifold` shows that it is a `C^n` manifold.

Here we prove the `n = ∞` instance of the statement that the two inclusions

* `D.ιX : X → D.Glued`,
* `D.ιY : Y → D.Glued`

are smooth (i.e. `MDifferentiableAt` at every point), and that the manifold derivative of `D.ιY`
is surjective at every point.  (`∞` is the level `((⊤ : ENat) : WithTop ENat)` used for the
smooth structures in this project, cf. `IsManifold (𝓡 7) ∞ M` in `Challenge.lean`.)

The argument is the one of `Submission.Work.Glue.mdifferentiable_iota`, carried out for a general
smoothness level `n ≠ 0`: the charts of the glued space are built precisely so that `D.homX` and
`D.homY` — the open partial homeomorphisms whose underlying maps are `D.ιX` and `D.ιY` — are local
structomorphisms for the groupoid `contDiffGroupoid n I`.  We prove that as
`liftProp_homX_gen`/`liftProp_homY_gen`, deduce `OpenPartialHomeomorph.MDifferentiable`
(`mdifferentiable_homX_gen`/`mdifferentiable_homY_gen`), and specialise to `n = ∞`.
-/

open scoped Manifold ContDiff Topology
open Submission.Glue
open OpenPartialHomeomorph
open Set

set_option linter.unusedSectionVars false

namespace Work.Glue

/-- `D.homX : X → D.Glued` (whose underlying function is `D.ιX`) is a local structomorphism for
the `C^n` groupoid, i.e. it is `C^n` together with its inverse.  This is the technical heart of the
smoothness of `D.ιX` and of `D.homX.symm`. -/
theorem liftProp_homX_gen
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {X : Type*} [TopologicalSpace X] [ChartedSpace H X] [IsManifold I n X]
    {Y : Type*} [TopologicalSpace Y] [ChartedSpace H Y] [IsManifold I n Y]
    [Nonempty X] [Nonempty Y] (D : Data I n X Y) :
    ChartedSpace.LiftPropOn (contDiffGroupoid n I).IsLocalStructomorphWithinAt
      (⇑D.homX) D.homX.source := by
  intro x hx
  rw [ChartedSpace.liftPropWithinAt_iff']
  refine ⟨?_, ?_⟩
  · rw [Work.Glue.homX_coe D]
    exact D.continuous_ιX.continuousAt.continuousWithinAt
  · intro _
    refine ⟨(chartAt H x).symm ≫ₕ D.homX ≫ₕ chartAt H (D.homX x), ?_, ?_, ?_⟩
    · have hc : chartAt H (D.homX x) = D.chartAt (D.homX x) := rfl
      rw [hc]
      rcases hout : Quotient.out (D.homX x) with x₀ | y
      · rw [D.chartAt_of_out_inl hout]
        have heq := Work.Glue.trans_chartOfX_chartOfX (I := I) (n := n) D x x₀
        rw [Work.Glue.chartOfX_symm_eq D x, OpenPartialHomeomorph.trans_assoc] at heq
        exact (contDiffGroupoid n I).mem_of_eqOnSource
          ((contDiffGroupoid n I).compatible (chart_mem_atlas H x) (chart_mem_atlas H x₀)) heq
      · rw [D.chartAt_of_out_inr hout]
        have heq := Work.Glue.trans_chartOfX_chartOfY (I := I) (n := n) D x y
        rw [Work.Glue.chartOfX_symm_eq D x, OpenPartialHomeomorph.trans_assoc] at heq
        exact (contDiffGroupoid n I).mem_of_eqOnSource
          (D.mem_groupoid (chartAt H x) (chart_mem_atlas H x) (chartAt H y) (chart_mem_atlas H y))
          heq
    · intro z _
      rfl
    · simp only [mfld_simps]
      exact hx

/-- `D.homY : Y → D.Glued` (whose underlying function is `D.ιY`) is a local structomorphism for
the `C^n` groupoid. -/
theorem liftProp_homY_gen
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {X : Type*} [TopologicalSpace X] [ChartedSpace H X] [IsManifold I n X]
    {Y : Type*} [TopologicalSpace Y] [ChartedSpace H Y] [IsManifold I n Y]
    [Nonempty X] [Nonempty Y] (D : Data I n X Y) :
    ChartedSpace.LiftPropOn (contDiffGroupoid n I).IsLocalStructomorphWithinAt
      (⇑D.homY) D.homY.source := by
  intro y hy
  rw [ChartedSpace.liftPropWithinAt_iff']
  refine ⟨?_, ?_⟩
  · rw [Work.Glue.homY_coe D]
    exact D.continuous_ιY.continuousAt.continuousWithinAt
  · intro _
    refine ⟨(chartAt H y).symm ≫ₕ D.homY ≫ₕ chartAt H (D.homY y), ?_, ?_, ?_⟩
    · have hc : chartAt H (D.homY y) = D.chartAt (D.homY y) := rfl
      rw [hc]
      rcases hout : Quotient.out (D.homY y) with x₀ | y₀
      · rw [D.chartAt_of_out_inl hout]
        have heq := Work.Glue.trans_chartOfY_chartOfX (I := I) (n := n) D y x₀
        rw [Work.Glue.chartOfY_symm_eq D y, OpenPartialHomeomorph.trans_assoc] at heq
        have hmem := D.mem_groupoid (chartAt H x₀) (chart_mem_atlas H x₀) (chartAt H y)
          (chart_mem_atlas H y)
        have heq2 : ((chartAt H x₀).symm ≫ₕ D.φ ≫ₕ (chartAt H y)).symm
            = (chartAt H y).symm ≫ₕ D.φ.symm ≫ₕ (chartAt H x₀) := by
          simp only [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
            OpenPartialHomeomorph.symm_symm, OpenPartialHomeomorph.trans_assoc]
        have hmem' : (chartAt H y).symm ≫ₕ D.φ.symm ≫ₕ (chartAt H x₀) ∈
            contDiffGroupoid n I := by
          rw [← heq2]; exact (contDiffGroupoid n I).symm hmem
        exact (contDiffGroupoid n I).mem_of_eqOnSource hmem' heq
      · rw [D.chartAt_of_out_inr hout]
        have heq := Work.Glue.trans_chartOfY_chartOfY (I := I) (n := n) D y y₀
        rw [Work.Glue.chartOfY_symm_eq D y, OpenPartialHomeomorph.trans_assoc] at heq
        exact (contDiffGroupoid n I).mem_of_eqOnSource
          ((contDiffGroupoid n I).compatible (chart_mem_atlas H y) (chart_mem_atlas H y₀)) heq
    · intro z _
      rfl
    · simp only [mfld_simps]
      exact hy

/-- `D.homX` is an `MDifferentiable` open partial homeomorphism, for any non-zero smoothness
level `n`. -/
theorem mdifferentiable_homX_gen
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {X : Type*} [TopologicalSpace X] [ChartedSpace H X] [IsManifold I n X]
    {Y : Type*} [TopologicalSpace Y] [ChartedSpace H Y] [IsManifold I n Y]
    [Nonempty X] [Nonempty Y] (D : Data I n X Y) (hn : n ≠ 0) :
    OpenPartialHomeomorph.MDifferentiable I I D.homX := by
  haveI : IsManifold I n D.Glued := glued_isManifold D
  have h := (isLocalStructomorphOn_contDiffGroupoid_iff (I := I) (n := n) (f := D.homX)).mp
    (liftProp_homX_gen D)
  exact ⟨h.1.mdifferentiableOn hn, h.2.mdifferentiableOn hn⟩

/-- `D.homY` is an `MDifferentiable` open partial homeomorphism, for any non-zero smoothness
level `n`. -/
theorem mdifferentiable_homY_gen
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {X : Type*} [TopologicalSpace X] [ChartedSpace H X] [IsManifold I n X]
    {Y : Type*} [TopologicalSpace Y] [ChartedSpace H Y] [IsManifold I n Y]
    [Nonempty X] [Nonempty Y] (D : Data I n X Y) (hn : n ≠ 0) :
    OpenPartialHomeomorph.MDifferentiable I I D.homY := by
  haveI : IsManifold I n D.Glued := glued_isManifold D
  have h := (isLocalStructomorphOn_contDiffGroupoid_iff (I := I) (n := n) (f := D.homY)).mp
    (liftProp_homY_gen D)
  exact ⟨h.1.mdifferentiableOn hn, h.2.mdifferentiableOn hn⟩

theorem mdifferentiable_iota_smooth
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H}
    {X : Type*} [TopologicalSpace X] [ChartedSpace H X]
      [IsManifold I ((⊤ : ENat) : WithTop ENat) X]
    {Y : Type*} [TopologicalSpace Y] [ChartedSpace H Y]
      [IsManifold I ((⊤ : ENat) : WithTop ENat) Y]
    [Nonempty X] [Nonempty Y]
    (D : Submission.Glue.Data I ((⊤ : ENat) : WithTop ENat) X Y) :
    (∀ x : X, MDifferentiableAt I I D.ιX x) ∧
    (∀ y : Y, MDifferentiableAt I I D.ιY y) ∧
    (∀ y : Y, Function.Surjective (mfderiv I I D.ιY y)) := by
  have hn : ((⊤ : ENat) : WithTop ENat) ≠ (0 : ℕ∞ω) := by simp
  haveI : IsManifold I ((⊤ : ENat) : WithTop ENat) D.Glued := glued_isManifold D
  refine ⟨?_, ?_, ?_⟩
  · -- smoothness of `D.ιX`
    intro x
    have h2 : MDifferentiableAt I I (⇑D.homX) x :=
      ((mdifferentiable_homX_gen D hn).1 x (mem_univ x)).mdifferentiableAt
        (by rw [D.homX_source]; exact Filter.univ_mem)
    rwa [Work.Glue.homX_coe D] at h2
  · -- smoothness of `D.ιY`
    intro y
    have h2 : MDifferentiableAt I I (⇑D.homY) y :=
      ((mdifferentiable_homY_gen D hn).1 y (mem_univ y)).mdifferentiableAt
        (by rw [D.homY_source]; exact Filter.univ_mem)
    rwa [Work.Glue.homY_coe D] at h2
  · -- surjectivity of the derivative of `D.ιY`
    intro y
    have h1 := OpenPartialHomeomorph.MDifferentiable.mfderiv_surjective (e := D.homY)
      (mdifferentiable_homY_gen D hn) (mem_univ y)
    rwa [Work.Glue.homY_coe D] at h1

end Work.Glue
