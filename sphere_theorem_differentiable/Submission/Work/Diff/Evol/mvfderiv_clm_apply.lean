import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open scoped Manifold ContDiff Bundle Topology

namespace Work.Diff.Evol

/-- The map `(A, V) ↦ A V` written in extended charts is the pointwise application of the
two charted functions.  This is the structural identity behind `mvfderiv_clm_apply`. -/
lemma writtenInExtChartAt_clm_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace ℝ F₁]
    {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace ℝ F₂]
    {A : M → (F₁ →L[ℝ] F₂)} {V : M → F₁} {x : M} :
    writtenInExtChartAt I (modelWithCornersSelf ℝ F₂) x (fun y : M => A y (V y))
      = fun z => (writtenInExtChartAt I (modelWithCornersSelf ℝ (F₁ →L[ℝ] F₂)) x A) z
          ((writtenInExtChartAt I (modelWithCornersSelf ℝ F₁) x V) z) := by
  funext z
  simp only [writtenInExtChartAt, Function.comp_apply, ext_chart_model_space_apply]

/-- In the extended chart at `x`, the point `x` is read back as `x`. -/
lemma writtenInExtChartAt_center
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace ℝ F₂]
    {A : M → F₂} {x : M} :
    writtenInExtChartAt I (modelWithCornersSelf ℝ F₂) x A ((extChartAt I x) x) = A x := by
  simp only [writtenInExtChartAt, Function.comp_apply, extChartAt_to_inv, ext_chart_model_space_apply]

theorem mvfderiv_clm_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I (((⊤ : ℕ∞) : WithTop ℕ∞)) M]
    {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace ℝ F₁]
    {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace ℝ F₂]
    {A : M → (F₁ →L[ℝ] F₂)} {V : M → F₁} {x : M}
    (hA : MDifferentiableAt I (modelWithCornersSelf ℝ (F₁ →L[ℝ] F₂)) A x)
    (hV : MDifferentiableAt I (modelWithCornersSelf ℝ F₁) V x) (v : TangentSpace I x) :
    mvfderiv I (fun y : M => A y (V y)) x v
      = (mvfderiv I A x v) (V x) + (A x) (mvfderiv I V x v) := by
  have hΦ : MDifferentiableAt I (modelWithCornersSelf ℝ F₂) (fun y : M => A y (V y)) x :=
    hA.clm_apply hV
  have hxs : UniqueDiffWithinAt ℝ (Set.range I) ((extChartAt I x) x) := by
    simpa only [UniqueMDiffWithinAt, Set.preimage_univ, Set.univ_inter] using
      (uniqueMDiffWithinAt_univ (I := I) (x := x))
  have hdA : DifferentiableWithinAt ℝ
      (writtenInExtChartAt I (modelWithCornersSelf ℝ (F₁ →L[ℝ] F₂)) x A)
      (Set.range I) ((extChartAt I x) x) := by
    simpa only [Set.preimage_univ, Set.univ_inter] using hA.differentiableWithinAt_writtenInExtChartAt
  have hdV : DifferentiableWithinAt ℝ
      (writtenInExtChartAt I (modelWithCornersSelf ℝ F₁) x V)
      (Set.range I) ((extChartAt I x) x) := by
    simpa only [Set.preimage_univ, Set.univ_inter] using hV.differentiableWithinAt_writtenInExtChartAt
  have hcomp := writtenInExtChartAt_clm_apply (I := I) (A := A) (V := V) (x := x)
  have hwx := writtenInExtChartAt_center (I := I) (A := A) (x := x)
  have hwy := writtenInExtChartAt_center (I := I) (A := V) (x := x)
  have hkeyv : fderivWithin ℝ (fun z => (writtenInExtChartAt I (modelWithCornersSelf ℝ (F₁ →L[ℝ] F₂)) x A) z
        ((writtenInExtChartAt I (modelWithCornersSelf ℝ F₁) x V) z)) (Set.range I) ((extChartAt I x) x) v
      = ((writtenInExtChartAt I (modelWithCornersSelf ℝ (F₁ →L[ℝ] F₂)) x A) ((extChartAt I x) x)
            ∘SL fderivWithin ℝ (writtenInExtChartAt I (modelWithCornersSelf ℝ F₁) x V)
                (Set.range I) ((extChartAt I x) x)
          + (fderivWithin ℝ (writtenInExtChartAt I (modelWithCornersSelf ℝ (F₁ →L[ℝ] F₂)) x A)
                (Set.range I) ((extChartAt I x) x)).flip
              ((writtenInExtChartAt I (modelWithCornersSelf ℝ F₁) x V) ((extChartAt I x) x))) v :=
    congrArg (fun f => f v) (fderivWithin_clm_apply hxs hdA hdV)
  have h1 : mvfderiv I (fun y : M => A y (V y)) x v
      = fderivWithin ℝ (fun z => (writtenInExtChartAt I (modelWithCornersSelf ℝ (F₁ →L[ℝ] F₂)) x A) z
          ((writtenInExtChartAt I (modelWithCornersSelf ℝ F₁) x V) z)) (Set.range I)
            ((extChartAt I x) x) v := by
    rw [hΦ.mvfderiv, hcomp]
    rfl
  have h2 : fderivWithin ℝ (fun z => (writtenInExtChartAt I (modelWithCornersSelf ℝ (F₁ →L[ℝ] F₂)) x A) z
          ((writtenInExtChartAt I (modelWithCornersSelf ℝ F₁) x V) z)) (Set.range I)
            ((extChartAt I x) x) v
      = ((fderivWithin ℝ (writtenInExtChartAt I (modelWithCornersSelf ℝ (F₁ →L[ℝ] F₂)) x A)
            (Set.range I) ((extChartAt I x) x)) v) (V x)
        + (A x) ((fderivWithin ℝ (writtenInExtChartAt I (modelWithCornersSelf ℝ F₁) x V)
            (Set.range I) ((extChartAt I x) x)) v) := by
    rw [hkeyv]
    simp only [hwx, hwy]
    exact add_comm _ _
  rw [h1, h2, hA.mvfderiv, hV.mvfderiv]
  rfl

end Work.Diff.Evol
