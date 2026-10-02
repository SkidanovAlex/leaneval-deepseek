import Mathlib
import Submission.Work.Morse.Transfer

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Morse

open scoped Manifold ContDiff Topology
open Set

set_option linter.style.haveILetI false

/-- Transfer of differentiability at a point along the change of model: `f : M → ℝ` is
differentiable at `x` for the pushed forward atlas iff it is differentiable at `x` for the original
atlas.  The topology on `M` is unchanged, so continuity is unchanged, and the chart expression of
`f` in the pushed structure is the original chart expression composed with `L.symm`
(`Work.Morse.writtenInExtChartAt_push`). -/
lemma mdifferentiableAt_push {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    (L : E ≃L[ℝ] E') (f : M → ℝ) (x : M) :
    (letI : ChartedSpace E' M := Work.Morse.pushChartedSpace (Work.Morse.modelHomeo I L);
      MDifferentiableAt (𝓘(ℝ,E')) 𝓘(ℝ,ℝ) f x) ↔ MDifferentiableAt I 𝓘(ℝ,ℝ) f x := by
  letI : ChartedSpace E' M := Work.Morse.pushChartedSpace (Work.Morse.modelHomeo I L)
  rw [mdifferentiableAt_iff, mdifferentiableAt_iff]
  refine and_congr_right (fun _ => ?_)
  rw [Work.Morse.writtenInExtChartAt_push]
  rw [ModelWithCorners.range_eq_univ (𝓘(ℝ,E')), ModelWithCorners.range_eq_univ I]
  rw [show (extChartAt (𝓘(ℝ,E')) x) x = L ((extChartAt I x) x) from by
        rw [Work.Morse.extChartAt_push_coe]]
  rw [show (fun z => writtenInExtChartAt I 𝓘(ℝ,ℝ) x f (L.symm z))
        = (writtenInExtChartAt I 𝓘(ℝ,ℝ) x f ∘ ⇑(L.symm : E' ≃L[ℝ] E)) from rfl]
  rw [differentiableWithinAt_univ, differentiableWithinAt_univ]
  have hiff := ContinuousLinearEquiv.comp_right_differentiableAt_iff (𝕜 := ℝ)
      (iso := (L.symm : E' ≃L[ℝ] E))
      (f := writtenInExtChartAt I 𝓘(ℝ,ℝ) x f) (x := L ((extChartAt I x) x))
  simpa only [ContinuousLinearEquiv.symm_apply_apply] using hiff

/-- The Fréchet derivative of `F ∘ L.symm` on the whole space, at the point `L a`, is the
derivative of `F` at `a`, composed with `L.symm`.  This is the chain rule for a continuous linear
equivalence (`ContinuousLinearEquiv.comp_right_fderivWithin`). -/
lemma fderivWithin_comp_symm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    (L : E ≃L[ℝ] E') (F : E → ℝ) (a : E) :
    fderivWithin ℝ (F ∘ ⇑(L.symm : E' ≃L[ℝ] E)) univ (L a)
      = (fderivWithin ℝ F univ a).comp (L.symm : E' →L[ℝ] E) := by
  have h := ContinuousLinearEquiv.comp_right_fderivWithin (𝕜 := ℝ)
    (iso := (L.symm : E' ≃L[ℝ] E)) (f := F) (s := univ) (x := L a)
    (by simp [uniqueDiffWithinAt_univ])
  simpa only [preimage_univ, ContinuousLinearEquiv.symm_apply_apply] using h

/-- The manifold derivative of a real function is transported by the change of model: in the pushed
forward structure the derivative is the original derivative composed with `L.symm`.  Use
`Work.Morse.writtenInExtChartAt_push` (`Submission.Work.Morse.Transfer`), the definition of
`HasMFDerivAt` (its chart expression, the set `range I = univ` and the point transform by `L`), and
the chain rule `HasFDerivWithinAt.comp`; the case distinction in the definition of `mfderiv` needs
the corresponding transfer of `MDifferentiableAt`, which follows from `mdifferentiableAt_iff`. -/
theorem mfderiv_push {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    (L : E ≃L[ℝ] E') (f : M → ℝ) (x : M) :
    (letI : ChartedSpace E' M := Work.Morse.pushChartedSpace (Work.Morse.modelHomeo I L);
      mfderiv (𝓘(ℝ,E')) 𝓘(ℝ,ℝ) f x)
      = (mfderiv I 𝓘(ℝ,ℝ) f x).comp (L.symm : E' →L[ℝ] E) := by
  letI : ChartedSpace E' M := Work.Morse.pushChartedSpace (Work.Morse.modelHomeo I L)
  by_cases h : MDifferentiableAt I 𝓘(ℝ,ℝ) f x
  · have h' : MDifferentiableAt (𝓘(ℝ,E')) 𝓘(ℝ,ℝ) f x := (mdifferentiableAt_push L f x).2 h
    rw [MDifferentiableAt.mfderiv h', MDifferentiableAt.mfderiv h]
    rw [Work.Morse.writtenInExtChartAt_push]
    rw [ModelWithCorners.range_eq_univ (𝓘(ℝ,E')), ModelWithCorners.range_eq_univ I]
    rw [show (extChartAt (𝓘(ℝ,E')) x) x = L ((extChartAt I x) x) from by
          rw [Work.Morse.extChartAt_push_coe]]
    exact fderivWithin_comp_symm L (writtenInExtChartAt I 𝓘(ℝ,ℝ) x f) ((extChartAt I x) x)
  · have h' : ¬ MDifferentiableAt (𝓘(ℝ,E')) 𝓘(ℝ,ℝ) f x :=
      fun hh => h ((mdifferentiableAt_push L f x).1 hh)
    rw [mfderiv_zero_of_not_mdifferentiableAt h', mfderiv_zero_of_not_mdifferentiableAt h]
    show (0 : E' →L[ℝ] ℝ) = (0 : E →L[ℝ] ℝ).comp (L.symm : E' →L[ℝ] E)
    simp

end Work.Morse
