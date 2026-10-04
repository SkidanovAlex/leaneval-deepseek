import Mathlib
import Submission.Work.Diff.Dim2.PushField

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.Dim2

open scoped Manifold ContDiff Bundle Topology ENNReal InnerProductSpace
open Bundle ContDiff Set Filter

theorem pushField_mfderiv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
      [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℝ G]
    {e : F ≃ₗᵢ[ℝ] G} {f : M → F} {x : M}
    (hf : MDifferentiableAt I 𝓘(ℝ, F) f x) :
    (∀ v : TangentSpace I x,
        mfderiv I 𝓘(ℝ, G) (Work.Diff.Dim2.pushField e f) x v
          = e (mfderiv I 𝓘(ℝ, F) f x v)) ∧
      (mfderiv I 𝓘(ℝ, F) f x ≠ 0 →
        mfderiv I 𝓘(ℝ, G) (Work.Diff.Dim2.pushField e f) x ≠ 0) := by
  -- `pushField e f` is the composition of `f` with the linear isometry `e`.
  have hg : MDifferentiableAt 𝓘(ℝ, F) 𝓘(ℝ, G) (fun z : F => e z) (f x) :=
    (ContinuousLinearMap.differentiableAt (e : F →L[ℝ] G)).mdifferentiableAt
  -- the differential of a continuous linear map is the map itself
  have hg' : mfderiv 𝓘(ℝ, F) 𝓘(ℝ, G) (fun z : F => e z) (f x) = (e : F →L[ℝ] G) := by
    rw [mfderiv_eq_fderiv]
    exact ContinuousLinearMap.fderiv (e : F →L[ℝ] G)
  -- so the chain rule gives the differential of the push-forward
  have hcomp : mfderiv I 𝓘(ℝ, G) (Work.Diff.Dim2.pushField e f) x
      = ((e : F →L[ℝ] G)).comp (mfderiv I 𝓘(ℝ, F) f x) := by
    have h := mfderiv_comp (I := I) (I' := 𝓘(ℝ, F)) (I'' := 𝓘(ℝ, G)) x hg hf
    rw [show Work.Diff.Dim2.pushField e f = (fun z : F => e z) ∘ f from rfl]
    rw [h, hg']
    try rfl
  have hpoint : ∀ v : TangentSpace I x,
      mfderiv I 𝓘(ℝ, G) (Work.Diff.Dim2.pushField e f) x v
        = e (mfderiv I 𝓘(ℝ, F) f x v) := by
    intro v
    rw [hcomp]
    rfl
  refine ⟨hpoint, ?_⟩
  -- injectivity of `e` upgrades the non-vanishing of the differential
  rintro hf0 h0
  apply hf0
  ext v
  have h : e (mfderiv I 𝓘(ℝ, F) f x v) = e (0 : F) := by
    rw [map_zero]
    have h1 := hpoint v
    rw [h0, zero_apply] at h1
    exact h1.symm
  exact e.injective h

end Work.Diff.Dim2
