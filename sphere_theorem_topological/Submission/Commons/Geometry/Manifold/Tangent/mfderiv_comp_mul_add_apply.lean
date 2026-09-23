import Mathlib.Geometry.Manifold.Instances.Icc

namespace Commons.Geometry.Manifold.Tangent

open scoped _root_.ContDiff _root_.Manifold

theorem mfderiv_comp_mul_add_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    (γ : ℝ → M) (c d t : ℝ)
    (hd : MDifferentiableAt (modelWithCornersSelf ℝ ℝ) I γ (c * t + d)) :
    (mfderiv (modelWithCornersSelf ℝ ℝ) I (fun s : ℝ => γ (c * s + d)) t) 1
      = c • (mfderiv (modelWithCornersSelf ℝ ℝ) I γ (c * t + d)) 1 := by
  have hf : MDifferentiableAt 𝓘(ℝ) 𝓘(ℝ) (fun s : ℝ => c * s + d) t := by
    rw [mdifferentiableAt_iff_differentiableAt]
    exact ((differentiableAt_id (x := t)).const_mul c).add_const d
  have hmd : (mfderiv 𝓘(ℝ) 𝓘(ℝ) (fun s : ℝ => c * s + d) t) (1 : ℝ) = c := by
    have hf' : HasFDerivAt (fun s : ℝ => c * s + d) (c • ContinuousLinearMap.id ℝ ℝ) t := by
      have h2 := (hasFDerivAt_id (𝕜 := ℝ) t).const_mul c
      exact h2.add_const d
    rw [mfderiv_eq_fderiv]
    show fderiv ℝ (fun s : ℝ => c * s + d) t 1 = c
    rw [hf'.fderiv]
    simp
  have hcomp := mfderiv_comp_apply (f := fun s : ℝ => c * s + d) (g := γ) t hd hf (1 : ℝ)
  calc (mfderiv 𝓘(ℝ) I (fun s : ℝ => γ (c * s + d)) t) (1 : ℝ)
      = (mfderiv 𝓘(ℝ) I γ (c * t + d))
          ((mfderiv 𝓘(ℝ) 𝓘(ℝ) (fun s : ℝ => c * s + d) t) (1 : ℝ)) := hcomp
    _ = (mfderiv 𝓘(ℝ) I γ (c * t + d)) (c : TangentSpace 𝓘(ℝ) (c * t + d)) := by rw [hmd]
    _ = c • (mfderiv 𝓘(ℝ) I γ (c * t + d)) (1 : TangentSpace 𝓘(ℝ) (c * t + d)) := by
        rw [← map_smul]
        congr 1
        show (c : ℝ) = c * (1 : ℝ)
        ring

end Commons.Geometry.Manifold.Tangent