import Mathlib
import Submission.Work.Drive.EpsForm.goodHeight_exists

namespace Work.Drive.Mono.Band

open scoped RealInnerProductSpace
open LeanEval.KnotTheory.PardonDistortion

/-- The derivative, with respect to the direction, of the height along a branch of critical points
is the point of the surface itself: `∇_n ⟪n, par ψ (y n)⟫ = par ψ (y n₀)`.  (The branch moves
tangentially, so the term arising from the motion of the branch vanishes by criticality; hence the
gradient of the difference of two branch heights is the chord between the two surface points.) -/
theorem fderiv_branchHeight_euclid (ψ : Submission.Diffeo)
    {y : LeanEval.KnotTheory.PardonDistortion.R3 → ℝ × ℝ}
    {n₀ : LeanEval.KnotTheory.PardonDistortion.R3}
    (hy : DifferentiableAt ℝ y n₀)
    (hcrit : fderiv ℝ (Work.Drive.EpsForm.heightOf ψ n₀) (y n₀) = 0) :
    fderiv ℝ (fun n : LeanEval.KnotTheory.PardonDistortion.R3 =>
        Work.Drive.EpsForm.heightOf ψ n (y n)) n₀
      = (innerSL ℝ) (Work.BoxShrink.Pinch.par ψ (y n₀)) := by
  -- The map `n ↦ ⟪n, par ψ (y n)⟫` splits into the *branch height* `A n = heightOf ψ n₀ (y n)`
  -- and the *chord form* `C n = ⟪n - n₀, par ψ (y n)⟫`.
  have hcd : DifferentiableAt ℝ (Work.Drive.EpsForm.heightOf ψ n₀) (y n₀) :=
    ((Work.Drive.EpsForm.heightOf_contDiff ψ n₀).differentiable (by simp)).differentiableAt
  -- The branch-height term has vanishing derivative at `n₀` precisely by criticality.
  have hA_has : HasFDerivAt (fun n : R3 => Work.Drive.EpsForm.heightOf ψ n₀ (y n))
      ((fderiv ℝ (Work.Drive.EpsForm.heightOf ψ n₀) (y n₀)).comp (fderiv ℝ y n₀)) n₀ :=
    hcd.hasFDerivAt.comp n₀ hy.hasFDerivAt
  have hA0 : fderiv ℝ (fun n : R3 => Work.Drive.EpsForm.heightOf ψ n₀ (y n)) n₀ = 0 := by
    rw [hA_has.fderiv, hcrit]
    exact ContinuousLinearMap.zero_comp _
  have hpar_d : DifferentiableAt ℝ (Work.BoxShrink.Pinch.par ψ) (y n₀) :=
    ((Work.BoxShrink.Pinch.par_contDiff ψ).differentiable (by simp)).differentiableAt
  have hT_d : DifferentiableAt ℝ (fun n : R3 => Work.BoxShrink.Pinch.par ψ (y n)) n₀ :=
    hpar_d.comp n₀ hy
  have hf_d : DifferentiableAt ℝ (fun n : R3 => n - n₀) n₀ := by fun_prop
  -- The chord form has derivative the surface point, since the first factor vanishes at `n₀`.
  have hC_eq : fderiv ℝ (fun n : R3 => inner ℝ (n - n₀) (Work.BoxShrink.Pinch.par ψ (y n))) n₀
      = innerSL ℝ (Work.BoxShrink.Pinch.par ψ (y n₀)) := by
    ext v
    rw [fderiv_inner_apply ℝ hf_d hT_d]
    have h1 : (fderiv ℝ (fun n : R3 => n - n₀) n₀) = ContinuousLinearMap.id ℝ R3 := by
      rw [fderiv_sub_const]
      simp
    rw [h1]
    simp only [ContinuousLinearMap.id_apply, sub_self, inner_zero_left, zero_add,
      innerSL_apply_apply]
    rw [real_inner_comm]
  have hsplit : (fun n : R3 => Work.Drive.EpsForm.heightOf ψ n (y n))
      = (fun n : R3 => Work.Drive.EpsForm.heightOf ψ n₀ (y n))
        + (fun n : R3 => inner ℝ (n - n₀) (Work.BoxShrink.Pinch.par ψ (y n))) := by
    funext n
    simp only [Pi.add_apply, Work.Drive.EpsForm.heightOf]
    have hkey : n₀ + (n - n₀) = n := by abel
    rw [← inner_add_left, hkey]
  have hAd : DifferentiableAt ℝ (fun n : R3 => Work.Drive.EpsForm.heightOf ψ n₀ (y n)) n₀ :=
    hA_has.differentiableAt
  have hCd : DifferentiableAt ℝ
      (fun n : R3 => inner ℝ (n - n₀) (Work.BoxShrink.Pinch.par ψ (y n))) n₀ :=
    DifferentiableAt.inner ℝ hf_d hT_d
  rw [hsplit, fderiv_add hAd hCd, hA0, hC_eq, zero_add]

end Work.Drive.Mono.Band
