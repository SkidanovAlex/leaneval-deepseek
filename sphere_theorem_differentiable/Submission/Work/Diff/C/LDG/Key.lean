import Submission.Work.Diff.C.LDG.Normalize

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The differential of the normalization `G₀ F = (rad F ·)⁻¹ • U F`
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option backward.isDefEq.respectTransparency false

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology EuclideanSpace
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.C.LDG

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- If the differential of `G₀ F` vanishes at `x` in the direction `v`, then the differential of
`U F` at `x` in the direction `v` is a multiple of `U F x`. -/
theorem exists_smul_of_mfderiv_G0_eq_zero {F : Idx E → M → ℝ}
    (hU : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Idx E)) ∞ (U F))
    {x : M} (hx : 0 < sq F x) {v : TangentSpace I x}
    (h : mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Idx E)) (G₀ F) x v = 0) :
    ∃ μ : ℝ, mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Idx E)) (U F) x v = μ • U F x := by
  set Φ : EuclideanSpace ℝ (Idx E) → EuclideanSpace ℝ (Idx E) := fun z => ‖z‖⁻¹ • z with hΦdef
  set y : EuclideanSpace ℝ (Idx E) := U F x with hydef
  set w : EuclideanSpace ℝ (Idx E) := mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Idx E)) (U F) x v
    with hwdef
  have hyne : y ≠ 0 := by
    intro h0
    have h1 : ‖y‖ = 0 := by rw [h0]; simp
    rw [hydef, norm_U] at h1
    exact absurd h1 (ne_of_gt (rad_pos F hx))
  have hΦeq : G₀ F = Φ ∘ U F := by
    funext z
    simp only [Function.comp_apply, hΦdef, G₀_def, norm_U F z]
  have hcontΦ : ContMDiffAt 𝓘(ℝ, EuclideanSpace ℝ (Idx E))
      𝓘(ℝ, EuclideanSpace ℝ (Idx E)) ∞ Φ y := by
    rw [hΦdef, contMDiffAt_iff_contDiffAt]
    have hnorm : ContDiffAt ℝ ∞ (fun z : EuclideanSpace ℝ (Idx E) => ‖z‖) y :=
      ContDiffAt.norm ℝ contDiffAt_id hyne
    have hne' : (fun z : EuclideanSpace ℝ (Idx E) => ‖z‖) y ≠ 0 := by
      simpa using (norm_ne_zero_iff.mpr hyne)
    exact ContDiffAt.smul (ContDiffAt.inv hnorm hne') contDiffAt_id
  have hmdU : MDiffAt (U F) x := (hU x).mdifferentiableAt (by simp)
  have hmdΦ : MDiffAt Φ y := hcontΦ.mdifferentiableAt (by simp)
  have hchain : mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Idx E)) (Φ ∘ U F) x
      = mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Idx E)) 𝓘(ℝ, EuclideanSpace ℝ (Idx E)) Φ y
        ∘SL mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Idx E)) (U F) x :=
    mfderiv_comp x hmdΦ hmdU
  have hzero : fderiv ℝ Φ y w = 0 := by
    have h1 : mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Idx E)) (Φ ∘ U F) x v
        = (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Idx E)) 𝓘(ℝ, EuclideanSpace ℝ (Idx E)) Φ y
            ∘SL mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Idx E)) (U F) x) v :=
      congrArg (fun L => L v) hchain
    rw [hΦeq] at h
    rw [h] at h1
    simp only [ContinuousLinearMap.comp_apply] at h1
    rw [← hwdef, mfderiv_eq_fderiv] at h1
    exact h1.symm
  rw [hΦdef] at hzero
  rw [fderiv_normalize_apply y hyne w] at hzero
  have h1 : ‖y‖⁻¹ • w = ((‖y‖ ^ 3)⁻¹ * Inner.inner ℝ y w) • y := sub_eq_zero.mp hzero
  have h2 : (‖y‖ * ((‖y‖ ^ 3)⁻¹ * Inner.inner ℝ y w)) • y = w := by
    rw [mul_smul, ← h1, ← mul_smul, mul_inv_cancel₀ (ne_of_gt (norm_pos_iff.mpr hyne)), one_smul]
  exact ⟨_, h2.symm⟩

end Work.Diff.C.LDG
