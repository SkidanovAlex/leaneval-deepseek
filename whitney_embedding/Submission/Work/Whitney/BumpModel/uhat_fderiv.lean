import Mathlib
import Submission.Work.Whitney.BumpModel.Defs

namespace Work.Whitney.BumpModel

open scoped Manifold ContDiff
open Set Filter Topology

noncomputable section

/-! ### Derivative of the denominator `bumpU = 1 + ∑ᵢ xᵢ²` -/

/-- The derivative of `bumpU n x = 1 + ∑ᵢ xᵢ²` at `x`, as a continuous linear map. -/
theorem hasFDerivAt_bumpU (n : ℕ) [NeZero n] (x : Fin n → ℝ) :
    HasFDerivAt (Work.Whitney.bumpU n)
      (∑ i, (2 * x i) • (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i)) x := by
  have hsum := HasFDerivAt.sum (u := Finset.univ)
    (A := fun (i : Fin n) (y : Fin n → ℝ) => y i ^ 2)
    (A' := fun (i : Fin n) => (2 * x i) •
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i))
    (x := x) (fun i _ => by
      have h1 : HasFDerivAt (fun y : Fin n → ℝ => y i)
          ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i) :
            (Fin n → ℝ) →L[ℝ] ℝ) x :=
        ContinuousLinearMap.hasFDerivAt
          ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i) :
            (Fin n → ℝ) →L[ℝ] ℝ)
      have h2 := h1.pow 2
      simpa using h2)
  have hfun : (∑ i : Fin n, (fun y : Fin n → ℝ => y i ^ 2)) = (fun y => ∑ i, y i ^ 2) := by
    funext y
    simp [Finset.sum_apply]
  rw [hfun] at hsum
  have h2 : HasFDerivAt
      (fun y : Fin n → ℝ => (fun _ => (1 : ℝ)) y + (fun y => ∑ i, y i ^ 2) y)
      (0 + ∑ i, (2 * x i) • (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i))
      x :=
    (hasFDerivAt_const (1 : ℝ) x).add hsum
  change HasFDerivAt (Work.Whitney.bumpU n)
      (∑ i, (2 * x i) • (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i)) x
  rw [zero_add] at h2
  exact h2

/-- The value of the derivative of `bumpU` on a vector `v`. -/
theorem fderiv_bumpU_apply (n : ℕ) [NeZero n] (x v : Fin n → ℝ) :
    (fderiv ℝ (Work.Whitney.bumpU n) x) v = ∑ i, 2 * x i * v i := by
  rw [(hasFDerivAt_bumpU n x).fderiv]
  simp [ContinuousLinearMap.proj_apply]

/-- Derivative of `x ↦ (bumpU n x)⁻¹`. -/
theorem hasFDerivAt_inv_bumpU (n : ℕ) [NeZero n] (x : Fin n → ℝ) :
    HasFDerivAt (fun y : Fin n → ℝ => (Work.Whitney.bumpU n y)⁻¹)
      ((ContinuousLinearMap.toSpanSingleton ℝ (-(Work.Whitney.bumpU n x ^ 2)⁻¹)).comp
        (fderiv ℝ (Work.Whitney.bumpU n) x)) x := by
  have hg : HasFDerivAt (fun t : ℝ => t⁻¹)
      (ContinuousLinearMap.toSpanSingleton ℝ (-(Work.Whitney.bumpU n x ^ 2)⁻¹))
      (Work.Whitney.bumpU n x) :=
    hasFDerivAt_inv (ne_of_gt (Work.Whitney.bumpU_pos n x))
  have hf := hasFDerivAt_bumpU n x
  have hcomp := hg.comp x hf
  rw [← hf.fderiv] at hcomp
  simpa [Function.comp_def] using hcomp

/-- The value of the derivative of `x ↦ (bumpU n x)⁻¹` on a vector `v`. -/
theorem fderiv_inv_bumpU_apply (n : ℕ) [NeZero n] (x v : Fin n → ℝ) :
    (fderiv ℝ (fun y : Fin n → ℝ => (Work.Whitney.bumpU n y)⁻¹) x) v =
      -((Work.Whitney.bumpU n x) ^ 2)⁻¹ * (∑ i, 2 * x i * v i) := by
  rw [(hasFDerivAt_inv_bumpU n x).fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply,
    fderiv_bumpU_apply n x v]
  ring

/-! ### Evaluation at `±e₀` -/

theorem bumpU_e0 (n : ℕ) [NeZero n] : Work.Whitney.bumpU n (Work.Whitney.e0 n) = 2 := by
  simp [Work.Whitney.bumpU, Work.Whitney.e0, Pi.single_apply, Finset.sum_ite_eq']
  norm_num

theorem bumpU_neg_e0 (n : ℕ) [NeZero n] :
    Work.Whitney.bumpU n (-(Work.Whitney.e0 n)) = 2 := by
  simp [Work.Whitney.bumpU, Work.Whitney.e0, Pi.single_apply, Finset.sum_ite_eq']
  norm_num

theorem sum_e0 (n : ℕ) [NeZero n] (v : Fin n → ℝ) :
    (∑ i, 2 * (Work.Whitney.e0 n) i * v i) = 2 * v 0 := by
  simp [Work.Whitney.e0, Pi.single_apply, Finset.sum_ite_eq']

theorem sum_neg_e0 (n : ℕ) [NeZero n] (v : Fin n → ℝ) :
    (∑ i, 2 * (-(Work.Whitney.e0 n)) i * v i) = -2 * v 0 := by
  simp [Work.Whitney.e0, Pi.single_apply, Finset.sum_ite_eq']

/-- The derivative of `û = χ/(1 + ∑xᵢ²)` at `±e₀`, where `χ = 1` on the closed ball of radius `2`. -/
theorem uhat_fderiv (n : ℕ) [NeZero n] {χ : (Fin n → ℝ) → ℝ} (hχ : ContDiff ℝ ⊤ χ)
    (hχ1 : ∀ x, ‖x‖ ≤ 2 → χ x = 1) (v : Fin n → ℝ) :
    (fderiv ℝ (Work.Whitney.uhat n χ) (Work.Whitney.e0 n)) v = -(1 / 2) * v 0 ∧
      (fderiv ℝ (Work.Whitney.uhat n χ) (-(Work.Whitney.e0 n))) v = (1 / 2) * v 0 := by
  constructor
  · have hlt : ∀ᶠ x in 𝓝 (Work.Whitney.e0 n), ‖x‖ < 2 := by
      have hcont : Tendsto (fun x : Fin n → ℝ => ‖x‖) (𝓝 (Work.Whitney.e0 n))
          (𝓝 ‖Work.Whitney.e0 n‖) := continuous_norm.continuousAt
      exact hcont.eventually (Iio_mem_nhds (by rw [Work.Whitney.norm_e0]; norm_num))
    have hfχ : χ =ᶠ[𝓝 (Work.Whitney.e0 n)] (fun _ => (1 : ℝ)) :=
      hlt.mono (fun x hx => hχ1 x (le_of_lt hx))
    have hu : Work.Whitney.uhat n χ =ᶠ[𝓝 (Work.Whitney.e0 n)]
        (fun y : Fin n → ℝ => (Work.Whitney.bumpU n y)⁻¹) :=
      hfχ.mono (fun y hy => by simp [Work.Whitney.uhat, hy])
    rw [hu.fderiv_eq, fderiv_inv_bumpU_apply n (Work.Whitney.e0 n) v, bumpU_e0 n,
      sum_e0 n v]
    norm_num
    ring
  · have hlt : ∀ᶠ x in 𝓝 (-(Work.Whitney.e0 n)), ‖x‖ < 2 := by
      have hcont : Tendsto (fun x : Fin n → ℝ => ‖x‖) (𝓝 (-(Work.Whitney.e0 n)))
          (𝓝 ‖-(Work.Whitney.e0 n)‖) := continuous_norm.continuousAt
      exact hcont.eventually
        (Iio_mem_nhds (by rw [norm_neg, Work.Whitney.norm_e0]; norm_num))
    have hfχ : χ =ᶠ[𝓝 (-(Work.Whitney.e0 n))] (fun _ => (1 : ℝ)) :=
      hlt.mono (fun x hx => hχ1 x (le_of_lt hx))
    have hu : Work.Whitney.uhat n χ =ᶠ[𝓝 (-(Work.Whitney.e0 n))]
        (fun y : Fin n → ℝ => (Work.Whitney.bumpU n y)⁻¹) :=
      hfχ.mono (fun y hy => by simp [Work.Whitney.uhat, hy])
    rw [hu.fderiv_eq, fderiv_inv_bumpU_apply n (-(Work.Whitney.e0 n)) v, bumpU_neg_e0 n,
      sum_neg_e0 n v]
    norm_num
    ring

end

end Work.Whitney.BumpModel
