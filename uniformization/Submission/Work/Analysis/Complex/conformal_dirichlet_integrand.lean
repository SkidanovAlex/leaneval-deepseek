import Mathlib
import Submission.Work.Jordan.dirichlet_integral

/-!
# Conformal invariance of the Dirichlet integrand

For `τ : ℂ → ℂ` complex differentiable at `z` and `u v : ℂ → ℝ` differentiable at `τ z`,
  `⟨∇(u∘τ), ∇(v∘τ)⟩ (z) = ‖τ'(z)‖² · ⟨∇u, ∇v⟩ (τ z)`.
This is the pointwise form of the conformal invariance of the Dirichlet density `⟨∇u, ∇v⟩ dA`; it is
the input of the chart-transfer step of the "energy" route to the symmetry of the Green function.
-/

open MeasureTheory Set Filter
open scoped Topology Gradient

noncomputable section

namespace Work.Analysis.Complex

theorem inner_conj_smul (c x y : ℂ) :
    inner (𝕜 := ℝ) ((starRingEnd ℂ) c • x) y = inner (𝕜 := ℝ) x (c • y) := by
  simp only [Complex.inner, smul_eq_mul, map_mul, Complex.conj_conj]
  ring_nf

theorem inner_conj_smul_conj_smul (c x y : ℂ) :
    inner (𝕜 := ℝ) ((starRingEnd ℂ) c • x) ((starRingEnd ℂ) c • y)
      = ‖c‖ ^ 2 * inner (𝕜 := ℝ) x y := by
  have h : ((starRingEnd ℂ) c * y) * (starRingEnd ℂ) ((starRingEnd ℂ) c * x)
      = ((‖c‖ ^ 2 : ℝ) : ℂ) * (y * (starRingEnd ℂ) x) := by
    calc ((starRingEnd ℂ) c * y) * (starRingEnd ℂ) ((starRingEnd ℂ) c * x)
        = ((starRingEnd ℂ) c * y) * (c * (starRingEnd ℂ) x) := by
          rw [map_mul, Complex.conj_conj]
      _ = (((starRingEnd ℂ) c * c) * (y * (starRingEnd ℂ) x)) := by ring
      _ = (((Complex.normSq c : ℝ) : ℂ) * (y * (starRingEnd ℂ) x)) := by
          rw [← Complex.normSq_eq_conj_mul_self]
      _ = (((‖c‖ ^ 2 : ℝ)) : ℂ) * (y * (starRingEnd ℂ) x) := by
          rw [Complex.normSq_eq_norm_sq]
  rw [Complex.inner, Complex.inner, smul_eq_mul, smul_eq_mul, h]
  rw [Complex.re_ofReal_mul]

/-- The gradient of a composition with a holomorphic map. -/
theorem gradient_comp_conformal {τ : ℂ → ℂ} {w : ℂ → ℝ} {z : ℂ}
    (hτ : DifferentiableAt ℂ τ z) (hw : DifferentiableAt ℝ w (τ z)) :
    gradient (fun x : ℂ => w (τ x)) z = (starRingEnd ℂ) (deriv τ z) • gradient w (τ z) := by
  have hcomp : fderiv ℝ (fun x : ℂ => w (τ x)) z
      = (fderiv ℝ w (τ z)).comp (fderiv ℝ τ z) := fderiv_comp z hw (hτ.restrictScalars ℝ)
  have hM : fderiv ℝ τ z = deriv τ z • (1 : ℂ →L[ℝ] ℂ) := Work.Jordan.fderiv_eq_smul_one hτ
  refine ext_inner_left ℝ (fun y => ?_)
  rw [real_inner_comm (gradient (fun x : ℂ => w (τ x)) z) y,
    real_inner_comm ((starRingEnd ℂ) (deriv τ z) • gradient w (τ z)) y,
    inner_gradient_left, inner_conj_smul, inner_gradient_left]
  rw [hcomp, ContinuousLinearMap.comp_apply, hM, ContinuousLinearMap.smul_apply,
    one_apply_eq_self]

/-- **Conformal invariance of the Dirichlet integrand.** -/
theorem conformal_dirichlet_integrand {τ : ℂ → ℂ} {u v : ℂ → ℝ} {z : ℂ}
    (hτ : DifferentiableAt ℂ τ z) (hu : DifferentiableAt ℝ u (τ z))
    (hv : DifferentiableAt ℝ v (τ z)) :
    inner (𝕜 := ℝ) (gradient (fun w : ℂ => u (τ w)) z) (gradient (fun w : ℂ => v (τ w)) z)
      = ‖deriv τ z‖ ^ 2 * inner (𝕜 := ℝ) (gradient u (τ z)) (gradient v (τ z)) := by
  rw [gradient_comp_conformal hτ hu, gradient_comp_conformal hτ hv, inner_conj_smul_conj_smul]

end Work.Analysis.Complex
