import Mathlib
import Submission.Work.CR.Flat.Cauchy
import Submission.Work.CR.Flat.Holder
import Submission.Work.CR.Flat.Cauchy.holderNorm_le_wirtinger

namespace Work.NN.Newton.FTsharp

open Work.CR.Flat.Cauchy

/-- The flat `∂̄` map on real differentials, evaluated on an operator:
`dbarCLM L = (1/2) (L 1 + i • L i)`. -/
lemma dbarCLM_apply (L : ℂ →L[ℝ] ℂ) :
    dbarCLM L = (1 / 2 : ℝ) • (L 1 + Complex.I • L Complex.I) := by
  simp only [dbarCLM, smul_apply, add_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply,
    ContinuousLinearMap.lsmul_apply]

/-- `dbarCLM` does not increase operator norms. -/
lemma norm_dbarCLM_le_one : ‖dbarCLM‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun L => ?_)
  rw [one_mul, dbarCLM_apply L, norm_smul]
  have hhalf : ‖(1 / 2 : ℝ)‖ = 1 / 2 := by norm_num
  rw [hhalf]
  have h1 : ‖L (1 : ℂ)‖ ≤ ‖L‖ := by
    simpa using ContinuousLinearMap.le_opNorm L (1 : ℂ)
  have h2 : ‖L Complex.I‖ ≤ ‖L‖ := by
    simpa using ContinuousLinearMap.le_opNorm L Complex.I
  have h3 : ‖Complex.I • L Complex.I‖ = ‖L Complex.I‖ := by
    rw [norm_smul, Complex.norm_I, one_mul]
  have h4 : ‖L 1 + Complex.I • L Complex.I‖ ≤ ‖L 1‖ + ‖Complex.I • L Complex.I‖ :=
    norm_add_le _ _
  rw [h3] at h4
  linarith

/-- Pointwise form of `norm_dbarCLM_le_one`. -/
lemma norm_dbarCLM_apply_le (L : ℂ →L[ℝ] ℂ) : ‖dbarCLM L‖ ≤ ‖L‖ := by
  calc ‖dbarCLM L‖ ≤ ‖dbarCLM‖ * ‖L‖ := ContinuousLinearMap.le_opNorm dbarCLM L
    _ ≤ 1 * ‖L‖ := mul_le_mul_of_nonneg_right norm_dbarCLM_le_one (norm_nonneg L)
    _ = ‖L‖ := one_mul ‖L‖

/-- Postcomposition by a linear map of operator norm at most one is norm
non-increasing. -/
lemma norm_comp_le_of_opNorm_le_one {A : (ℂ →L[ℝ] ℂ) →L[ℝ] ℂ} (hA : ‖A‖ ≤ 1)
    (X : ℂ →L[ℝ] (ℂ →L[ℝ] ℂ)) : ‖A.comp X‖ ≤ ‖X‖ := by
  calc ‖A.comp X‖ ≤ ‖A‖ * ‖X‖ := ContinuousLinearMap.opNorm_comp_le A X
    _ ≤ 1 * ‖X‖ := mul_le_mul_of_nonneg_right hA (norm_nonneg X)
    _ = ‖X‖ := one_mul ‖X‖

/-- A Lipschitz bound `‖g z - g w‖ ≤ C ‖z - w‖` bounds the operator norm of the
derivative by `C`. -/
lemma norm_fderiv_le_of_norm_sub_le {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {g : E → F} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ z w : E, ‖g z - g w‖ ≤ C * ‖z - w‖) (z : E) :
    ‖fderiv ℝ g z‖ ≤ C := by
  have hlip : LipschitzWith C.toNNReal g :=
    LipschitzWith.of_dist_le' (fun x y => by simpa only [dist_eq_norm] using h x y)
  have hle := norm_fderiv_le_of_lipschitz ℝ hlip (x₀ := z)
  rwa [Real.coe_toNNReal C hC] at hle

/-- Chain rule for a continuous linear map applied to a differentiable family of
operators: the derivative of `z ↦ A (g z)` is `A.comp (fderiv g z)`. -/
lemma fderiv_clm_comp {A : (ℂ →L[ℝ] ℂ) →L[ℝ] ℂ} {g : ℂ → (ℂ →L[ℝ] ℂ)} {z : ℂ}
    (hg : DifferentiableAt ℝ g z) :
    fderiv ℝ (fun u => A (g u)) z = A.comp (fderiv ℝ g z) := by
  have h := fderiv_comp z (f := g) (g := ⇑A) A.differentiableAt hg
  have hgoal : fderiv ℝ (fun u => A (g u)) z = fderiv ℝ (⇑A ∘ g) z := rfl
  rw [hgoal, h, ContinuousLinearMap.fderiv]

theorem dbarC_bounds {f : ℂ → ℂ} (hf : ContDiff ℝ 2 f)
    {M₁ M₂ M₃ : ℝ} (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂) (hM₃ : 0 ≤ M₃)
    (h1 : ∀ z : ℂ, ‖fderiv ℝ f z‖ ≤ M₁)
    (h2 : ∀ z w : ℂ, ‖fderiv ℝ f z - fderiv ℝ f w‖ ≤ M₂ * ‖z - w‖)
    (h3 : ∀ z w : ℂ, ‖(fderiv ℝ (fun u => fderiv ℝ f u)) z
        - (fderiv ℝ (fun u => fderiv ℝ f u)) w‖ ≤ M₃ * ‖z - w‖) :
    ContDiff ℝ 1 (fun z => Work.CR.Flat.dbarC f z) ∧
    (∀ z : ℂ, ‖Work.CR.Flat.dbarC f z‖ ≤ M₁) ∧
    (∀ z : ℂ, ‖fderiv ℝ (fun u => Work.CR.Flat.dbarC f u) z‖ ≤ M₂) ∧
    (∀ z w : ℂ, ‖fderiv ℝ (fun u => Work.CR.Flat.dbarC f u) z
        - fderiv ℝ (fun u => Work.CR.Flat.dbarC f u) w‖ ≤ M₃ * ‖z - w‖) := by
  have hA : ‖dbarCLM‖ ≤ 1 := norm_dbarCLM_le_one
  have hLcd : ContDiff ℝ 1 (fun u : ℂ => fderiv ℝ f u) := by
    simpa using hf.fderiv_right (by norm_num : ((1 : ℕ) : WithTop ℕ∞) + 1 ≤ (2 : WithTop ℕ∞))
  have hLdiff : ∀ z : ℂ, DifferentiableAt ℝ (fun u : ℂ => fderiv ℝ f u) z :=
    fun z => (hLcd.differentiable (by simp)).differentiableAt
  have hdbar_eq : (fun z : ℂ => Work.CR.Flat.dbarC f z)
      = ⇑dbarCLM ∘ (fun u : ℂ => fderiv ℝ f u) := dbarC_eq_dbarCLM f
  have hfdeq : ∀ z : ℂ, fderiv ℝ (fun u : ℂ => Work.CR.Flat.dbarC f u) z
      = dbarCLM.comp (fderiv ℝ (fun u : ℂ => fderiv ℝ f u) z) := by
    intro z
    rw [hdbar_eq]
    exact fderiv_clm_comp (A := dbarCLM) (g := fun u : ℂ => fderiv ℝ f u) (z := z) (hLdiff z)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hdbar_eq]
    exact dbarCLM.contDiff.comp hLcd
  · intro z
    have hz : Work.CR.Flat.dbarC f z = dbarCLM (fderiv ℝ f z) :=
      congrFun (dbarC_eq_dbarCLM f) z
    rw [hz]
    exact le_trans (norm_dbarCLM_apply_le _) (h1 z)
  · intro z
    rw [hfdeq z]
    exact le_trans (norm_comp_le_of_opNorm_le_one hA _)
      (norm_fderiv_le_of_norm_sub_le hM₂ h2 z)
  · intro z w
    rw [hfdeq z, hfdeq w, ← ContinuousLinearMap.comp_sub]
    exact le_trans (norm_comp_le_of_opNorm_le_one hA _) (h3 z w)

end Work.NN.Newton.FTsharp
