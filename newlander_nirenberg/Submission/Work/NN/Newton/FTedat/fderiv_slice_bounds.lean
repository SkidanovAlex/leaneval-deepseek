import Mathlib
import Submission.Work.CR.Flat.Holder

namespace Work.NN.Newton.FTedat

open ContinuousLinearMap

/-- The coordinate projection `z ↦ z j` on `Fin n → ℂ` has operator norm at most one. -/
private lemma norm_proj_fin {n : ℕ} (j : Fin n) :
    ‖(ContinuousLinearMap.proj (R := ℝ) (φ := fun _ => ℂ) j : (Fin n → ℂ) →L[ℝ] ℂ)‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun x => by
    rw [one_mul, ContinuousLinearMap.proj_apply]; exact norm_le_pi_norm x j)

/-- The derivative of a slice `z ↦ φ (z j)` of a map `φ : ℂ → ℂ` is
`(fderiv ℝ φ (x j)).comp (proj j)`. -/
private lemma fderiv_slice {n : ℕ} {φ : ℂ → ℂ} (hφ : Differentiable ℝ φ) (j : Fin n)
    (x : Fin n → ℂ) :
    fderiv ℝ (fun z : Fin n → ℂ => φ (z j)) x
      = (fderiv ℝ φ (x j)).comp (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ => ℂ) j) := by
  rw [show (fun z : Fin n → ℂ => φ (z j)) = φ ∘ (fun z : Fin n → ℂ => z j) from rfl]
  rw [fderiv_comp x hφ.differentiableAt (by fun_prop)]
  have hfun : (fun z : Fin n → ℂ => z j)
      = ⇑(ContinuousLinearMap.proj (R := ℝ) (φ := fun _ => ℂ) j) := by
    ext z; rw [ContinuousLinearMap.proj_apply]
  rw [hfun, ContinuousLinearMap.fderiv]

lemma fderiv_slice_bounds {n : ℕ} {φ : ℂ → ℂ} (hφ : Differentiable ℝ φ)
    {M L Md : ℝ}
    (hM : ∀ ζ : ℂ, ‖fderiv ℝ φ ζ‖ ≤ M)
    (hL : ∀ ζ η : ℂ, ‖φ ζ - φ η‖ ≤ L * ‖ζ - η‖)
    (hMd : ∀ ζ η : ℂ, ‖fderiv ℝ φ ζ - fderiv ℝ φ η‖ ≤ Md * ‖ζ - η‖) :
    (∀ j : Fin n, ∀ x : Fin n → ℂ, ‖fderiv ℝ (fun z : Fin n → ℂ => φ (z j)) x‖ ≤ M) ∧
    (∀ j : Fin n, ∀ x y : Fin n → ℂ,
        ‖(fun z : Fin n → ℂ => φ (z j)) x - (fun z : Fin n → ℂ => φ (z j)) y‖ ≤ L * ‖x - y‖) ∧
    (∀ j : Fin n, ∀ x y : Fin n → ℂ,
        ‖fderiv ℝ (fun z : Fin n → ℂ => φ (z j)) x
          - fderiv ℝ (fun z : Fin n → ℂ => φ (z j)) y‖ ≤ Md * ‖x - y‖) := by
  -- the hypotheses force the three constants to be nonnegative
  have hMnn : 0 ≤ M := le_trans (norm_nonneg _) (hM 0)
  have hLnn : 0 ≤ L := le_trans (norm_nonneg _) (by simpa using hL 0 1)
  have hMdnn : 0 ≤ Md := le_trans (norm_nonneg _) (by simpa using hMd 0 1)
  refine ⟨?_, ?_, ?_⟩
  · intro j x
    rw [fderiv_slice hφ j x]
    calc ‖(fderiv ℝ φ (x j)).comp
            (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ => ℂ) j)‖
        ≤ ‖fderiv ℝ φ (x j)‖
            * ‖(ContinuousLinearMap.proj (R := ℝ) (φ := fun _ => ℂ) j : (Fin n → ℂ) →L[ℝ] ℂ)‖ :=
          opNorm_comp_le _ _
      _ ≤ M * 1 := mul_le_mul (hM (x j)) (norm_proj_fin j) (norm_nonneg _) hMnn
      _ = M := mul_one M
  · intro j x y
    show ‖φ (x j) - φ (y j)‖ ≤ L * ‖x - y‖
    calc ‖φ (x j) - φ (y j)‖
        ≤ L * ‖x j - y j‖ := hL (x j) (y j)
      _ ≤ L * ‖x - y‖ :=
          mul_le_mul_of_nonneg_left
            (by simpa [Pi.sub_apply] using norm_le_pi_norm (x - y) j) hLnn
  · intro j x y
    rw [fderiv_slice hφ j x, fderiv_slice hφ j y, ← ContinuousLinearMap.sub_comp]
    calc ‖(fderiv ℝ φ (x j) - fderiv ℝ φ (y j)).comp
            (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ => ℂ) j)‖
        ≤ ‖fderiv ℝ φ (x j) - fderiv ℝ φ (y j)‖
            * ‖(ContinuousLinearMap.proj (R := ℝ) (φ := fun _ => ℂ) j : (Fin n → ℂ) →L[ℝ] ℂ)‖ :=
          opNorm_comp_le _ _
      _ ≤ (Md * ‖x j - y j‖) * 1 :=
          mul_le_mul (hMd (x j) (y j)) (norm_proj_fin j) (norm_nonneg _)
            (mul_nonneg hMdnn (norm_nonneg _))
      _ = Md * ‖x j - y j‖ := mul_one _
      _ ≤ Md * ‖x - y‖ :=
          mul_le_mul_of_nonneg_left
            (by simpa [Pi.sub_apply] using norm_le_pi_norm (x - y) j) hMdnn

end Work.NN.Newton.FTedat
