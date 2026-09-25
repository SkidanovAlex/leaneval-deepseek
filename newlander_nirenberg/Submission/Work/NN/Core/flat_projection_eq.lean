import Mathlib
import Submission.Work.NN.Core.CnPert

namespace Work.NN.Core

open scoped NNReal ENNReal Topology
open Set

/-- The function `y ↦ stdForm ψ y (Pi.single m 1)` is the coefficient `ψ m`. -/
lemma stdForm_fun_single {n : ℕ} (ψ : Fin n → (Fin n → ℂ) → ℂ) (m : Fin n) :
    (fun y : Fin n → ℂ => stdForm ψ y (Pi.single m 1)) = ψ m := by
  funext y; exact stdForm_single ψ y m

/-- The function `y ↦ stdForm ψ y (Pi.single m i)` is `-i · ψ m`. -/
lemma stdForm_fun_single_I {n : ℕ} (ψ : Fin n → (Fin n → ℂ) → ℂ) (m : Fin n) :
    (fun y : Fin n → ℂ => stdForm ψ y (Pi.single m Complex.I)) = fun y => -Complex.I * ψ m y := by
  funext y; exact stdForm_single_I ψ y m

/-- **The `(0,2)`-part of the exterior derivative of the standard `(0,1)`-form `Σ ψ_m dz̄_m`,
computed with the standard complex structure, in terms of the coefficients.**

For a coefficient family `ψ : Fin n → ℂⁿ → ℂ` and a point `z`, the flat `(0,2)`-projection
`(1/4)·(dω(e_k,e_l) + i·dω(i e_k,e_l) + i·dω(e_k,i e_l) - dω(i e_k,i e_l))` of the exterior
derivative of `ω = stdForm ψ` is the classical coefficient expression
`∂̄_k ψ_l - ∂̄_l ψ_k`. -/
theorem flat_projection_eq {n : ℕ} {ψ : Fin n → (Fin n → ℂ) → ℂ} (hψ : ∀ m, ContDiff ℝ 1 (ψ m))
    (z : Fin n → ℂ) (k l : Fin n) :
    (1 / 4 : ℂ) *
        ( (fderiv ℝ (fun y => Work.NN.Core.stdForm ψ y (Pi.single l 1)) z (Pi.single k 1)
            - fderiv ℝ (fun y => Work.NN.Core.stdForm ψ y (Pi.single k 1)) z (Pi.single l 1))
        + Complex.I * (fderiv ℝ (fun y => Work.NN.Core.stdForm ψ y (Pi.single l 1)) z (Pi.single k Complex.I)
            - fderiv ℝ (fun y => Work.NN.Core.stdForm ψ y (Pi.single k Complex.I)) z (Pi.single l 1))
        + Complex.I * (fderiv ℝ (fun y => Work.NN.Core.stdForm ψ y (Pi.single l Complex.I)) z (Pi.single k 1)
            - fderiv ℝ (fun y => Work.NN.Core.stdForm ψ y (Pi.single k 1)) z (Pi.single l Complex.I))
        - (fderiv ℝ (fun y => Work.NN.Core.stdForm ψ y (Pi.single l Complex.I)) z (Pi.single k Complex.I)
            - fderiv ℝ (fun y => Work.NN.Core.stdForm ψ y (Pi.single k Complex.I)) z (Pi.single l Complex.I)) )
      = Work.CR.Flat.dbarCoord k (ψ l) z - Work.CR.Flat.dbarCoord l (ψ k) z := by
  have hd : ∀ m, DifferentiableAt ℝ (ψ m) z :=
    fun m => ((hψ m).differentiable_one).differentiableAt
  have hLl : fderiv ℝ (fun y => -Complex.I * ψ l y) z = (-Complex.I) • fderiv ℝ (ψ l) z :=
    fderiv_const_mul (hd l) (-Complex.I)
  have hLk : fderiv ℝ (fun y => -Complex.I * ψ k y) z = (-Complex.I) • fderiv ℝ (ψ k) z :=
    fderiv_const_mul (hd k) (-Complex.I)
  rw [stdForm_fun_single ψ l, stdForm_fun_single ψ k, stdForm_fun_single_I ψ l,
    stdForm_fun_single_I ψ k, hLl, hLk]
  rw [Work.CR.Flat.dbarCoord, Work.CR.Flat.dbarCoord]
  simp only [smul_apply, smul_eq_mul]
  ring_nf
  rw [Complex.I_sq]
  ring

end Work.NN.Core
