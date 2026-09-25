import Mathlib
import Submission.Work.Hormander.Weights.Defs

namespace Work.Hormander.Weights

/-- The derivative of the complex valued function `w ↦ (φ w : ℂ)` built from a real
valued `φ` is the composition of the (real linear) inclusion `ℝ → ℂ` with the
derivative of `φ`.  Note that no differentiability of `φ` is assumed: when `φ` is
not differentiable at `z` both sides vanish. -/
lemma fderiv_ofReal_comp {n : ℕ} (φ : Cn n → ℝ) (z : Cn n) :
    fderiv ℝ (fun w : Cn n => (φ w : ℂ)) z = Complex.ofRealCLM.comp (fderiv ℝ φ z) := by
  by_cases h : DifferentiableAt ℝ φ z
  · change fderiv ℝ ((Complex.ofRealCLM : ℝ →L[ℝ] ℂ) ∘ φ) z
      = Complex.ofRealCLM.comp (fderiv ℝ φ z)
    rw [fderiv_comp]
    · rw [ContinuousLinearMap.fderiv]
    · exact Complex.ofRealCLM.differentiableAt
    · exact h
  · have h2 : ¬ DifferentiableAt ℝ (fun w : Cn n => (φ w : ℂ)) z := by
      intro hcon
      have h3 : DifferentiableAt ℝ (fun w : Cn n => Complex.reCLM ((φ w : ℂ))) z :=
        Complex.reCLM.differentiableAt.comp z hcon
      refine h ?_
      convert h3 using 1
      ext w
      simp
    rw [fderiv_zero_of_not_differentiableAt h2, fderiv_zero_of_not_differentiableAt h]
    simp

/-- For a real valued weight `φ`, the `∂`- and `∂̄`-derivatives are complex conjugates
of each other. -/
theorem star_dPhi {n : ℕ} (φ : Cn n → ℝ) (j : Fin n) (z : Cn n) :
    star (dPhi n j φ z) = dbarPhi n j φ z := by
  have hkey := fderiv_ofReal_comp (n := n) φ z
  rw [dPhi, dbarPhi, dCoord, dbarCoord, hkey]
  simp [Complex.conj_ofReal]

end Work.Hormander.Weights
