/-
Copyright: none.  Part of the `Newlander-Nirenberg` formalisation project.

# Regularity of the weighted `∂`-operator on weights

For a `C²` real weight `φ : ℂⁿ → ℝ`, the function `z ↦ ∂_j φ(z)` is `C¹`.  This is
the regularity assertion needed so that expressions built out of the weight (for
instance `∂̄*_φ f = -Σ_j (∂_j f_j - f_j ∂_j φ)`) are as smooth as their form
coefficients.

The proof is the standard one for a first derivative of a `C²` function: the map
`(z, v) ↦ dφ_z(v)` is `C¹` (`ContDiff.contDiff_fderiv_apply`), and `∂_j φ` is a
fixed linear combination of its values at the two fixed vectors `e_j`, `i e_j`.
-/

import Mathlib
import Submission.Work.Hormander.Weights.Basic

noncomputable section

open scoped Topology ContDiff

namespace Work.Hormander.Weights

theorem contDiff_dPhi {n : ℕ} (j : Fin n) {φ : Cn n → ℝ} (hφ : ContDiff ℝ 2 φ) :
    ContDiff ℝ 1 (fun z => dPhi n j φ z) := by
  -- `z ↦ dφ_z(v)` is `C¹` for each fixed vector `v`
  have hderiv (v : Cn n) : ContDiff ℝ 1 (fun z : Cn n => fderiv ℝ φ z v) := by
    have h := hφ.contDiff_fderiv_apply (m := 1) (by norm_num)
    have hg : ContDiff ℝ 1 (fun z : Cn n => (z, v)) := by fun_prop
    simpa [Function.comp_def] using h.comp hg
  -- the two real partial derivatives, pushed into `ℂ`
  have hcE : ContDiff ℝ 1 (fun z : Cn n => ((fderiv ℝ φ z (evec n j) : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (hderiv (evec n j))
  have hcI : ContDiff ℝ 1 (fun z : Cn n => ((fderiv ℝ φ z (ivec n j) : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (hderiv (ivec n j))
  have hmain : ContDiff ℝ 1 fun z : Cn n =>
      (1 / 2 : ℂ) * (((fderiv ℝ φ z (evec n j) : ℝ) : ℂ)
        - Complex.I * ((fderiv ℝ φ z (ivec n j) : ℝ) : ℂ)) := by
    fun_prop
  -- identify `∂_j φ` with that combination of the two partial derivatives
  have key : (fun z => dPhi n j φ z) = (fun z : Cn n =>
      (1 / 2 : ℂ) * (((fderiv ℝ φ z (evec n j) : ℝ) : ℂ)
        - Complex.I * ((fderiv ℝ φ z (ivec n j) : ℝ) : ℂ))) := by
    funext z
    have hdiff : DifferentiableAt ℝ φ z := (hφ.differentiable (by norm_num)) z
    have hfderiv : fderiv ℝ (fun w : Cn n => (φ w : ℂ)) z
        = Complex.ofRealCLM.comp (fderiv ℝ φ z) := by
      have h := fderiv_comp (𝕜 := ℝ) z (g := (Complex.ofRealCLM : ℝ → ℂ)) (f := φ)
        Complex.ofRealCLM.differentiableAt hdiff
      rw [ContinuousLinearMap.fderiv] at h
      simpa [Function.comp_def] using h
    simp only [dPhi, dCoord, hfderiv, ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply]
  rw [key]
  exact hmain

end Work.Hormander.Weights
