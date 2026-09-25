import Mathlib
import Submission.Work.Hormander.Weights.Rint
import Submission.Work.Hormander.Weights.rpair0_dbar_left

namespace Work.Hormander.Weights

open MeasureTheory Set
open scoped Topology ContDiff

/-- The elementary complex identity behind `dbarPhi_eq_star_dPhi`. -/
private lemma star_half_mul (A B : ℝ) :
    star ((1/2 : ℂ) * ((A:ℂ) - Complex.I * (B:ℂ)))
      = (1/2 : ℂ) * ((A:ℂ) + Complex.I * (B:ℂ)) := by
  rw [show (1/2:ℂ) = ((1/2:ℝ):ℂ) from by norm_num]
  simp only [Complex.star_def, map_mul, map_sub, Complex.conj_ofReal, Complex.conj_I]
  ring

/-- For a real weight `φ` the `(0,1)`- and `(1,0)`-derivatives are conjugate:
`∂̄_j φ = conj (∂_j φ)`. -/
lemma dbarPhi_eq_star_dPhi {n : ℕ} (φ : Cn n → ℝ) (j : Fin n) (z : Cn n)
    (hφ : DifferentiableAt ℝ φ z) : dbarPhi n j φ z = star (dPhi n j φ z) := by
  have hF : fderiv ℝ (fun w : Cn n => ((φ w : ℝ) : ℂ)) z
      = (Complex.ofRealCLM : ℝ →L[ℝ] ℂ).comp (fderiv ℝ φ z) := by
    have h1 : (fun w : Cn n => ((φ w : ℝ) : ℂ))
        = (Complex.ofRealCLM : ℝ →L[ℝ] ℂ) ∘ φ := rfl
    rw [h1, fderiv_comp z (ContinuousLinearMap.differentiableAt _) hφ,
      ContinuousLinearMap.fderiv]
  simp only [dbarPhi, dPhi, dbarCoord, dCoord, hF, ContinuousLinearMap.comp_apply,
    Complex.ofRealCLM_apply]
  rw [star_half_mul]

theorem rpair0_dbar_right {n : ℕ} (φ : Cn n → ℝ) (hφ : ContDiff ℝ 1 φ) (j : Fin n)
    (X Y : Cn n → ℂ) (hX : ContDiff ℝ 1 X) (hY : ContDiff ℝ 1 Y)
    (hsX : HasCompactSupport X) (hsY : HasCompactSupport Y) :
    rpair0 φ X (fun z => dbarCoord n j Y z)
      = -rpair0 φ (fun z => dCoord n j X z) Y
        + rpair0 φ (fun z => X z * dPhi n j φ z) Y := by
  -- In the weight term the Leibniz rule produces `∂̄_j φ`; after taking real
  -- parts this equals the `∂_j φ` term, because `∂̄_j φ = conj (∂_j φ)` and
  -- `Re (a * conj s) = Re (conj a * s)`.
  have hweight : rpair0 φ (fun z => Y z * dbarPhi n j φ z) X
      = rpair0 φ (fun z => X z * dPhi n j φ z) Y := by
    unfold rpair0 rint
    apply integral_congr_ae
    filter_upwards with z
    have hpt : ((Y z * dbarPhi n j φ z) * star (X z)).re
        = ((X z * dPhi n j φ z) * star (Y z)).re := by
      rw [dbarPhi_eq_star_dPhi φ j z
        ((hφ.differentiable (by norm_num)).differentiableAt)]
      have key : (Y z * star (dPhi n j φ z)) * star (X z)
          = star ((X z * dPhi n j φ z) * star (Y z)) := by
        simp only [star_mul, star_star]; ring
      rw [key]
      rw [Complex.star_def, Complex.conj_re]
    rw [hpt]
  -- `rpair0` is symmetric, so the `∂̄`-differentiation can be moved from the
  -- second argument to the first; the rest is `rpair0_dbar_left`.
  rw [rpair0_comm (φ := φ) X (fun z => dbarCoord n j Y z)]
  rw [rpair0_dbar_left φ hφ j Y X hY hX hsY hsX]
  rw [rpair0_comm (φ := φ) Y (fun z => dCoord n j X z)]
  rw [hweight]

end Work.Hormander.Weights
