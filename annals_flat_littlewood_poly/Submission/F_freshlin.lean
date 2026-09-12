import Mathlib
import Submission.F_gauss

/-!
Lintegral (ENNReal) version of the fresh-step bound (child task).
-/

open scoped BigOperators RealInnerProductSpace
open MeasureTheory ProbabilityTheory

noncomputable section

namespace Submission.Discrepancy

/-- The integrand of the Gaussian MGF is integrable. -/
lemma integrable_mgf_exp (n : ℕ) (a : Vec n) (t : ℝ) :
    Integrable (fun g : Vec n => Real.exp (t * vin g a)) (stdGaussian (Vec n)) := by
  by_contra h
  have h0 : (∫ g : Vec n, Real.exp (t * vin g a) ∂(stdGaussian (Vec n))) = 0 :=
    integral_undef h
  have hpos : 0 < (∫ g : Vec n, Real.exp (t * vin g a) ∂(stdGaussian (Vec n))) := by
    rw [gauss_mgf]
    positivity
  linarith

/-- Lintegral version of the Gaussian MGF:
∫⁻ over g of ofReal (exp (t * vin g a)) = ofReal (exp (t^2 ‖a‖^2 / 2)). -/
lemma gauss_mgf_lin (n : ℕ) (a : Vec n) (t : ℝ) :
    (∫⁻ g : Vec n, ENNReal.ofReal (Real.exp (t * vin g a)) ∂(stdGaussian (Vec n))) =
      ENNReal.ofReal (Real.exp (t ^ 2 * ‖a‖ ^ 2 / 2)) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_mgf_exp n a t)
    (ae_of_all (stdGaussian (Vec n)) (fun g : Vec n => (Real.exp_pos _).le))]
  rw [gauss_mgf]

/-- Comparison of the arguments of the exponentials in the fresh-step bound. -/
lemma fresh_lin_arg_le {n : ℕ} {lam γ : ℝ} {p w : Vec n} (hp : ‖p‖ ≤ ‖w‖) :
    (lam * γ) ^ 2 * ‖p‖ ^ 2 / 2 ≤ lam ^ 2 * γ ^ 2 * ‖w‖ ^ 2 / 2 := by
  have hp2 : ‖p‖ ^ 2 ≤ ‖w‖ ^ 2 := by
    simpa [pow_two] using mul_self_le_mul_self (norm_nonneg p) hp
  have hmul : (lam * γ) ^ 2 * ‖p‖ ^ 2 ≤ (lam * γ) ^ 2 * ‖w‖ ^ 2 :=
    mul_le_mul_of_nonneg_left hp2 (sq_nonneg (lam * γ))
  have hle2 : (lam * γ) ^ 2 * ‖p‖ ^ 2 / 2 ≤ (lam * γ) ^ 2 * ‖w‖ ^ 2 / 2 :=
    div_le_div_of_nonneg_right hmul (by positivity)
  calc
    (lam * γ) ^ 2 * ‖p‖ ^ 2 / 2 ≤ (lam * γ) ^ 2 * ‖w‖ ^ 2 / 2 := hle2
    _ = lam ^ 2 * γ ^ 2 * ‖w‖ ^ 2 / 2 := by ring

/-- Fresh-step bound in lintegral form:
∫⁻ over g of ofReal(exp (lam * (γ * vin (walkProj v A B g) w))) ≤ ofReal(exp(lam^2 γ^2 ‖w‖^2/2)). -/
lemma fresh_lin {n : ℕ} {ι : Type*} [Fintype ι] (v : ι → Vec n) (A : Finset (Fin n))
    (B : Finset ι) (lam γ : ℝ) (w : Vec n) :
    (∫⁻ g : Vec n, ENNReal.ofReal (Real.exp (lam * (γ * vin (walkProj v A B g) w)))
      ∂(stdGaussian (Vec n))) ≤
      ENNReal.ofReal (Real.exp (lam ^ 2 * γ ^ 2 * ‖w‖ ^ 2 / 2)) := by
  let p := walkProj v A B w
  have hfull : (fun g : Vec n =>
      ENNReal.ofReal (Real.exp (lam * (γ * vin (walkProj v A B g) w)))) =
      (fun g : Vec n => ENNReal.ofReal (Real.exp ((lam * γ) * vin g p))) := by
    funext g
    congr 1
    rw [proj_adjoint v A B g w]
    simp [p, mul_assoc]
  calc
    (∫⁻ g : Vec n, ENNReal.ofReal (Real.exp (lam * (γ * vin (walkProj v A B g) w)))
        ∂(stdGaussian (Vec n)))
        = (∫⁻ g : Vec n, ENNReal.ofReal (Real.exp ((lam * γ) * vin g p))
            ∂(stdGaussian (Vec n))) := by rw [hfull]
    _ = ENNReal.ofReal (Real.exp ((lam * γ) ^ 2 * ‖p‖ ^ 2 / 2)) := gauss_mgf_lin n p (lam * γ)
    _ ≤ ENNReal.ofReal (Real.exp (lam ^ 2 * γ ^ 2 * ‖w‖ ^ 2 / 2)) := by
        exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr
          (fresh_lin_arg_le (p := p) (w := w) (lam := lam) (γ := γ)
            (proj_norm_le v A B w)))

end Discrepancy

end Submission
