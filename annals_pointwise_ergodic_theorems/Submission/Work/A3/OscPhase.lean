import Mathlib
import Submission.Work.A3.Circle

/-!
# The oscillatory phase `e^{-2πi f}`

`oscPhase f x = exp(-(2π i f x))` is the phase whose integral is `singInt`:
`singInt Q N β = ∫ t in 0..N, oscPhase (fun t => β * (Qreal Q).eval t) t`.

It is the conjugate of the phase `Submission.SdtOscB.ephase (-f)` of the van der Corput
second-derivative-test development in `Submission.Commons.Analysis.ExponentialSums`.

This file collects the elementary facts about it that the singular-integral bound needs.
-/

set_option autoImplicit false

namespace Work.A3

open Polynomial MeasureTheory

noncomputable section

/-- The oscillatory exponential `e^{-2πi f(x)} = exp(-(2πi f(x)))`. -/
def oscPhase (f : ℝ → ℝ) (x : ℝ) : ℂ := Complex.exp (-(2 * Real.pi * Complex.I * (f x : ℂ)))

/-- `oscPhase f` has unit modulus. -/
lemma oscPhase_norm (f : ℝ → ℝ) (x : ℝ) : ‖oscPhase f x‖ = 1 := by
  have h : -(2 * Real.pi * Complex.I * (f x : ℂ))
      = ((-(2 * Real.pi * f x) : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [oscPhase, h, Complex.norm_exp_ofReal_mul_I]

/-- `oscPhase f` is bounded by `1`. -/
lemma oscPhase_norm_le (f : ℝ → ℝ) (x : ℝ) : ‖oscPhase f x‖ ≤ 1 := oscPhase_norm f x ▸ le_rfl

/-- `oscPhase` of a continuous phase is continuous. -/
lemma continuous_oscPhase {f : ℝ → ℝ} (hf : Continuous f) : Continuous (oscPhase f) := by
  have h : oscPhase f
      = fun x => Complex.exp (((((-2 * Real.pi) : ℝ) : ℂ) * Complex.I) * (f x : ℂ)) := by
    funext x
    rw [oscPhase]; congr 1; push_cast; ring
  rw [h]
  exact Complex.continuous_exp.comp (((continuous_const.mul Complex.continuous_ofReal).comp hf))

/-- `oscPhase (-f) = conj ∘ oscPhase f`. -/
lemma oscPhase_neg (f : ℝ → ℝ) (x : ℝ) :
    oscPhase (-f) x = (starRingEnd ℂ) (oscPhase f x) := by
  rw [← Complex.inv_eq_conj (oscPhase_norm f x), oscPhase, oscPhase]
  have h : -(2 * Real.pi * Complex.I * ((-f) x : ℂ))
      = -(-(2 * Real.pi * Complex.I * (f x : ℂ))) := by
    simp only [Pi.neg_apply]; push_cast; ring
  rw [h, Complex.exp_neg]

/-- Function-level form of `oscPhase_neg`. -/
lemma oscPhase_neg_fun (f : ℝ → ℝ) :
    oscPhase (-f) = fun x => (starRingEnd ℂ) (oscPhase f x) := by
  funext x
  exact oscPhase_neg f x

/-- Complex conjugation commutes with the interval integral. -/
lemma intervalIntegral_star (g : ℝ → ℂ) (a b : ℝ) (hg : IntervalIntegrable g volume a b) :
    ∫ x in a..b, (starRingEnd ℂ) (g x) = (starRingEnd ℂ) (∫ x in a..b, g x) := by
  have h := ContinuousLinearMap.intervalIntegral_comp_comm (μ := volume) (a := a) (b := b)
    Complex.conjCLE.toContinuousLinearMap (f := g) hg
  have hcoe : Complex.conjCLE.toContinuousLinearMap = fun z : ℂ => (starRingEnd ℂ) z := by
    funext z; exact Complex.conjCLE_apply z
  rw [hcoe] at h
  exact h

/-- Negating the phase does not change the norm of the oscillatory integral. -/
lemma norm_intervalIntegral_oscPhase_neg (f : ℝ → ℝ) {a b : ℝ} (hab : a ≤ b)
    (hf : Continuous f) :
    ‖∫ x in a..b, oscPhase (-f) x‖ = ‖∫ x in a..b, oscPhase f x‖ := by
  have h : (∫ x in a..b, oscPhase (-f) x) = (starRingEnd ℂ) (∫ x in a..b, oscPhase f x) := by
    rw [← intervalIntegral_star (fun x => oscPhase f x) a b
      ((continuous_oscPhase hf).intervalIntegrable a b)]
    exact intervalIntegral.integral_congr fun x _ => oscPhase_neg f x
  rw [h, starRingEnd_apply, norm_star]

/-- `singInt` is the integral of `oscPhase` of the polynomial phase `t ↦ β Q(t)`. -/
lemma singInt_eq_integral_oscPhase (Q : Polynomial ℤ) (N : ℕ) (β : ℝ) :
    singInt Q N β = ∫ t in (0 : ℝ)..(N : ℝ), oscPhase (fun t => β * (Qreal Q).eval t) t := by
  rw [singInt]
  refine intervalIntegral.integral_congr fun t _ => ?_
  rw [oscPhase]
  congr 1
  push_cast
  ring

/-- Polynomials are smooth. -/
lemma contDiff_poly_eval (P : Polynomial ℝ) (n : WithTop ℕ∞) :
    ContDiff ℝ n (fun t : ℝ => P.eval t) := by
  induction P using Polynomial.induction_on' with
  | add f g fc gc => simpa using fc.add gc
  | monomial k a => simpa using contDiff_const.mul (contDiff_id.pow k)

/-- Polynomials are continuous on any set. -/
lemma continuousOn_poly_eval (P : Polynomial ℝ) (s : Set ℝ) :
    ContinuousOn (fun t : ℝ => P.eval t) s :=
  (Polynomial.continuous P).continuousOn

/-- Polynomials are `C²` on any interval. -/
lemma contDiffOn_poly_eval (P : Polynomial ℝ) {a b : ℝ} :
    ContDiffOn ℝ 2 (fun t : ℝ => P.eval t) (Set.Icc a b) :=
  (contDiff_poly_eval P 2).contDiffOn

/-- The derivative of a polynomial phase. -/
lemma deriv_poly_eval (P : Polynomial ℝ) :
    deriv (fun t : ℝ => P.eval t) = fun t => P.derivative.eval t := by
  funext t
  exact (Polynomial.hasDerivAt P t).deriv

/-- The second derivative of a polynomial phase. -/
lemma deriv_deriv_poly_eval (P : Polynomial ℝ) :
    deriv (deriv (fun t : ℝ => P.eval t)) = fun t => P.derivative.derivative.eval t := by
  rw [deriv_poly_eval]
  exact deriv_poly_eval P.derivative

end

end Work.A3
