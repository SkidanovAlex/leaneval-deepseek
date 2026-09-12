import Mathlib
import Submission.RS
import Submission.Sec3Defs

/-! Section 3 analysis objects (paper arXiv:1907.09464v1 §3):

    T   := 2^(t+10)
    α(x):= 2^-(t+1)/2 · P_t(e^{ix/T})
    β(x):= 2^-(t+1)/2 · Q_t(e^{ix/T})
    H(x):= e^{ix} α(x) + e^{2ix} β(x)

  These are ℂ-valued functions of a real variable `x`.  The cosine polynomial of
  Section 3 satisfies `c(θ) = 2^((t+1)/2) · Re H(2Tθ)`.
  We realise the scalar `2^(-(t+1)/2)` as `1 / sqrt(2^(t+1))` so that
  `scale^2 · 2^(t+1) = 1` is immediate from `Real.sq_sqrt`. -/

noncomputable section
open scoped Polynomial BigOperators
open Polynomial Complex

namespace Submission
namespace Sec3H

/-- `T = 2^(t+10)`. -/
def T (t : ℕ) : ℕ := 2 ^ (t + 10)

/-- The scalar `2^(-(t+1)/2)`, realised as `1 / sqrt(2^(t+1))`. -/
def scale (t : ℕ) : ℝ := (Real.sqrt (2 ^ (t + 1)))⁻¹

/-- `α(x) = 2^(-(t+1)/2) · P_t(e^{ix/T})`. -/
def alpha (t : ℕ) (x : ℝ) : ℂ :=
  (scale t : ℂ) * (RudinShapiro.P t).eval (Sec3.eθ (x / (T t : ℝ)))

/-- `β(x) = 2^(-(t+1)/2) · Q_t(e^{ix/T})`. -/
def beta (t : ℕ) (x : ℝ) : ℂ :=
  (scale t : ℂ) * (RudinShapiro.Q t).eval (Sec3.eθ (x / (T t : ℝ)))

/-- `H(x) = e^{ix} α(x) + e^{2ix} β(x)`. -/
def H (t : ℕ) (x : ℝ) : ℂ :=
  Sec3.eθ x * alpha t x + Sec3.eθ (2 * x) * beta t x

/-- Norm of an embedded real equals its absolute value. -/
lemma norm_of_real (r : ℝ) : ‖(r : ℂ)‖ = |r| := by
  have hs : ‖(r : ℂ)‖ ^ 2 = |r| ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_ofReal]
    ring_nf
    rw [sq_abs]
  have hnn : 0 ≤ ‖(r : ℂ)‖ := norm_nonneg _
  have hnn2 : 0 ≤ |r| := abs_nonneg r
  calc
    ‖(r : ℂ)‖ = |‖(r : ℂ)‖| := (abs_of_nonneg hnn).symm
    _ = |(|r|)| := (sq_eq_sq_iff_abs_eq_abs ‖(r : ℂ)‖ |r|).mp hs
    _ = |r| := abs_of_nonneg hnn2

lemma scale_nonneg (t : ℕ) : 0 ≤ scale t := by
  unfold scale
  exact inv_nonneg.mpr (Real.sqrt_nonneg _)

lemma scale_sq (t : ℕ) : (scale t) ^ 2 * (2 ^ (t + 1) : ℝ) = 1 := by
  unfold scale
  have hpos : 0 < (2 ^ (t + 1) : ℝ) := by positivity
  rw [inv_pow]
  have hs : (Real.sqrt (2 ^ (t + 1) : ℝ)) ^ 2 = (2 ^ (t + 1) : ℝ) := Real.sq_sqrt hpos.le
  rw [hs]
  field_simp [hpos.ne']

/-- Multiplication by the nonneg real `scale` factors out of the norm. -/
lemma norm_scale_mul (t : ℕ) (w : ℂ) : ‖(scale t : ℂ) * w‖ = scale t * ‖w‖ := by
  rw [norm_mul, norm_of_real, abs_of_nonneg (scale_nonneg t)]

/-- `‖(scale : ℂ) * w‖^2 = scale^2 · ‖w‖^2`. -/
lemma norm_scale_mul_sq (t : ℕ) (w : ℂ) : ‖(scale t : ℂ) * w‖ ^ 2 = (scale t) ^ 2 * ‖w‖ ^ 2 := by
  rw [norm_scale_mul]
  ring

/-- `α(x)` and `β(x)` have the modulus-one relation `‖α(x)‖^2 + ‖β(x)‖^2 = 1`. -/
lemma norm_sq_alpha_add_beta (t : ℕ) (x : ℝ) :
    ‖alpha t x‖ ^ 2 + ‖beta t x‖ ^ 2 = 1 := by
  let z : ℂ := Sec3.eθ (x / (T t : ℝ))
  have hsum := RudinShapiro.normSq_eval_add t z (Sec3.norm_eθ (x / (T t : ℝ)))
  have hn : ∀ w : ℂ, Complex.normSq w = ‖w‖ ^ 2 := Complex.normSq_eq_norm_sq
  unfold alpha beta
  rw [norm_scale_mul_sq, norm_scale_mul_sq]
  change (scale t) ^ 2 * ‖(RudinShapiro.P t).eval z‖ ^ 2 +
      (scale t) ^ 2 * ‖(RudinShapiro.Q t).eval z‖ ^ 2 = 1
  rw [← hn ((RudinShapiro.P t).eval z), ← hn ((RudinShapiro.Q t).eval z)]
  have hsum' : Complex.normSq ((RudinShapiro.P t).eval z) +
      Complex.normSq ((RudinShapiro.Q t).eval z) = (2 ^ (t + 1) : ℝ) := by
    simpa using hsum
  calc
    (scale t) ^ 2 * Complex.normSq ((RudinShapiro.P t).eval z) +
        (scale t) ^ 2 * Complex.normSq ((RudinShapiro.Q t).eval z)
        = (scale t) ^ 2 * (Complex.normSq ((RudinShapiro.P t).eval z) +
            Complex.normSq ((RudinShapiro.Q t).eval z)) := by ring
    _ = (scale t) ^ 2 * (2 ^ (t + 1) : ℝ) := by rw [hsum']
    _ = 1 := by
        simpa [mul_comm, mul_left_comm, mul_assoc] using scale_sq t

/-- `‖α(x)‖ ≤ 1`. -/
lemma norm_alpha_le (t : ℕ) (x : ℝ) : ‖alpha t x‖ ≤ 1 := by
  have h := norm_sq_alpha_add_beta t x
  have hsq : ‖alpha t x‖ ^ 2 ≤ 1 ^ 2 := by
    nlinarith [sq_nonneg (‖beta t x‖)]
  have habs := (sq_le_sq.mp hsq)
  have hnn : 0 ≤ ‖alpha t x‖ := norm_nonneg _
  simpa [abs_of_nonneg hnn] using habs

/-- `‖β(x)‖ ≤ 1`. -/
lemma norm_beta_le (t : ℕ) (x : ℝ) : ‖beta t x‖ ≤ 1 := by
  have h := norm_sq_alpha_add_beta t x
  have hsq : ‖beta t x‖ ^ 2 ≤ 1 ^ 2 := by
    nlinarith [sq_nonneg (‖alpha t x‖)]
  have habs := (sq_le_sq.mp hsq)
  have hnn : 0 ≤ ‖beta t x‖ := norm_nonneg _
  simpa [abs_of_nonneg hnn] using habs

end Sec3H
end Submission
