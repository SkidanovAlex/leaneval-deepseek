import Mathlib
import Submission.Work.RPV.Defs

set_option linter.unusedVariables false

noncomputable section

namespace Work.RPV

open Complex

/-- Reduced `(q₁,p₁)` coordinate `p₁ + i q₁` of a point of `PS`. -/
def red (x : PS) : ℂ := (x.2.1 : ℂ) + (x.1.1 : ℂ) * Complex.I

lemma red_chordPS (z w : ℂ) (a : ℝ) :
    red (chordPS z w a) = Complex.exp (-(a : ℂ) * I) * ((z + w) / (Real.sqrt 2 : ℂ)) := by
  simp only [red, chordPS]
  rw [Complex.re_add_im]

lemma red_Tk (k : ℤ) (x : PS) : red (Tk k x) = red x := by
  simp only [red, Tk]

lemma exp_neg_mul_I (θ : ℝ) :
    Complex.exp (-(θ : ℂ) * I) = (Real.cos θ : ℂ) - (Real.sin θ : ℂ) * I := by
  rw [show -(θ : ℂ) * I = ((-θ : ℝ) : ℂ) * I by push_cast; ring]
  rw [Complex.exp_ofReal_mul_I]
  simp only [Complex.ofReal_neg, Complex.ofReal_cos, Complex.ofReal_sin, Real.cos_neg,
    Real.sin_neg]
  ring

lemma red_tau (θ : ℝ) (x : PS) :
    red (tau θ x) = red x * Complex.exp (-(θ : ℂ) * I) := by
  rw [exp_neg_mul_I]
  simp only [red, tau]
  apply Complex.ext
  · simp only [Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.mul_re,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring
  · simp only [Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.mul_re,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring

lemma neg_mul_I_add (s t : ℝ) :
    -(s : ℂ) * I + -(t : ℂ) * I = -((s + t : ℝ) : ℂ) * I := by
  push_cast; ring

/-- `e^{-is} X e^{-it} = e^{-i(s+t)} X`. -/
lemma exp_mul_sandwich (s t : ℝ) (X : ℂ) :
    Complex.exp (-(s : ℂ) * I) * X * Complex.exp (-(t : ℂ) * I)
      = Complex.exp (-((s + t : ℝ) : ℂ) * I) * X := by
  have h := neg_mul_I_add s t
  calc Complex.exp (-(s : ℂ) * I) * X * Complex.exp (-(t : ℂ) * I)
      = Complex.exp (-(s : ℂ) * I) * (Complex.exp (-(t : ℂ) * I) * X) := by ring
    _ = (Complex.exp (-(s : ℂ) * I) * Complex.exp (-(t : ℂ) * I)) * X := by ring
    _ = Complex.exp (-(s : ℂ) * I + -(t : ℂ) * I) * X := by rw [Complex.exp_add]
    _ = Complex.exp (-((s + t : ℝ) : ℂ) * I) * X := by rw [h]

/-- `‖p-q‖² = 2‖p‖² + 2‖q‖² - ‖p+q‖²` (parallelogram). -/
lemma norm_sub_sq_identity (p q : ℂ) :
    ‖p - q‖ ^ 2 = 2 * ‖p‖ ^ 2 + 2 * ‖q‖ ^ 2 - ‖p + q‖ ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq (p - q), ← Complex.normSq_eq_norm_sq p,
    ← Complex.normSq_eq_norm_sq q, ← Complex.normSq_eq_norm_sq (p + q),
    Complex.normSq_sub, Complex.normSq_add]
  ring

theorem rect_of_tau_chord {z w z' w' : ℂ} {a a' θ : ℝ} (hzw : z ≠ w) (hz'w' : z' ≠ w')
    (ha : z - w = (‖z - w‖ : ℂ) * Complex.exp (a * I))
    (ha' : z' - w' = (‖z' - w'‖ : ℂ) * Complex.exp (a' * I)) (k : ℤ)
    (h : Work.RPV.tau θ (Work.RPV.chordPS z w a) = Work.RPV.Tk k (Work.RPV.chordPS z' w' a')) :
    z + w = z' + w' ∧ z' - w' = Complex.exp (θ * I) * (z - w) := by
  have hsqrt : (Real.sqrt 2 : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]
    exact ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  -- angle relation
  have hq : a + θ = a' + 2 * Real.pi * k := by
    have h1 := congrArg (fun x : PS => x.1.2) h
    simpa [tau, Tk, chordPS] using h1
  -- second-coordinate relation
  have hp : ‖z‖ ^ 2 + ‖w‖ ^ 2 = ‖z'‖ ^ 2 + ‖w'‖ ^ 2 := by
    have h1 := congrArg (fun x : PS => x.2.2) h
    simp only [tau, Tk, chordPS] at h1
    linarith
  -- reduced-coordinate relation
  have hred : red (chordPS z w a) * Complex.exp (-(θ : ℂ) * I) = red (chordPS z' w' a') := by
    have h1 := congrArg red h
    rw [red_tau, red_Tk] at h1
    exact h1
  have hE : Complex.exp (-(a : ℂ) * I) * ((z + w) / (Real.sqrt 2 : ℂ)) *
        Complex.exp (-(θ : ℂ) * I)
      = Complex.exp (-(a' : ℂ) * I) * ((z' + w') / (Real.sqrt 2 : ℂ)) := by
    have h2 := hred
    rw [red_chordPS z w a, red_chordPS z' w' a'] at h2
    exact h2
  -- `e^{-i(a+θ)} = e^{-ia'}` since `a + θ = a' + 2πk`
  have hOne : Complex.exp (-((a + θ : ℝ) : ℂ) * I) = Complex.exp (-(a' : ℂ) * I) := by
    rw [Complex.exp_eq_exp_iff_exists_int]
    refine ⟨-k, ?_⟩
    have hk : (a' : ℝ) = a + θ - 2 * Real.pi * k := by linarith
    rw [hk]; push_cast; ring
  have hXY : (z + w) / (Real.sqrt 2 : ℂ) = (z' + w') / (Real.sqrt 2 : ℂ) := by
    rw [exp_mul_sandwich a θ, hOne] at hE
    exact mul_left_cancel₀ (Complex.exp_ne_zero _) hE
  have hzw' : z + w = z' + w' := by
    have h2 := congrArg (fun t : ℂ => t * (Real.sqrt 2 : ℂ)) hXY
    rw [div_mul_cancel₀ _ hsqrt, div_mul_cancel₀ _ hsqrt] at h2
    exact h2
  -- the difference vectors have the same modulus
  have hnorm : ‖z - w‖ = ‖z' - w'‖ := by
    have h1 : ‖z - w‖ ^ 2 = ‖z' - w'‖ ^ 2 := by
      rw [norm_sub_sq_identity z w, norm_sub_sq_identity z' w', hzw']
      linarith
    calc ‖z - w‖ = Real.sqrt (‖z - w‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
      _ = Real.sqrt (‖z' - w'‖ ^ 2) := by rw [h1]
      _ = ‖z' - w'‖ := Real.sqrt_sq (norm_nonneg _)
  -- `e^{ia'} = e^{iθ} e^{ia}`
  have hexp2 : Complex.exp ((a' : ℂ) * I) = Complex.exp ((θ : ℂ) * I + (a : ℂ) * I) := by
    rw [Complex.exp_eq_exp_iff_exists_int]
    refine ⟨-k, ?_⟩
    have hk : (a' : ℝ) = θ + a - 2 * Real.pi * k := by linarith
    rw [hk]; push_cast; ring
  refine ⟨hzw', ?_⟩
  rw [ha', ha, hnorm, hexp2, Complex.exp_add]
  ring

end Work.RPV
