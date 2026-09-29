import Mathlib
import Submission.Work.Fx.FxTdivReal

namespace Work.Resample

/-- The norm of the complex embedding of a real number is its absolute value. -/
private lemma norm_ofReal_eq_abs (x : ℝ) : ‖((x : ℝ) : ℂ)‖ = |x| := by
  rw [show ‖((x:ℝ):ℂ)‖ = Real.sqrt (‖((x:ℝ):ℂ)‖^2) from (Real.sqrt_sq (norm_nonneg _)).symm]
  rw [Complex.sq_norm, Complex.normSq_ofReal, ← sq, Real.sqrt_sq_eq_abs]

/-- Triangle inequality for a complex number with real and imaginary parts `a`, `b`. -/
private lemma norm_ofReal_add_I_mul_le (a b : ℝ) :
    ‖(a : ℂ) + (b : ℂ) * Complex.I‖ ≤ |a| + |b| := by
  calc ‖(a : ℂ) + (b : ℂ) * Complex.I‖
      ≤ ‖(a : ℂ)‖ + ‖(b : ℂ) * Complex.I‖ := norm_add_le _ _
    _ = |a| + |b| := by
        rw [norm_mul, Complex.norm_I, mul_one, norm_ofReal_eq_abs, norm_ofReal_eq_abs]

/-- The `tdiv` rounding error of the pair `(W*x₁, W*x₂)`: rounding each coordinate to
`2^p`-scaled integers and back reconstructs `W x / 2^p` up to `√2 < 2` in the complex norm. -/
theorem buDscTdiv (W : ℤ) (X : ℤ × ℤ) (p : ℕ) :
    ‖(((Int.tdiv (W * X.1) ((2 : ℤ) ^ p) : ℤ) : ℂ)
       + ((Int.tdiv (W * X.2) ((2 : ℤ) ^ p) : ℤ) : ℂ) * Complex.I)
      - (W : ℂ) * ((X.1 : ℂ) + (X.2 : ℂ) * Complex.I) / ((2 : ℂ) ^ p)‖ ≤ 2 := by
  have hqpos : 0 < (2:ℤ)^p := by positivity
  have h1 := (Work.Fx.FxTdivReal (W * X.1) ((2:ℤ)^p) hqpos).1
  have h2 := (Work.Fx.FxTdivReal (W * X.2) ((2:ℤ)^p) hqpos).1
  -- Split off the real and imaginary parts, each of which is a difference of a
  -- truncated quotient and the true quotient.
  have hkey : (((Int.tdiv (W * X.1) ((2:ℤ)^p) : ℤ) : ℂ)
     + ((Int.tdiv (W * X.2) ((2:ℤ)^p) : ℤ) : ℂ) * Complex.I)
    - (W : ℂ) * ((X.1:ℂ) + (X.2:ℂ)*Complex.I) / ((2:ℂ)^p)
   = ((((Int.tdiv (W*X.1) ((2:ℤ)^p) : ℤ) : ℝ) - ((W*X.1 : ℤ) : ℝ)/(((2:ℤ)^p : ℤ) : ℝ) : ℝ) : ℂ)
     + ((((Int.tdiv (W*X.2) ((2:ℤ)^p) : ℤ) : ℝ) - ((W*X.2 : ℤ) : ℝ)/(((2:ℤ)^p : ℤ) : ℝ) : ℝ) : ℂ) * Complex.I := by
    push_cast
    field_simp
    ring
  calc ‖(((Int.tdiv (W * X.1) ((2 : ℤ) ^ p) : ℤ) : ℂ)
       + ((Int.tdiv (W * X.2) ((2 : ℤ) ^ p) : ℤ) : ℂ) * Complex.I)
      - (W : ℂ) * ((X.1 : ℂ) + (X.2 : ℂ) * Complex.I) / ((2 : ℂ) ^ p)‖
      = ‖((((Int.tdiv (W*X.1) ((2:ℤ)^p) : ℤ) : ℝ) - ((W*X.1 : ℤ) : ℝ)/(((2:ℤ)^p : ℤ) : ℝ) : ℝ) : ℂ)
         + ((((Int.tdiv (W*X.2) ((2:ℤ)^p) : ℤ) : ℝ) - ((W*X.2 : ℤ) : ℝ)/(((2:ℤ)^p : ℤ) : ℝ) : ℝ) : ℂ) * Complex.I‖ := by
        rw [hkey]
    _ ≤ |(((Int.tdiv (W*X.1) ((2:ℤ)^p) : ℤ) : ℝ) - ((W*X.1 : ℤ) : ℝ)/(((2:ℤ)^p : ℤ) : ℝ))|
        + |(((Int.tdiv (W*X.2) ((2:ℤ)^p) : ℤ) : ℝ) - ((W*X.2 : ℤ) : ℝ)/(((2:ℤ)^p : ℤ) : ℝ))| :=
        norm_ofReal_add_I_mul_le _ _
    _ ≤ 2 := by linarith [h1, h2]

end Work.Resample
