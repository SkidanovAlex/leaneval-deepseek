import Mathlib
import Submission.Work.LinnikAreas.BGTZ.AuxC

namespace Work.LinnikAreas.BGTZ

/-- **The `exp(-s·(A - log(C₀ u))/u) ≤ exp(s·C₀)·(exp(-A))^{s/u}` bound.**

This is the "powers of `exp`" step of the `C₀`-generalised high-zero bound with an
arbitrary positive exponent `s`: both sides are rewritten as single exponentials,

`LHS = exp(-(s/u)·A) · exp((s/u)·log(C₀ u))` and `RHS = exp(s·C₀) · exp(-(s/u)·A)`,

so the claim reduces (as `s/u ≥ 0` and `exp` is monotone) to `log(C₀ u) ≤ C₀ u`. -/
theorem algPowCS {s C₀ u A : ℝ} (hs : 0 < s) (hC₀ : 0 < C₀) (hu : 0 < u) :
    Real.exp (-s * ((A - Real.log (C₀ * u)) / u))
      ≤ Real.exp (s * C₀) * (Real.exp (-A)) ^ (s / u) := by
  have hCu : 0 < C₀ * u := mul_pos hC₀ hu
  -- collapse the real power on the right into a single exponential
  have h1 : (Real.exp (-A)) ^ (s / u) = Real.exp (-A * (s / u)) := by
    rw [Real.exp_mul]
  -- split the left-hand exponential using `exp(x+y) = exp x * exp y`
  have hsplit : Real.exp (-s * ((A - Real.log (C₀ * u)) / u))
      = Real.exp (-(s / u * A)) * Real.exp (s / u * Real.log (C₀ * u)) := by
    rw [← Real.exp_add]
    congr 1
    field_simp
    ring
  have h3 : Real.exp (-(s / u * A)) = Real.exp (-A * (s / u)) := by
    congr 1
    ring
  -- the remaining inequality is `log(C₀ u) ≤ C₀ u`
  have h4 : Real.exp (s / u * Real.log (C₀ * u)) ≤ Real.exp (s * C₀) := by
    rw [Real.exp_le_exp]
    have h5 : Real.log (C₀ * u) ≤ C₀ * u := Real.log_le_self hCu.le
    have h7 : 0 ≤ s / u := by positivity
    have h8 := mul_le_mul_of_nonneg_left h5 h7
    have h9 : s / u * (C₀ * u) = s * C₀ := by field_simp
    linarith
  calc Real.exp (-s * ((A - Real.log (C₀ * u)) / u))
      = Real.exp (-A * (s / u)) * Real.exp (s / u * Real.log (C₀ * u)) := by
        rw [hsplit, h3]
    _ ≤ Real.exp (-A * (s / u)) * Real.exp (s * C₀) :=
        mul_le_mul_of_nonneg_left h4 (Real.exp_pos _).le
    _ = Real.exp (s * C₀) * (Real.exp (-A)) ^ (s / u) := by rw [← h1]; ring

end Work.LinnikAreas.BGTZ
