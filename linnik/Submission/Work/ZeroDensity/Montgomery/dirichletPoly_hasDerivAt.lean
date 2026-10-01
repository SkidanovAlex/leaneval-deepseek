import Mathlib

namespace Work.ZeroDensity.Montgomery

open scoped Classical BigOperators

/-- The derivative of a Dirichlet polynomial `t ↦ ∑_{n≤N} c n · n^{-it}` (with `n^{-it}` the complex
power `(n : ℂ) ^ (-((t : ℂ) * Complex.I))`): termwise differentiation gives the Dirichlet
polynomial with coefficients `-i (log n) c n`. -/
theorem dirichletPoly_hasDerivAt (N : ℕ) (c : ℕ → ℂ) (t : ℝ) :
    HasDerivAt (fun u : ℝ => ∑ n ∈ Finset.Icc 1 N, c n * (n : ℂ) ^ (-((u : ℂ) * Complex.I)))
      (∑ n ∈ Finset.Icc 1 N, (-(Complex.I * (Real.log n : ℂ))) * c n * (n : ℂ) ^ (-((t : ℂ) * Complex.I))) t := by
  -- rewrite the target function as a pointwise sum of functions so that we may differentiate
  -- termwise with `HasDerivAt.sum`
  rw [show (fun u : ℝ => ∑ n ∈ Finset.Icc 1 N, c n * (n : ℂ) ^ (-((u : ℂ) * Complex.I)))
        = (∑ n ∈ Finset.Icc 1 N, fun u : ℝ => c n * (n : ℂ) ^ (-((u : ℂ) * Complex.I)))
      from by funext u; rw [Finset.sum_apply]]
  apply HasDerivAt.sum
  intro n hn
  have hnz : (n : ℂ) ≠ 0 := by
    have : n ≠ 0 := by
      have : 1 ≤ n := (Finset.mem_Icc.mp hn).1
      omega
    exact_mod_cast this
  -- derivative of `u ↦ (u : ℂ)`, then of `u ↦ -((u : ℂ) * I)`
  have h1 : HasDerivAt (fun u : ℝ => (u : ℂ)) 1 t := by
    have := Complex.ofRealCLM.hasFDerivAt (x := t)
    exact this.hasDerivAt
  have h2 : HasDerivAt (fun u : ℝ => -((u : ℂ) * Complex.I)) (-Complex.I) t := by
    have h := (h1.mul_const Complex.I).neg
    simpa [Pi.neg_def] using h
  -- multiply by the constant `log n` and exponentiate
  have h3 : HasDerivAt (fun u : ℝ => Complex.log (n : ℂ) * -((u : ℂ) * Complex.I))
      (Complex.log (n : ℂ) * -Complex.I) t :=
    h2.const_mul (Complex.log (n : ℂ))
  have h4 : HasDerivAt (fun u : ℝ => Complex.exp (Complex.log (n:ℂ) * -((u:ℂ) * Complex.I)))
      (Complex.exp (Complex.log (n:ℂ) * -((t:ℂ) * Complex.I)) * (Complex.log (n:ℂ) * -Complex.I)) t :=
    h3.cexp
  have h5 := h4.const_mul (c n)
  -- rewrite `exp (log n * -((y:ℂ) * I))` back into the complex power `(n:ℂ) ^ (-((y:ℂ) * I))`
  have hfun : (fun y : ℝ => c n * Complex.exp (Complex.log (n:ℂ) * -((y:ℂ) * Complex.I)))
      = (fun y : ℝ => c n * (n:ℂ)^(-((y:ℂ)*Complex.I))) := by
    funext y; rw [Complex.cpow_def_of_ne_zero hnz]
  rw [hfun] at h5
  -- identify the derivative: `exp(...) * (log n * -I) = -(I * log n) * ...`
  have hderiv : c n * (Complex.exp (Complex.log (n:ℂ) * -((t:ℂ)*Complex.I)) * (Complex.log (n:ℂ) * -Complex.I))
      = (-(Complex.I * (Real.log n:ℂ))) * c n * (n:ℂ)^(-((t:ℂ) * Complex.I)) := by
    rw [← Complex.cpow_def_of_ne_zero hnz (-((t:ℂ)*Complex.I)), ← Complex.natCast_log]
    ring
  rw [hderiv] at h5
  exact h5

end Work.ZeroDensity.Montgomery
