import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Submission.Commons.NumberTheory.Mertens.corr_partial_sums_tendsto_tsum

namespace Commons.NumberTheory.Mertens

/-- Termwise bridge between the complex and real logarithms in the Euler-product logarithm.

For a real `1 < s` and a prime `p`, the complex-logarithm summand
`-log (1 - p^(-s))` (with complex `log`) equals the coercion of the real-logarithm
summand `-log (1 - p^(-s))` (with real `log`). -/
lemma exp_primeZetaLog_log_term_eq {s : ℝ} (hs : 1 < s) (p : Nat.Primes) :
    -Complex.log (1 - ((p : ℕ) : ℂ) ^ (-(s : ℂ))) =
      -↑(Real.log (1 - ((p : ℕ) : ℝ) ^ (-s))) := by
  have hbase : 1 < ((p : ℕ) : ℝ) := by
    exact_mod_cast p.prop.one_lt
  have hneg : -s < 0 := by linarith
  have hpow : ((p : ℕ) : ℝ) ^ (-s) < 1 := by
    have h := Real.rpow_lt_rpow_of_exponent_lt hbase hneg
    simpa using h
  have hle : 0 ≤ 1 - ((p : ℕ) : ℝ) ^ (-s) := by linarith
  have hcpow : ((((p : ℕ) : ℝ) ^ (-s) : ℝ) : ℂ) = ((p : ℕ) : ℂ) ^ (-(s : ℂ)) := by
    simpa [Complex.ofReal_natCast, Complex.ofReal_neg] using
      (Complex.ofReal_cpow (x := ((p : ℕ) : ℝ)) (y := -s)
        (by positivity : 0 ≤ ((p : ℕ) : ℝ)))
  have hlog : (Real.log (1 - ((p : ℕ) : ℝ) ^ (-s)) : ℂ) =
      Complex.log (1 - ((p : ℕ) : ℂ) ^ (-(s : ℂ))) := by
    rw [Complex.ofReal_log hle]
    congr 1
    · rw [← hcpow]
      simp
  calc
    -Complex.log (1 - ((p : ℕ) : ℂ) ^ (-(s : ℂ))) =
        -((Real.log (1 - ((p : ℕ) : ℝ) ^ (-s))) : ℂ) := by rw [hlog]
    _ = -↑(Real.log (1 - ((p : ℕ) : ℝ) ^ (-s))) := by simp

/-- The exponential of the negative-logarithm sum over primes (the logarithm of the Euler
product) equals the real part of the analytically continued Riemann zeta function, for real
`s > 1`. -/
lemma exp_primeZetaLog_eq_riemannZeta_re {s : ℝ} (hs : 1 < s) :
    Real.exp (∑' p : Nat.Primes, -Real.log (1 - ((p : ℕ) : ℝ) ^ (-s))) =
      (riemannZeta (s : ℂ)).re := by
  let S : ℝ := ∑' p : Nat.Primes, -Real.log (1 - ((p : ℕ) : ℝ) ^ (-s))
  have hsC : 1 < (s : ℂ).re := by simpa using hs
  have hZeta :
      Complex.exp (∑' p : Nat.Primes, -Complex.log (1 - ((p : ℕ) : ℂ) ^ (-(s : ℂ)))) =
        riemannZeta (s : ℂ) := by
    simpa using (riemannZeta_eulerProduct_exp_log (s := (s : ℂ)) hsC)
  have hArg :
      (∑' p : Nat.Primes, -Complex.log (1 - ((p : ℕ) : ℂ) ^ (-(s : ℂ)))) = (S : ℂ) := by
    calc
      (∑' p : Nat.Primes, -Complex.log (1 - ((p : ℕ) : ℂ) ^ (-(s : ℂ)))) =
          ∑' p : Nat.Primes, ((-Real.log (1 - ((p : ℕ) : ℝ) ^ (-s))) : ℂ) := by
            apply tsum_congr
            intro p
            simpa using exp_primeZetaLog_log_term_eq hs p
      _ = (S : ℂ) := by
            simpa using (Complex.ofReal_tsum (α := Nat.Primes)
              (f := fun p : Nat.Primes => -Real.log (1 - ((p : ℕ) : ℝ) ^ (-s)))).symm
  have hZetaR : riemannZeta (s : ℂ) = (Real.exp S : ℂ) := by
    calc
      riemannZeta (s : ℂ) =
          Complex.exp (∑' p : Nat.Primes, -Complex.log (1 - ((p : ℕ) : ℂ) ^ (-(s : ℂ)))) :=
            hZeta.symm
      _ = Complex.exp (S : ℂ) := by rw [hArg]
      _ = (Real.exp S : ℂ) := (Complex.ofReal_exp S).symm
  calc
    Real.exp S = ((Real.exp S : ℂ)).re := (Complex.ofReal_re (Real.exp S)).symm
    _ = (riemannZeta (s : ℂ)).re := by rw [hZetaR]

end Commons.NumberTheory.Mertens