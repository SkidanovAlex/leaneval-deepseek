import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
import Submission.Work.BoseFixR.LatGreen.PoissonDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixR.LatGreen

/-- Poisson/Jacobi summation in one dimension: the periodisation of the Gaussian heat kernel
`heatK1 t` on `ℝ/ℤ` is its Fourier series, in complex-exponential form:
`Σ_{n∈ℤ} heatK1 t (x−n) = Σ_{m∈ℤ} exp(−4π²t m²) e^{−2πi m x}`.  Suggested route: Mathlib's Jacobi
theta transformation `Complex.tsum_exp_neg_quadratic` applied with `a = (1/(4πt) : ℂ)` and
`b = (x/(4πt) : ℂ)` (so that `π a = 1/(4t)`, `2π b = x/(2t)`, `π/a = 4π²t`); write
`(heatK1 t (x−n) : ℂ) = (4πt)^{-1/2} · cexp(−(x−n)²/(4t))` and use `Complex.ofReal_exp`,
`Complex.ofReal_cpow`, `Real.rpow_add`, `Real.rpow_neg` to cancel the `(4πt)^{∓1/2}` factors, and
`Summable.tsum_mul_left` (or the unconditional `tsum_mul_left`) to pull the constants
`cexp(∓x²/(4t))` out of the sums.

Proof as carried out below: with `a = (1/(4πt) : ℂ)`, `b = (x/(4πt) : ℂ)`, Jacobi
(`Complex.tsum_exp_neg_quadratic`) reads

`Σ_n cexp(−π a n² + 2π b n) = a^{−1/2} Σ_n cexp(−(π/a)(n + ib)²)`,

and termwise (`tsum_congr`, no convergence needed)
* `cexp(−π a n² + 2π b n) = ↑(exp(−n²/(4t) + xn/(2t)))`,
* `cexp(−(π/a)(n+ib)²) = ↑(exp(x²/(4t))) · thetaTerm1 t x n`,
* `↑(heatK1 t (x−n)) = ca · ↑(exp(−n²/(4t) + xn/(2t)))` with `ca = ↑((4πt)^{−1/2})·↑(exp(−x²/(4t)))`,
* `1/a^{1/2} = ↑((4πt)^{1/2})`, and `ca · ↑((4πt)^{1/2}) · ↑(exp(x²/(4t))) = 1`.
The constants are pulled out of the sums by the unconditional `tsum_mul_left`. -/
theorem tsum_heatK1_eq {t : ℝ} (ht : 0 < t) (x : ℝ) :
    (∑' n : ℤ, (Work.BoseFixR.LatGreen.heatK1 t (x - n) : ℂ))
      = ∑' m : ℤ, Work.BoseFixR.LatGreen.thetaTerm1 t x m := by
  have ht0 : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  have hp0 : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  -- the Jacobi parameters
  set a : ℂ := ((1 / (4 * Real.pi * t) : ℝ) : ℂ) with ha
  set b : ℂ := ((x / (4 * Real.pi * t) : ℝ) : ℂ) with hb
  have ha_re : 0 < a.re := by rw [ha, Complex.ofReal_re]; positivity
  have hJ := Complex.tsum_exp_neg_quadratic (a := a) ha_re b
  -- the three sums and the constants
  set S : ℂ := ∑' n : ℤ, (Real.exp (-((n:ℝ)^2/(4*t)) + x*(n:ℝ)/(2*t)) : ℂ) with hS
  set T : ℂ := ∑' n : ℤ, Complex.exp (-(Real.pi : ℂ) / a * ((n:ℂ) + Complex.I * b)^2) with hT
  set R : ℂ := ∑' m : ℤ, Work.BoseFixR.LatGreen.thetaTerm1 t x m with hR
  set ca : ℂ := (((4*Real.pi*t) ^ (-(1/2:ℝ)) : ℝ) : ℂ) * (Real.exp (-(x^2/(4*t))) : ℂ) with hca
  set cb : ℂ := (((4*Real.pi*t) ^ (1/2:ℝ) : ℝ) : ℂ) with hcb
  set cc : ℂ := (Real.exp (x^2/(4*t)) : ℂ) with hcc0
  -- `S` is the left-hand side of Jacobi's transformation
  have hSJ : S = ∑' n : ℤ, Complex.exp (-(Real.pi : ℂ) * a * (n:ℂ)^2 + 2*(Real.pi:ℂ)*b*(n:ℂ)) := by
    rw [hS]
    apply tsum_congr
    intro n
    rw [ha, hb]
    rw [show -(Real.pi : ℂ) * ((1/(4*Real.pi*t) : ℝ) : ℂ) * (n:ℂ)^2
        + 2*(Real.pi:ℂ)*((x/(4*Real.pi*t):ℝ):ℂ)*(n:ℂ)
      = ((-((n:ℝ)^2/(4*t)) + x*(n:ℝ)/(2*t) : ℝ) : ℂ) from by
        push_cast; field_simp; ring]
    rw [← Complex.ofReal_exp]
  -- the left-hand side of the goal is `ca * S`
  have hLen : (∑' n : ℤ, (Work.BoseFixR.LatGreen.heatK1 t (x - n) : ℂ)) = ca * S := by
    rw [hca, hS, ← tsum_mul_left]
    apply tsum_congr
    intro n
    have h1 : -(x - (n:ℝ))^2/(4*t) = -(x^2/(4*t)) + (-((n:ℝ)^2/(4*t)) + x*(n:ℝ)/(2*t)) := by
      field_simp; ring
    calc (Work.BoseFixR.LatGreen.heatK1 t (x - (n:ℝ)) : ℂ)
        = (((4*Real.pi*t) ^ (-(1/2:ℝ)) : ℝ) : ℂ) * (Real.exp (-(x - (n:ℝ))^2/(4*t)) : ℂ) := by
          unfold Work.BoseFixR.LatGreen.heatK1; push_cast; ring
      _ = (((4*Real.pi*t) ^ (-(1/2:ℝ)) : ℝ) : ℂ)
            * (Real.exp (-(x^2/(4*t)) + (-((n:ℝ)^2/(4*t)) + x*(n:ℝ)/(2*t))) : ℂ) := by
          rw [← h1]
      _ = ((((4*Real.pi*t) ^ (-(1/2:ℝ)) : ℝ) : ℂ) * (Real.exp (-(x^2/(4*t))) : ℂ))
            * (Real.exp (-((n:ℝ)^2/(4*t)) + x*(n:ℝ)/(2*t)) : ℂ) := by
          rw [Real.exp_add]; push_cast; ring
  -- the right-hand side of Jacobi's transformation is `cc * R`
  have hTR : T = cc * R := by
    rw [hT, hR, hcc0, ← tsum_mul_left]
    apply tsum_congr
    intro n
    rw [ha, hb]
    have h2 : -(Real.pi : ℂ) / ((1/(4*Real.pi*t) : ℝ) : ℂ)
          * ((n:ℂ) + Complex.I * ((x/(4*Real.pi*t) : ℝ):ℂ))^2
        = ((x^2/(4*t) : ℝ) : ℂ) + (((-(4*Real.pi^2*t)*(n:ℝ)^2) : ℝ) : ℂ)
          + (-(2*Real.pi * Complex.I * ((n:ℝ)*x))) := by
      have ht0 : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
      have hp0 : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
      push_cast
      field_simp
      ring_nf
      rw [Complex.I_sq]
      ring
    rw [h2, Complex.exp_add]
    rw [Complex.exp_add]
    rw [← Complex.ofReal_exp, ← Complex.ofReal_exp]
    unfold Work.BoseFixR.LatGreen.thetaTerm1
    ring
  -- the Jacobi prefactor `1 / a^{1/2}` is `(4πt)^{1/2}`
  have hcoef : 1 / a ^ (1/2 : ℂ) = cb := by
    rw [ha, hcb]
    have h1 : (((1/(4*Real.pi*t) : ℝ)) : ℂ) ^ ((1/2 : ℂ))
        = ((((1/(4*Real.pi*t) : ℝ) ^ (1/2:ℝ)) : ℝ) : ℂ) := by
      rw [show (1/2 : ℂ) = ((1/2 : ℝ) : ℂ) from by norm_num]
      exact (Complex.ofReal_cpow (by positivity : (0:ℝ) ≤ 1/(4*Real.pi*t)) (1/2)).symm
    rw [h1, ← Complex.ofReal_one, ← Complex.ofReal_div, Complex.ofReal_inj]
    rw [show (1 / (4*Real.pi*t) : ℝ) = (4*Real.pi*t)⁻¹ from by rw [one_div],
      Real.inv_rpow (by positivity : (0:ℝ) ≤ 4*Real.pi*t)]
    simp
  -- the constants cancel
  have hcc1 : ca * cb * cc = 1 := by
    rw [hca, hcb, hcc0]
    rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Complex.ofReal_one,
      Complex.ofReal_inj]
    have e1 : (4*Real.pi*t) ^ (-(1/2:ℝ)) * (4*Real.pi*t) ^ (1/2:ℝ) = 1 := by
      rw [← Real.rpow_add (by positivity : (0:ℝ) < 4*Real.pi*t),
        show -(1/2:ℝ) + 1/2 = 0 from by norm_num, Real.rpow_zero]
    have e2 : Real.exp (-(x^2/(4*t))) * Real.exp (x^2/(4*t)) = 1 := by
      rw [← Real.exp_add, show -(x^2/(4*t)) + x^2/(4*t) = (0:ℝ) from by ring, Real.exp_zero]
    rw [show (((4*Real.pi*t) ^ (-(1/2:ℝ)) * Real.exp (-(x^2/(4*t)))) * (4*Real.pi*t) ^ (1/2:ℝ)
        * Real.exp (x^2/(4*t)))
        = ((4*Real.pi*t) ^ (-(1/2:ℝ)) * (4*Real.pi*t) ^ (1/2:ℝ))
          * (Real.exp (-(x^2/(4*t))) * Real.exp (x^2/(4*t))) from by ring]
    rw [e1, e2, one_mul]
  calc (∑' n : ℤ, (Work.BoseFixR.LatGreen.heatK1 t (x - n) : ℂ))
      = ca * S := hLen
    _ = ca * (∑' n : ℤ, Complex.exp (-(Real.pi : ℂ) * a * (n:ℂ)^2 + 2*(Real.pi:ℂ)*b*(n:ℂ))) := by
          rw [hSJ]
    _ = ca * (1 / a ^ (1/2 : ℂ) * T) := by rw [hJ]
    _ = ca * (cb * (cc * R)) := by rw [hcoef, hTR]
    _ = R := by
        rw [show ca * (cb * (cc * R)) = (ca * cb * cc) * R from by ring, hcc1, one_mul]

end Work.BoseFixR.LatGreen
