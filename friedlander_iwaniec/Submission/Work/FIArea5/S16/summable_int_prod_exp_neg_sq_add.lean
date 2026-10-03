import Mathlib

namespace Work.FIArea5.S16

open Real

/-- One-dimensional Gaussian sum with a power weight: `Σ_{n∈ℤ} |n|^j e^{-d n²}` converges
for `d > 0`.  Reduced to `HurwitzKernelBounds.summable_f_int` with `π t = d`. -/
theorem summable_int_abs_pow_mul_exp_neg_sq {d : ℝ} (hd : 0 < d) (j : ℕ) :
    Summable (fun n : ℤ => |(n : ℝ)| ^ j * Real.exp (-d * (n : ℝ) ^ 2)) := by
  have h := HurwitzKernelBounds.summable_f_int j 0 (t := d / Real.pi) (by positivity)
  refine h.congr (fun n => ?_)
  simp only [HurwitzKernelBounds.f_int, add_zero]
  have hkey : Real.pi * (n : ℝ) ^ 2 * (d / Real.pi) = d * (n : ℝ) ^ 2 := by
    rw [mul_assoc, mul_comm ((n:ℝ)^2) (d/Real.pi), ← mul_assoc,
      show Real.pi * (d / Real.pi) = d by rw [mul_comm, div_mul_cancel₀ d Real.pi_ne_zero]]
  have hneg : (-Real.pi) * (n : ℝ) ^ 2 * (d / Real.pi) = -d * (n : ℝ) ^ 2 := by
    have h1 : (-Real.pi) * (n:ℝ)^2 * (d/Real.pi)
        = -(Real.pi * (n:ℝ)^2 * (d/Real.pi)) := by ring
    rw [h1, hkey]; ring
  rw [hneg]

/-- One-dimensional Gaussian sum with a polynomial weight: `Σ_{n∈ℤ} e^{-d n²} (1 + n²)^k`
converges for `d > 0`.  The polynomial is expanded by the binomial theorem into a finite
combination of the power-weighted Gaussians of `summable_int_abs_pow_mul_exp_neg_sq`. -/
theorem summable_int_exp_neg_sq_mul_one_add_sq_pow {d : ℝ} (hd : 0 < d) (k : ℕ) :
    Summable (fun n : ℤ => Real.exp (-d * (n : ℝ) ^ 2) * (1 + (n : ℝ) ^ 2) ^ k) := by
  have key : (fun n : ℤ => Real.exp (-d * (n : ℝ) ^ 2) * (1 + (n : ℝ) ^ 2) ^ k)
      = fun n : ℤ => ∑ j ∈ Finset.range (k+1),
          (k.choose j : ℝ) * (|(n : ℝ)| ^ (2*j) * Real.exp (-d * (n : ℝ) ^ 2)) := by
    funext n
    rw [show (1 + (n:ℝ)^2)^k = ∑ j ∈ Finset.range (k+1), ((n:ℝ)^2)^j * (k.choose j : ℝ) by
        rw [add_comm 1 ((n:ℝ)^2), add_pow]
        simp
      , Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [pow_mul, sq_abs]
    ring
  rw [key]
  apply summable_sum
  intro j _
  exact (summable_int_abs_pow_mul_exp_neg_sq hd (2*j)).mul_left _

/-- **Summability of a quadratically-decaying exponential with a linear growth factor and a
polynomial weight over `ℤ × ℤ`.**

For `c > 0`, any `C : ℝ` and `k : ℕ`, the lattice sum
`Σ_{(m,n)∈ℤ²} e^{-c(m²+n²) + C(|m|+|n|)} (1 + m² + n²)^k` converges absolutely.

The linear term `C(|m|+|n|)` is absorbed into the quadratic decay by two AM–GM inequalities
`C|m| - (c/4)m² ≤ C²/c`, and the polynomial is dominated by `(1+m²)^k (1+n²)^k`, so that the
summand is bounded by a constant multiple of a product `φ(m) φ(n)` of two summable
one-dimensional Gaussian sums `φ(n) = e^{-(3c/4)n²} (1+n²)^k`. -/
theorem summable_int_prod_exp_neg_sq_add {c : ℝ} (hc : 0 < c) (C : ℝ) (k : ℕ) :
    Summable (fun p : ℤ × ℤ => Real.exp (-c * ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2)
      + C * (|(p.1 : ℝ)| + |(p.2 : ℝ)|)) * (1 + (p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2) ^ k) := by
  have hd : 0 < 3 * c / 4 := by linarith
  have hφ : Summable (fun n : ℤ => Real.exp (-(3*c/4) * (n:ℝ)^2) * (1 + (n:ℝ)^2)^k) :=
    summable_int_exp_neg_sq_mul_one_add_sq_pow hd k
  have hprod : Summable (fun p : ℤ × ℤ =>
      (Real.exp (-(3*c/4) * (p.1:ℝ)^2) * (1 + (p.1:ℝ)^2)^k)
      * (Real.exp (-(3*c/4) * (p.2:ℝ)^2) * (1 + (p.2:ℝ)^2)^k)) :=
    Summable.mul_of_nonneg hφ hφ (fun n => by positivity) (fun n => by positivity)
  have key : ∀ x y : ℝ, Real.exp (-c*(x^2+y^2) + C*(|x|+|y|)) * (1+x^2+y^2)^k
      ≤ Real.exp (C^2/c + C^2/c) *
        ((Real.exp (-(3*c/4)*x^2)*(1+x^2)^k) * (Real.exp (-(3*c/4)*y^2)*(1+y^2)^k)) := by
    intro x y
    have hamgm : C * |x| - (c/4) * x^2 ≤ C^2/c := by
      have hpos : (0:ℝ) ≤ (1/(4*c)) * (c*|x| - 2*C)^2 := by positivity
      have h1 : C^2/c - C*|x| + (c/4)*x^2 = (1/(4*c)) * (c*|x| - 2*C)^2 := by
        rw [← sq_abs x]; field_simp; ring
      linarith
    have hamgm' : C * |y| - (c/4) * y^2 ≤ C^2/c := by
      have hpos : (0:ℝ) ≤ (1/(4*c)) * (c*|y| - 2*C)^2 := by positivity
      have h1 : C^2/c - C*|y| + (c/4)*y^2 = (1/(4*c)) * (c*|y| - 2*C)^2 := by
        rw [← sq_abs y]; field_simp; ring
      linarith
    have h_arg : -c*(x^2+y^2) + C*(|x|+|y|) ≤ (C^2/c + C^2/c) + -(3*c/4)*(x^2+y^2) := by
      linarith [hamgm, hamgm']
    have hA : Real.exp (-c*(x^2+y^2) + C*(|x|+|y|))
        ≤ Real.exp (C^2/c + C^2/c) * (Real.exp (-(3*c/4)*x^2) * Real.exp (-(3*c/4)*y^2)) := by
      have e1 : Real.exp (C^2/c + C^2/c) * (Real.exp (-(3*c/4)*x^2) * Real.exp (-(3*c/4)*y^2))
          = Real.exp ((C^2/c + C^2/c) + -(3*c/4)*(x^2+y^2)) := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
      rw [e1]
      exact Real.exp_le_exp.mpr h_arg
    have hB : (1+x^2+y^2)^k ≤ (1+x^2)^k * (1+y^2)^k := by
      have hle : 1 + x^2 + y^2 ≤ (1+x^2)*(1+y^2) := by nlinarith [sq_nonneg (x*y)]
      rw [← mul_pow]
      exact pow_le_pow_left₀ (by positivity) hle k
    have hres := mul_le_mul hA hB (by positivity) (by positivity)
    calc Real.exp (-c*(x^2+y^2) + C*(|x|+|y|)) * (1+x^2+y^2)^k
        ≤ (Real.exp (C^2/c + C^2/c) * (Real.exp (-(3*c/4)*x^2) * Real.exp (-(3*c/4)*y^2)))
            * ((1+x^2)^k * (1+y^2)^k) := hres
      _ = Real.exp (C^2/c + C^2/c) *
            ((Real.exp (-(3*c/4)*x^2)*(1+x^2)^k) * (Real.exp (-(3*c/4)*y^2)*(1+y^2)^k)) := by
          ring
  refine Summable.of_nonneg_of_le (fun p => by positivity) (fun p => ?_)
    (hprod.mul_left (Real.exp (C^2/c + C^2/c)))
  obtain ⟨i, j⟩ := p
  exact key i j

end Work.FIArea5.S16
