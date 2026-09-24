import Mathlib

namespace Work.GM.Affine

/-- The series `∑_{ℓ ∈ ℤ} 1/(1+|ℓ|)^k` converges for `k ≥ 2`: splitting `ℤ` into `ℕ` and the
negative integers reduces it to two shifted `p`-series, whose convergence is
`Real.summable_nat_pow_inv`. -/
theorem summable_int_inv_one_add_abs_pow (k : ℕ) (hk : 1 < k) :
    Summable (fun ℓ : ℤ => (1:ℝ) / (1 + |((ℓ:ℤ):ℝ)|)^k) := by
  have hbase : Summable (fun n : ℕ => ((n:ℝ)^k)⁻¹) := Real.summable_nat_pow_inv.mpr hk
  have h1 : Summable (fun n : ℕ => (1:ℝ) / (1 + |(((n:ℤ):ℝ))|)^k) := by
    have h := (summable_nat_add_iff (f := fun n : ℕ => ((n:ℝ)^k)⁻¹) 1).mpr hbase
    refine h.congr (fun n => ?_)
    have hb : (1:ℝ) + |(((n:ℤ):ℝ))| = ((n + 1 : ℕ) : ℝ) := by
      rw [show (((n:ℤ):ℝ)) = (n:ℝ) by push_cast; ring,
        abs_of_nonneg (by positivity : (0:ℝ) ≤ (n:ℝ))]
      push_cast
      ring
    rw [← hb, one_div]
  have h2 : Summable (fun n : ℕ => (1:ℝ) / (1 + |(((-(n+1) : ℤ) : ℝ))|)^k) := by
    have h := (summable_nat_add_iff (f := fun n : ℕ => ((n:ℝ)^k)⁻¹) 2).mpr hbase
    refine h.congr (fun n => ?_)
    have hb : (1:ℝ) + |(-((n:ℝ) + 1))| = ((n + 2 : ℕ) : ℝ) := by
      rw [abs_neg, abs_of_nonneg (by positivity : (0:ℝ) ≤ (n:ℝ) + 1)]
      push_cast
      ring
    rw [show (((-(n+1) : ℤ) : ℝ)) = -((n:ℝ) + 1) by push_cast; ring, ← hb, one_div]
  exact Summable.of_nat_of_neg_add_one h1 h2

end Work.GM.Affine
