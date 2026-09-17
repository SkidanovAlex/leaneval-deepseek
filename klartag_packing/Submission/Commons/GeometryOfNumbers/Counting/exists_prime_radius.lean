import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Complex.ExponentialBounds

namespace Commons.GeometryOfNumbers.Counting

/-- Given `d ≥ 2` and `ω > 0`, there is a prime `q` and a radius `R` with
`1 ≤ R < q`, `4 ω R^d = q`, and `(R + √d/2)^d ω < 2q`. -/
theorem exists_prime_radius {d : ℕ} (hd : 2 ≤ d) {ω : ℝ} (hω : 0 < ω) :
    ∃ q : ℕ, q.Prime ∧ ∃ R : ℝ, 0 < R ∧ 1 ≤ R ∧ R < (q : ℝ) ∧
      (4 : ℝ) * ω * R ^ d = (q : ℝ) ∧ (R + Real.sqrt (d : ℝ) / 2) ^ d * ω < 2 * (q : ℝ) := by
  have hdne : d ≠ 0 := by omega
  have hdRne : (d : ℝ) ≠ 0 := by exact_mod_cast hdne
  have hdRpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (by omega : 0 < d)
  have h4ωpos : (0 : ℝ) < 4 * ω := by linarith
  -- Step 1: reference radius R0 = d * √d satisfies the geometric bound.
  set R0 : ℝ := (d : ℝ) * Real.sqrt (d : ℝ) with hR0def
  have hR0pos : 0 < R0 := by rw [hR0def]; positivity
  have hR0nonneg : 0 ≤ R0 := le_of_lt hR0pos
  have hsqrt_le : Real.sqrt (d : ℝ) / (2 * R0) ≤ 1 / (2 * (d : ℝ)) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity), one_mul]
    have hEq : Real.sqrt (d : ℝ) * (2 * (d : ℝ)) = 2 * R0 := by
      rw [hR0def]; ring
    rw [hEq]
  have hexp_bound : (1 + 1 / (2 * (d : ℝ))) ^ d ≤ Real.exp (1 / 2) := by
    have h1 : (1 : ℝ) + 1 / (2 * (d : ℝ)) ≤ Real.exp (1 / (2 * (d : ℝ))) := by
      have := Real.add_one_le_exp (1 / (2 * (d : ℝ)))
      linarith
    have h2 : ((1 : ℝ) + 1 / (2 * (d : ℝ))) ^ d ≤ (Real.exp (1 / (2 * (d : ℝ)))) ^ d :=
      pow_le_pow_left₀ (by positivity) h1 d
    have h3 : (Real.exp (1 / (2 * (d : ℝ)))) ^ d = Real.exp (1 / 2) := by
      rw [← Real.exp_nat_mul]
      have hd : (d : ℝ) * (1 / (2 * (d : ℝ))) = 1 / 2 := by
        field_simp
      rw [hd]
    linarith [h2, h3.le]
  have hexp_lt : Real.exp (1 / 2) < (8 : ℝ) := by
    have h1 : Real.exp (1 / 2) < Real.exp 1 := by
      rw [Real.exp_lt_exp]; norm_num
    linarith [Real.exp_one_lt_three]
  have hkey : (1 + Real.sqrt (d : ℝ) / (2 * R0)) ^ d < 8 := by
    have hle : (1 + Real.sqrt (d : ℝ) / (2 * R0)) ≤ (1 + 1 / (2 * (d : ℝ))) := by
      linarith [hsqrt_le]
    calc (1 + Real.sqrt (d : ℝ) / (2 * R0)) ^ d
        ≤ (1 + 1 / (2 * (d : ℝ))) ^ d := pow_le_pow_left₀ (by positivity) hle d
      _ ≤ Real.exp (1 / 2) := hexp_bound
      _ < 8 := hexp_lt
  -- Step 2: choose a large enough prime.
  obtain ⟨n, hn⟩ := exists_nat_ge (max (max (4 * ω) (4 * ω * R0 ^ d)) (1 / (4 * ω) + 1))
  obtain ⟨q, hqn, hqprime⟩ := Nat.exists_infinite_primes n
  have hqT : max (max (4 * ω) (4 * ω * R0 ^ d)) (1 / (4 * ω) + 1) ≤ (q : ℝ) :=
    le_trans hn (by exact_mod_cast hqn)
  have hq_ge_4w : (4 : ℝ) * ω ≤ (q : ℝ) :=
    le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hqT
  have hq_ge_R0 : (4 : ℝ) * ω * R0 ^ d ≤ (q : ℝ) :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hqT
  have hq_gt_inv : 1 / ((4 : ℝ) * ω) + 1 ≤ (q : ℝ) :=
    le_trans (le_max_right _ _) hqT
  have hqpos : 0 < (q : ℝ) := by exact_mod_cast hqprime.pos
  have hq_nonneg : 0 ≤ (q : ℝ) := le_of_lt hqpos
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by
    exact_mod_cast (le_trans (by norm_num : 1 ≤ 2) hqprime.two_le)
  -- Step 3: define R and verify.
  set R : ℝ := ((q : ℝ) / (4 * ω)) ^ ((d : ℝ)⁻¹) with hRdef
  have hxpos : 0 < (q : ℝ) / (4 * ω) := by positivity
  have hRpos : 0 < R := by rw [hRdef]; exact Real.rpow_pos_of_pos hxpos _
  have hRnonneg : 0 ≤ R := le_of_lt hRpos
  have hRpow : R ^ d = (q : ℝ) / (4 * ω) := by
    rw [hRdef]
    exact Real.rpow_inv_natCast_pow (le_of_lt hxpos) hdne
  have hx_ge_one : 1 ≤ (q : ℝ) / (4 * ω) := by
    rw [one_le_div₀ h4ωpos]; exact hq_ge_4w
  have hRge1 : 1 ≤ R := by
    rw [hRdef]
    exact Real.one_le_rpow hx_ge_one (by positivity)
  have hR0d_le : R0 ^ d ≤ (q : ℝ) / (4 * ω) := by
    rw [le_div_iff₀ h4ωpos, mul_comm]
    exact hq_ge_R0
  have hR_ge_R0 : R0 ≤ R := by
    have h := Real.rpow_le_rpow (pow_nonneg hR0nonneg d) hR0d_le (by positivity : (0 : ℝ) ≤ (d : ℝ)⁻¹)
    have hR0pow : (R0 ^ d) ^ ((d : ℝ)⁻¹) = R0 := Real.pow_rpow_inv_natCast hR0nonneg hdne
    rw [hRdef]
    linarith [h, hR0pow]
  have hq_gt : 1 / (4 * ω) < (q : ℝ) := by linarith [hq_gt_inv]
  have hqq : (q : ℝ) / (4 * ω) < (q : ℝ) * (q : ℝ) := by
    rw [div_eq_mul_inv]
    have hinv : ((4 : ℝ) * ω)⁻¹ < (q : ℝ) := by simpa [one_div] using hq_gt
    exact mul_lt_mul_of_pos_left hinv hqpos
  have hqqd : (q : ℝ) * (q : ℝ) ≤ (q : ℝ) ^ d := by
    have h := pow_le_pow_right₀ hq1 hd
    simpa [pow_two] using h
  have hlt : R ^ d < (q : ℝ) ^ d := by
    rw [hRpow]; exact lt_of_lt_of_le hqq hqqd
  have hRlt : R < (q : ℝ) := (pow_lt_pow_iff_left₀ hRnonneg hq_nonneg hdne).mp hlt
  have hReq : (4 : ℝ) * ω * R ^ d = (q : ℝ) := by
    rw [hRpow]; field_simp
  -- final geometric inequality
  have hu_le : Real.sqrt (d : ℝ) / (2 * R) ≤ 1 / (2 * (d : ℝ)) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity), one_mul]
    have hEq : Real.sqrt (d : ℝ) * (2 * (d : ℝ)) = 2 * R0 := by rw [hR0def]; ring
    rw [hEq]
    linarith [hR_ge_R0]
  have hu_bound : (1 + Real.sqrt (d : ℝ) / (2 * R)) ^ d < 8 := by
    have hle : 1 + Real.sqrt (d : ℝ) / (2 * R) ≤ 1 + 1 / (2 * (d : ℝ)) := by
      linarith [hu_le]
    calc (1 + Real.sqrt (d : ℝ) / (2 * R)) ^ d
        ≤ (1 + 1 / (2 * (d : ℝ))) ^ d := pow_le_pow_left₀ (by positivity) hle d
      _ ≤ Real.exp (1 / 2) := hexp_bound
      _ < 8 := hexp_lt
  have hfac : R + Real.sqrt (d : ℝ) / 2 = R * (1 + Real.sqrt (d : ℝ) / (2 * R)) := by
    field_simp
  have hA : R ^ d * (1 + Real.sqrt (d : ℝ) / (2 * R)) ^ d < 8 * R ^ d := by
    have h := mul_lt_mul_of_pos_left hu_bound (pow_pos hRpos d)
    rwa [mul_comm (R ^ d) 8] at h
  have hstep : (R + Real.sqrt (d : ℝ) / 2) ^ d * ω < (8 * R ^ d) * ω := by
    rw [hfac, mul_pow]
    exact mul_lt_mul_of_pos_right hA hω
  have h2q : 2 * (q : ℝ) = (8 * R ^ d) * ω := by
    rw [hRpow]; field_simp; ring
  have hfinal : (R + Real.sqrt (d : ℝ) / 2) ^ d * ω < 2 * (q : ℝ) := by
    linarith [hstep, h2q]
  exact ⟨q, hqprime, R, hRpos, hRge1, hRlt, hReq, hfinal⟩

end Commons.GeometryOfNumbers.Counting