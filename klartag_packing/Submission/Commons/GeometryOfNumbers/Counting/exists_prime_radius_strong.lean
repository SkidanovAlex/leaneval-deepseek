import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Commons.GeometryOfNumbers.Counting.exists_prime_radius

namespace Commons.GeometryOfNumbers.Counting

open Filter

/-- Given `d ≥ 2` and `ω > 0`, there is a prime `q` and a radius `R` with
`0 < R`, `2R < q`, `4 ω R^d = q`, and `(R + √d/2)^d ω ≤ q/3`. -/
theorem exists_prime_radius_strong {d : ℕ} (hd : 2 ≤ d) {ω : ℝ} (hω : 0 < ω) :
    ∃ q : ℕ, q.Prime ∧ ∃ R : ℝ, 0 < R ∧ 2 * R < (q : ℝ) ∧
      (4 : ℝ) * ω * R ^ d = (q : ℝ) ∧ (R + Real.sqrt (d : ℝ) / 2) ^ d * ω ≤ (q : ℝ) / 3 := by
  have hdne : d ≠ 0 := by omega
  have h4ωpos : (0 : ℝ) < 4 * ω := by linarith
  -- Step 1: a radius threshold beyond which the geometric inequality holds.
  have htend : Tendsto (fun R : ℝ => (1 + (Real.sqrt (d : ℝ) / 2) / R) ^ d) atTop (nhds 1) := by
    have h1 : Tendsto (fun R : ℝ => (Real.sqrt (d : ℝ) / 2) / R) atTop (nhds 0) := by
      simpa [div_eq_mul_inv] using tendsto_inv_atTop_zero.const_mul (Real.sqrt (d : ℝ) / 2)
    have h2 : Tendsto (fun R : ℝ => 1 + (Real.sqrt (d : ℝ) / 2) / R) atTop (nhds (1 + 0)) :=
      tendsto_const_nhds.add h1
    have h3 : Tendsto (fun R : ℝ => (1 + (Real.sqrt (d : ℝ) / 2) / R) ^ d) atTop
        (nhds (1 : ℝ)) := by
      simpa using h2.pow d
    exact h3
  have hev : ∀ᶠ R in atTop, (1 + (Real.sqrt (d : ℝ) / 2) / R) ^ d < 4 / 3 :=
    htend.eventually (isOpen_Iio.mem_nhds (by norm_num : (1 : ℝ) < 4 / 3))
  obtain ⟨R1a, hR1a⟩ := eventually_atTop.1 hev
  -- Step 2: also force `2R < q` by taking a large threshold.
  set R1 : ℝ := max R1a (1 / (2 * ω) + 1) with hR1def
  have hR1_ge_R1a : R1a ≤ R1 := by rw [hR1def]; exact le_max_left _ _
  have hR1_ge_inv : 1 / (2 * ω) + 1 ≤ R1 := by rw [hR1def]; exact le_max_right _ _
  have hR1pos : 0 < R1 := lt_of_lt_of_le (by positivity) hR1_ge_inv
  have hR1_ge1 : 1 ≤ R1 := le_trans (by linarith [show (0:ℝ) < 1 / (2 * ω) by positivity]) hR1_ge_inv
  -- Step 3: choose a large enough prime.
  obtain ⟨n, hn⟩ := exists_nat_ge (4 * ω * R1 ^ d)
  obtain ⟨q, hqn, hqprime⟩ := Nat.exists_infinite_primes n
  have hqT : 4 * ω * R1 ^ d ≤ (q : ℝ) := le_trans hn (by exact_mod_cast hqn)
  have hqpos : 0 < (q : ℝ) := by exact_mod_cast hqprime.pos
  -- Step 4: define the radius R.
  set R : ℝ := ((q : ℝ) / (4 * ω)) ^ ((d : ℝ)⁻¹) with hRdef
  have hxpos : 0 < (q : ℝ) / (4 * ω) := by positivity
  have hRpos : 0 < R := by rw [hRdef]; exact Real.rpow_pos_of_pos hxpos _
  have hRnonneg : 0 ≤ R := le_of_lt hRpos
  have hRpow : R ^ d = (q : ℝ) / (4 * ω) := by
    rw [hRdef]
    exact Real.rpow_inv_natCast_pow (le_of_lt hxpos) hdne
  have hR1d_le : R1 ^ d ≤ (q : ℝ) / (4 * ω) := by
    rw [le_div_iff₀ h4ωpos, mul_comm]
    exact hqT
  have hR_ge_R1 : R1 ≤ R := by
    rw [hRdef]
    have h := Real.rpow_le_rpow (pow_nonneg (le_of_lt hR1pos) d) hR1d_le
      (by positivity : (0 : ℝ) ≤ (d : ℝ)⁻¹)
    rwa [Real.pow_rpow_inv_natCast (le_of_lt hR1pos) hdne] at h
  have hR_ge_R1a : R1a ≤ R := le_trans hR1_ge_R1a hR_ge_R1
  -- Step 5: `2R < q`.
  have hdecomp : R ^ d = R ^ (d - 1) * R := by
    conv_lhs => rw [show d = (d - 1) + 1 by omega]
    rw [pow_succ]
  have hR_ge1 : 1 ≤ R := le_trans hR1_ge1 hR_ge_R1
  have hRd1_ge_R : R ≤ R ^ (d - 1) := by
    have h := pow_le_pow_right₀ hR_ge1 (by omega : 1 ≤ d - 1)
    simpa using h
  have hR_gt_inv : 1 / (2 * ω) < R := by
    have hle : 1 / (2 * ω) + 1 ≤ R := le_trans hR1_ge_inv hR_ge_R1
    linarith
  have h4ωR_gt2 : 2 < 4 * ω * R := by
    have h1 : 1 < R * (2 * ω) := (div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * ω)).mp hR_gt_inv
    nlinarith
  have hlt2 : 2 < 4 * ω * R ^ (d - 1) := by
    have h1 : 4 * ω * R ≤ 4 * ω * R ^ (d - 1) :=
      mul_le_mul_of_nonneg_left hRd1_ge_R (by positivity : (0 : ℝ) ≤ 4 * ω)
    linarith [h1, h4ωR_gt2]
  have h2R_lt : 2 * R < 4 * ω * R ^ d := by
    have h := mul_lt_mul_of_pos_right hlt2 hRpos
    have heq : (4 * ω * R ^ (d - 1)) * R = 4 * ω * R ^ d := by rw [hdecomp]; ring
    linarith [h, heq]
  have hqd : (4 : ℝ) * ω * R ^ d = (q : ℝ) := by
    rw [hRpow]; field_simp
  have h2Rq : 2 * R < (q : ℝ) := by rw [← hqd]; exact h2R_lt
  -- Step 6: the geometric inequality.
  have hgeom : (1 + (Real.sqrt (d : ℝ) / 2) / R) ^ d < 4 / 3 := hR1a R hR_ge_R1a
  have hratio : (R + Real.sqrt (d : ℝ) / 2) ^ d / R ^ d < 4 / 3 := by
    have hfac : (1 + (Real.sqrt (d : ℝ) / 2) / R) = (R + Real.sqrt (d : ℝ) / 2) / R := by
      field_simp
    rw [hfac, div_pow] at hgeom
    exact hgeom
  have h3 : 3 * (R + Real.sqrt (d : ℝ) / 2) ^ d < 4 * R ^ d := by
    have h := (div_lt_div_iff₀ (pow_pos hRpos d) (by norm_num : (0 : ℝ) < 3)).mp hratio
    linarith
  have h4 : 3 * ((R + Real.sqrt (d : ℝ) / 2) ^ d * ω) < 4 * (R ^ d * ω) := by
    have h := mul_lt_mul_of_pos_right h3 hω
    linarith
  have hqdω : 4 * (R ^ d * ω) = (q : ℝ) := by
    rw [← hqd]; ring
  have h5 : 3 * ((R + Real.sqrt (d : ℝ) / 2) ^ d * ω) < (q : ℝ) := by
    rw [← hqdω]; exact h4
  have h6 : (R + Real.sqrt (d : ℝ) / 2) ^ d * ω < (q : ℝ) / 3 := by linarith
  exact ⟨q, hqprime, R, hRpos, h2Rq, hqd, le_of_lt h6⟩

end Commons.GeometryOfNumbers.Counting