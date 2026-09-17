import Mathlib
import Submission.Commons.Probability.Gaussian.stdGaussian_real_tail_le
import Submission.Commons.Analysis.Asymptotics.geom_sum_range_le
import Submission.Commons.Analysis.Exponential.exp_le_one_div_one_sub

open MeasureTheory

namespace Commons.Probability.Gaussian

/-- The standard Gaussian tail is dominated by `exp (-z^2/2)` for `z > 0`.
This is the crude Chernoff-type bound obtained from the Mills ratio bound. -/
theorem stdGaussian_real_tail_le_exp (z : ℝ) (hz : 0 < z) :
    (ProbabilityTheory.stdGaussian ℝ).real {y : ℝ | z ≤ y} ≤ Real.exp (-(z ^ 2) / 2) := by
  refine le_trans (stdGaussian_real_tail_le z hz) ?_
  rw [min_le_iff]
  by_cases hs : 1 ≤ Real.sqrt (2 * Real.pi) * z
  · right
    have hs0 : 0 < Real.sqrt (2 * Real.pi) * z := lt_of_lt_of_le zero_lt_one hs
    have hE : 0 ≤ Real.exp (-(z ^ 2) / 2) := Real.exp_nonneg _
    rw [div_le_iff₀ hs0]
    nlinarith [hE, hs]
  · left
    have hslt : Real.sqrt (2 * Real.pi) * z < 1 := lt_of_not_ge hs
    have hs2 : (2 : ℝ) ≤ Real.sqrt (2 * Real.pi) := by
      rw [Real.le_sqrt (by norm_num) (by positivity)]
      nlinarith [Real.pi_gt_three]
    have hz2 : z < 1 / 2 := by nlinarith [hs2, hz, hslt]
    have h1 : (1 : ℝ) - z ^ 2 / 2 ≤ Real.exp (-(z ^ 2 / 2)) := Real.one_sub_le_exp_neg (z ^ 2 / 2)
    have h2 : Real.exp (-(z ^ 2 / 2)) = Real.exp (-(z ^ 2) / 2) := by congr 1; ring
    rw [h2] at h1
    nlinarith [h1, hz2]

/-- For `y > 0`, `1/(1 - exp (-y)) ≤ 1 + 1/y`. -/
theorem inv_one_sub_exp_neg_le (y : ℝ) (hy : 0 < y) :
    1 / (1 - Real.exp (-y)) ≤ 1 + 1 / y := by
  have h1 : Real.exp (-y) ≤ 1 / (1 + y) := by
    have := Commons.Analysis.Exponential.exp_le_one_div_one_sub (t := -y) (by linarith)
    simpa using this
  have hpos : 0 < y / (1 + y) := by positivity
  have h2 : y / (1 + y) ≤ 1 - Real.exp (-y) := by
    have h3 : y / (1 + y) = 1 - 1 / (1 + y) := by
      field_simp
      ring
    rw [h3]
    linarith
  calc 1 / (1 - Real.exp (-y)) ≤ 1 / (y / (1 + y)) :=
        one_div_le_one_div_of_le hpos h2
    _ = 1 + 1 / y := by
        field_simp
        ring

/-- The key geometric-series estimate: for `c > 0` and `K ≥ 1`,
`∑_{k=1}^K exp (-c/k) ≤ (1 + K^2/c) * exp (-c/K)`. -/
theorem sum_exp_neg_div_le {c : ℝ} (hc : 0 < c) {K : ℕ} (hK : 1 ≤ K) :
    (∑ k ∈ Finset.Icc 1 K, Real.exp (-(c / (k : ℝ))))
      ≤ (1 + (K : ℝ) ^ 2 / c) * Real.exp (-(c / (K : ℝ))) := by
  have hKpos : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK
  set q : ℝ := Real.exp (-(c / (K : ℝ) ^ 2)) with hq
  have hq0 : 0 ≤ q := le_of_lt (Real.exp_pos _)
  have hq1 : q < 1 := by
    rw [hq, Real.exp_lt_one_iff]
    have : 0 < c / (K : ℝ) ^ 2 := div_pos hc (pow_pos hKpos 2)
    linarith
  have hreindex : (∑ k ∈ Finset.Icc 1 K, q ^ (K - k)) = ∑ j ∈ Finset.range K, q ^ j := by
    refine Finset.sum_bij (fun k _ => K - k) ?_ ?_ ?_ ?_
    · intro k hk
      rw [Finset.mem_range]
      have := (Finset.mem_Icc.mp hk).1
      omega
    · intro k1 hk1 k2 hk2 h
      have h1 := (Finset.mem_Icc.mp hk1).2
      have h2 := (Finset.mem_Icc.mp hk2).2
      omega
    · intro j hj
      refine ⟨K - j, ?_, ?_⟩
      · rw [Finset.mem_Icc]
        have := Finset.mem_range.mp hj
        omega
      · have := Finset.mem_range.mp hj
        omega
    · intro k hk
      rfl
  have hterm : ∀ k ∈ Finset.Icc 1 K,
      Real.exp (-(c / (k : ℝ))) ≤ Real.exp (-(c / (K : ℝ))) * q ^ (K - k) := by
    intro k hk
    have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
    have hkK : k ≤ K := (Finset.mem_Icc.mp hk).2
    have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk1
    have hkn : ((K - k : ℕ) : ℝ) = (K : ℝ) - (k : ℝ) := by rw [Nat.cast_sub hkK]
    have hle : (1 : ℝ) / (K : ℝ) + ((K : ℝ) - (k : ℝ)) / (K : ℝ) ^ 2 ≤ 1 / (k : ℝ) := by
      have hkey : (1 : ℝ) / (k : ℝ) - 1 / (K : ℝ) - ((K : ℝ) - (k : ℝ)) / (K : ℝ) ^ 2
          = ((K : ℝ) - (k : ℝ)) ^ 2 / ((k : ℝ) * (K : ℝ) ^ 2) := by
        field_simp [ne_of_gt hkpos, ne_of_gt hKpos]
      have hnn : 0 ≤ ((K : ℝ) - (k : ℝ)) ^ 2 / ((k : ℝ) * (K : ℝ) ^ 2) := by positivity
      linarith [hkey, hnn]
    have hexp : -(c / (k : ℝ)) ≤ -(c / (K : ℝ)) - ((K - k : ℕ) : ℝ) * (c / (K : ℝ) ^ 2) := by
      rw [hkn]
      have hmul := mul_le_mul_of_nonneg_left hle (le_of_lt hc)
      have h1 : c * (1 / (K : ℝ) + ((K : ℝ) - (k : ℝ)) / (K : ℝ) ^ 2)
          = c / (K : ℝ) + ((K : ℝ) - (k : ℝ)) * (c / (K : ℝ) ^ 2) := by ring
      have h2 : c * (1 / (k : ℝ)) = c / (k : ℝ) := by ring
      rw [h1, h2] at hmul
      linarith [hmul]
    have hfac : Real.exp (-(c / (K : ℝ))) * q ^ (K - k)
        = Real.exp (-(c / (K : ℝ)) + ((K - k : ℕ) : ℝ) * (-(c / (K : ℝ) ^ 2))) := by
      rw [hq, ← Real.exp_nat_mul, ← Real.exp_add]
    rw [hfac]
    apply Real.exp_le_exp.mpr
    have : ((K - k : ℕ) : ℝ) * (-(c / (K : ℝ) ^ 2))
        = - (((K - k : ℕ) : ℝ) * (c / (K : ℝ) ^ 2)) := by ring
    rw [this]
    exact hexp
  have hgeom : (∑ j ∈ Finset.range K, q ^ j) ≤ 1 / (1 - q) :=
    Commons.Analysis.Asymptotics.geom_sum_range_le hq0 hq1 K
  have hfinal : 1 / (1 - q) ≤ 1 + (K : ℝ) ^ 2 / c := by
    rw [hq]
    have hy : 0 < c / (K : ℝ) ^ 2 := div_pos hc (pow_pos hKpos 2)
    have h := inv_one_sub_exp_neg_le (c / (K : ℝ) ^ 2) hy
    have heq : 1 + 1 / (c / (K : ℝ) ^ 2) = 1 + (K : ℝ) ^ 2 / c := by
      field_simp [ne_of_gt hc, ne_of_gt hKpos]
    linarith [h, heq]
  calc (∑ k ∈ Finset.Icc 1 K, Real.exp (-(c / (k : ℝ))))
      ≤ ∑ k ∈ Finset.Icc 1 K, Real.exp (-(c / (K : ℝ))) * q ^ (K - k) :=
        Finset.sum_le_sum hterm
    _ = Real.exp (-(c / (K : ℝ))) * (∑ k ∈ Finset.Icc 1 K, q ^ (K - k)) := by
        rw [Finset.mul_sum]
    _ = Real.exp (-(c / (K : ℝ))) * (∑ j ∈ Finset.range K, q ^ j) := by rw [hreindex]
    _ ≤ Real.exp (-(c / (K : ℝ))) * (1 / (1 - q)) :=
        mul_le_mul_of_nonneg_left hgeom (Real.exp_nonneg _)
    _ ≤ Real.exp (-(c / (K : ℝ))) * (1 + (K : ℝ) ^ 2 / c) :=
        mul_le_mul_of_nonneg_left hfinal (Real.exp_nonneg _)
    _ = (1 + (K : ℝ) ^ 2 / c) * Real.exp (-(c / (K : ℝ))) := by ring

theorem sum_tail_div_sqrt_le {β : ℝ} (hβ : 0 < β) {K : ℕ} (hK : 1 ≤ K) :
    (∑ k ∈ Finset.Icc 1 K,
        (ProbabilityTheory.stdGaussian ℝ).real {z : ℝ | β / Real.sqrt (k : ℝ) ≤ z})
      ≤ (4 * (K : ℝ) ^ 2 / β ^ 2 + 1) * Real.exp (-(β ^ 2) / (2 * (K : ℝ))) := by
  have hc : 0 < β ^ 2 / 2 := by positivity
  have hterm : ∀ k ∈ Finset.Icc 1 K,
      (ProbabilityTheory.stdGaussian ℝ).real {z : ℝ | β / Real.sqrt (k : ℝ) ≤ z}
        ≤ Real.exp (-((β ^ 2 / 2) / (k : ℝ))) := by
    intro k hk
    have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
    have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk1
    have hz : 0 < β / Real.sqrt (k : ℝ) := div_pos hβ (Real.sqrt_pos_of_pos hkpos)
    refine le_trans (stdGaussian_real_tail_le_exp (β / Real.sqrt (k : ℝ)) hz) (le_of_eq ?_)
    congr 1
    rw [div_pow, Real.sq_sqrt (le_of_lt hkpos)]
    field_simp [ne_of_gt hkpos]
  have hKsq : (K : ℝ) ^ 2 / (β ^ 2 / 2) = 2 * (K : ℝ) ^ 2 / β ^ 2 := by
    field_simp [ne_of_gt hβ]
  have hexp : Real.exp (-((β ^ 2 / 2) / (K : ℝ))) = Real.exp (-(β ^ 2) / (2 * (K : ℝ))) := by
    congr 1
    field_simp [ne_of_gt hβ]
  calc (∑ k ∈ Finset.Icc 1 K,
        (ProbabilityTheory.stdGaussian ℝ).real {z : ℝ | β / Real.sqrt (k : ℝ) ≤ z})
      ≤ ∑ k ∈ Finset.Icc 1 K, Real.exp (-((β ^ 2 / 2) / (k : ℝ))) := Finset.sum_le_sum hterm
    _ ≤ (1 + (K : ℝ) ^ 2 / (β ^ 2 / 2)) * Real.exp (-((β ^ 2 / 2) / (K : ℝ))) :=
        sum_exp_neg_div_le hc hK
    _ = (1 + 2 * (K : ℝ) ^ 2 / β ^ 2) * Real.exp (-(β ^ 2) / (2 * (K : ℝ))) := by
        rw [hKsq, hexp]
    _ ≤ (4 * (K : ℝ) ^ 2 / β ^ 2 + 1) * Real.exp (-(β ^ 2) / (2 * (K : ℝ))) := by
        apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
        have hA : (0 : ℝ) ≤ (K : ℝ) ^ 2 / β ^ 2 := by positivity
        have h2 : 2 * (K : ℝ) ^ 2 / β ^ 2 ≤ 4 * (K : ℝ) ^ 2 / β ^ 2 := by
          calc 2 * (K : ℝ) ^ 2 / β ^ 2 = 2 * ((K : ℝ) ^ 2 / β ^ 2) := by ring
            _ ≤ 4 * ((K : ℝ) ^ 2 / β ^ 2) := mul_le_mul_of_nonneg_right (by norm_num) hA
            _ = 4 * (K : ℝ) ^ 2 / β ^ 2 := by ring
        linarith

end Commons.Probability.Gaussian
