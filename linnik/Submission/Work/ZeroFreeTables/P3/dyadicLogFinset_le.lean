import Mathlib

namespace Work.ZeroFreeTables.P3

/-- Finite-sum form of the dyadic logarithm estimate used in the Heath–Brown
zero-free-region argument.

For `R ≥ 2`, `L ≥ 0` and any finite set `T` of exponents,

`∑_{k ∈ T} 2^{-k} (log(2^{k+1} R + 2) + L) ≤ 4 (log(R + 2) + L + 1)`.

The estimate follows by bounding `log(2^{k+1} R + 2) ≤ (k+1) log 2 + log(R+2)`
pointwise and then using the exact values `∑ 2^{-k}(k+1) = 4` and `∑ 2^{-k} = 2`
of the corresponding infinite series, together with `Finset.sum_le_tsum`. -/
theorem dyadicLogFinset_le (R L : ℝ) (hR : 2 ≤ R) (hL : 0 ≤ L) (T : Finset ℕ) :
    (∑ k ∈ T, (1 / 2 : ℝ) ^ k * (Real.log ((2 : ℝ) ^ (k + 1) * R + 2) + L))
      ≤ 4 * (Real.log (R + 2) + L + 1) := by
  have hRpos : 0 < R := by linarith
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hc : 0 ≤ Real.log (R + 2) + L := by
    have h1 : (1 : ℝ) ≤ R + 2 := by linarith
    have := Real.log_nonneg h1
    linarith
  have hxnorm : ‖(1 / 2 : ℝ)‖ < 1 := by norm_num
  have hs1 : Summable (fun k : ℕ => (k : ℝ) * (1 / 2 : ℝ) ^ k) :=
    (hasSum_coe_mul_geometric_of_norm_lt_one hxnorm).summable
  have hs2 : Summable (fun k : ℕ => (1 / 2 : ℝ) ^ k) :=
    summable_geometric_of_norm_lt_one hxnorm
  have hg1 : Summable (fun k : ℕ => (1 / 2 : ℝ) ^ k * ((k : ℝ) + 1)) := by
    refine (hs1.add hs2).congr ?_
    intro k; ring
  have htsum_geo : (∑' k : ℕ, (1 / 2 : ℝ) ^ k) = 2 := by
    rw [tsum_geometric_of_norm_lt_one hxnorm]; norm_num
  have hA : (∑' k : ℕ, (1 / 2 : ℝ) ^ k * ((k : ℝ) + 1)) = 4 := by
    have hcongr : (fun k : ℕ => (1 / 2 : ℝ) ^ k * ((k : ℝ) + 1))
        = fun k : ℕ => (k : ℝ) * (1 / 2 : ℝ) ^ k + (1 / 2 : ℝ) ^ k := by
      funext k; ring
    rw [hcongr, Summable.tsum_add hs1 hs2,
      tsum_coe_mul_geometric_of_norm_lt_one hxnorm, htsum_geo]
    norm_num
  have hterm : ∀ k : ℕ, (1 / 2 : ℝ) ^ k * (Real.log ((2 : ℝ) ^ (k + 1) * R + 2) + L)
      ≤ (1 / 2 : ℝ) ^ k * ((k : ℝ) + 1) * Real.log 2
          + (1 / 2 : ℝ) ^ k * (Real.log (R + 2) + L) := by
    intro k
    have hxk : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ k := pow_nonneg (by norm_num) k
    have hpowpos : (0 : ℝ) < (2 : ℝ) ^ (k + 1) := pow_pos (by norm_num) _
    have hp : (1 : ℝ) ≤ (2 : ℝ) ^ (k + 1) := one_le_pow₀ (by norm_num) (n := k + 1)
    have h2le : (2 : ℝ) ≤ (2 : ℝ) ^ (k + 1) * 2 := by nlinarith [hp]
    have hle' : (2 : ℝ) ^ (k + 1) * R + 2 ≤ (2 : ℝ) ^ (k + 1) * (R + 2) := by
      have hfirst : (2 : ℝ) ^ (k + 1) * R + 2
          ≤ (2 : ℝ) ^ (k + 1) * R + (2 : ℝ) ^ (k + 1) * 2 := by linarith [h2le]
      have h2 : (2 : ℝ) ^ (k + 1) * R + (2 : ℝ) ^ (k + 1) * 2
          = (2 : ℝ) ^ (k + 1) * (R + 2) := by ring
      linarith [hfirst, h2]
    have hpos1 : (0 : ℝ) < (2 : ℝ) ^ (k + 1) * R + 2 := by
      have := mul_pos hpowpos hRpos; linarith
    have hlogbound : Real.log ((2 : ℝ) ^ (k + 1) * R + 2)
        ≤ ((k : ℝ) + 1) * Real.log 2 + Real.log (R + 2) := by
      calc Real.log ((2 : ℝ) ^ (k + 1) * R + 2)
          ≤ Real.log ((2 : ℝ) ^ (k + 1) * (R + 2)) := Real.log_le_log hpos1 hle'
        _ = Real.log ((2 : ℝ) ^ (k + 1)) + Real.log (R + 2) :=
              Real.log_mul (pow_ne_zero _ (by norm_num)) (by linarith : R + 2 ≠ 0)
        _ = ((k : ℝ) + 1) * Real.log 2 + Real.log (R + 2) := by
              rw [Real.log_pow]; push_cast; ring
    have hstep := mul_le_mul_of_nonneg_left hlogbound hxk
    calc (1 / 2 : ℝ) ^ k * (Real.log ((2 : ℝ) ^ (k + 1) * R + 2) + L)
        = (1 / 2 : ℝ) ^ k * Real.log ((2 : ℝ) ^ (k + 1) * R + 2)
            + (1 / 2 : ℝ) ^ k * L := by ring
      _ ≤ (1 / 2 : ℝ) ^ k * (((k : ℝ) + 1) * Real.log 2 + Real.log (R + 2))
            + (1 / 2 : ℝ) ^ k * L := by linarith [hstep]
      _ = (1 / 2 : ℝ) ^ k * ((k : ℝ) + 1) * Real.log 2
            + (1 / 2 : ℝ) ^ k * (Real.log (R + 2) + L) := by ring
  have hgsplit :
      (∑ k ∈ T, ((1 / 2 : ℝ) ^ k * ((k : ℝ) + 1) * Real.log 2
          + (1 / 2 : ℝ) ^ k * (Real.log (R + 2) + L)))
      = Real.log 2 * (∑ k ∈ T, (1 / 2 : ℝ) ^ k * ((k : ℝ) + 1))
          + (Real.log (R + 2) + L) * (∑ k ∈ T, (1 / 2 : ℝ) ^ k) := by
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul]
    ring
  have hA_sum : (∑ k ∈ T, (1 / 2 : ℝ) ^ k * ((k : ℝ) + 1)) ≤ 4 := by
    have h := hg1.sum_le_tsum T (fun k _ => mul_nonneg (pow_nonneg (by norm_num) k) (by positivity))
    rwa [hA] at h
  have hB_sum : (∑ k ∈ T, (1 / 2 : ℝ) ^ k) ≤ 2 := by
    have h := hs2.sum_le_tsum T (fun k _ => pow_nonneg (by norm_num) k)
    rwa [htsum_geo] at h
  have hlog2le : 4 * Real.log 2 ≤ 4 := by
    have h := Real.log_le_sub_one_of_pos (show (0:ℝ) < 2 by norm_num)
    linarith
  calc (∑ k ∈ T, (1 / 2 : ℝ) ^ k * (Real.log ((2 : ℝ) ^ (k + 1) * R + 2) + L))
      ≤ ∑ k ∈ T, ((1 / 2 : ℝ) ^ k * ((k : ℝ) + 1) * Real.log 2
          + (1 / 2 : ℝ) ^ k * (Real.log (R + 2) + L)) :=
        Finset.sum_le_sum (fun k _ => hterm k)
    _ = Real.log 2 * (∑ k ∈ T, (1 / 2 : ℝ) ^ k * ((k : ℝ) + 1))
          + (Real.log (R + 2) + L) * (∑ k ∈ T, (1 / 2 : ℝ) ^ k) := hgsplit
    _ ≤ Real.log 2 * 4 + (Real.log (R + 2) + L) * 2 := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_left hA_sum (le_of_lt hlog2pos)
        · exact mul_le_mul_of_nonneg_left hB_sum hc
    _ ≤ 4 * (Real.log (R + 2) + L + 1) := by linarith [hlog2le, hc]

end Work.ZeroFreeTables.P3
