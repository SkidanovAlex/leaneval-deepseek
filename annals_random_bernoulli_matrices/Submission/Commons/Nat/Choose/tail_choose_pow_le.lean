import Mathlib.Analysis.Complex.Exponential

namespace Commons.Nat.Choose

open Finset

/-- Binomial lower-tail bound: `Σ_{ℓ ≤ r} C(m,ℓ) ≤ (e·m/r)^r` for `0 < r ≤ m`. -/
lemma sum_choose_lower_le (m r : ℕ) (hr : 0 < r) (hrm : r ≤ m) :
    (∑ ℓ ∈ Finset.range (r + 1), (m.choose ℓ : ℝ)) ≤
      (Real.exp 1 * (m : ℝ) / (r : ℝ)) ^ r := by
  let e : ℝ := Real.exp 1
  let S : ℝ := ∑ ℓ ∈ Finset.range (r + 1), (m.choose ℓ : ℝ)
  let q : ℝ := (r : ℝ) / (m : ℝ)
  have mpos : 0 < m := lt_of_lt_of_le hr hrm
  have hmc : (0 : ℝ) < (m : ℝ) := by exact_mod_cast mpos
  have hrc : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  have hm0 : (m : ℝ) ≠ 0 := ne_of_gt hmc
  have hr0 : (r : ℝ) ≠ 0 := ne_of_gt hrc
  have hqpos : 0 < q := by
    dsimp [q]
    exact div_pos hrc hmc
  have hqge0 : 0 ≤ q := le_of_lt hqpos
  have hqle1 : q ≤ 1 := by
    dsimp [q]
    rw [div_le_iff₀ hmc]
    simpa using (Nat.cast_le.mpr hrm : (r : ℝ) ≤ (m : ℝ))
  have hmq : (m : ℝ) * q = (r : ℝ) := by
    dsimp [q]
    field_simp [hm0]
  -- q^r ≤ q^ℓ for ℓ ≤ r
  have hqrle {ℓ : ℕ} (hℓ : ℓ ≤ r) : q ^ r ≤ q ^ ℓ := by
    have hrℓ : r = ℓ + (r - ℓ) := by omega
    calc
      q ^ r = q ^ (ℓ + (r - ℓ)) := by rw [← hrℓ]
      _ = q ^ ℓ * q ^ (r - ℓ) := by rw [pow_add]
      _ ≤ q ^ ℓ * 1 := by
        exact mul_le_mul_of_nonneg_left (pow_le_one₀ hqge0 hqle1) (pow_nonneg hqge0 ℓ)
      _ = q ^ ℓ := by rw [mul_one]
  -- binomial identity: Σ_{ℓ ≤ m} C(m,ℓ) q^ℓ = (1+q)^m
  have hbin : (∑ ℓ ∈ Finset.range (m + 1), (m.choose ℓ : ℝ) * q ^ ℓ) = (1 + q) ^ m := by
    calc
      (∑ ℓ ∈ Finset.range (m + 1), (m.choose ℓ : ℝ) * q ^ ℓ)
          = ∑ ℓ ∈ Finset.range (m + 1), q ^ ℓ * 1 ^ (m - ℓ) * (m.choose ℓ : ℝ) := by
            apply Finset.sum_congr rfl
            intro ℓ hℓ
            rw [one_pow]
            ring
      _ = (q + 1) ^ m := (add_pow q (1 : ℝ) m).symm
      _ = (1 + q) ^ m := by
        congr 1
        ring
  -- Part A: q^r · S ≤ (1+q)^m
  have hA : q ^ r * S ≤ (1 + q) ^ m := by
    calc
      q ^ r * S = ∑ ℓ ∈ Finset.range (r + 1), (m.choose ℓ : ℝ) * q ^ r := by
        dsimp [S]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro ℓ hℓ
        ring
      _ ≤ ∑ ℓ ∈ Finset.range (r + 1), (m.choose ℓ : ℝ) * q ^ ℓ := by
        apply Finset.sum_le_sum
        intro ℓ hℓ
        exact mul_le_mul_of_nonneg_left
          (hqrle (Nat.lt_succ_iff.mp (mem_range.mp hℓ))) (Nat.cast_nonneg _)
      _ ≤ ∑ ℓ ∈ Finset.range (m + 1), (m.choose ℓ : ℝ) * q ^ ℓ := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · rw [Finset.range_subset]
          intro ℓ hℓ
          rw [Finset.mem_range]
          omega
        · intro ℓ hℓ hnot
          exact mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hqge0 ℓ)
      _ = (1 + q) ^ m := hbin
  -- Part B: (1+q)^m ≤ e^r
  have h1q : 1 + q ≤ Real.exp q := by
    simpa [add_comm] using (Real.add_one_le_exp q)
  have hB : (1 + q) ^ m ≤ e ^ r := by
    calc
      (1 + q) ^ m ≤ (Real.exp q) ^ m := by
        exact pow_le_pow_left₀ (by positivity) h1q m
      _ = Real.exp ((m : ℝ) * q) := (Real.exp_nat_mul q m).symm
      _ = Real.exp ((r : ℝ)) := by rw [hmq]
      _ = (Real.exp 1) ^ r := by
        rw [← Real.exp_nat_mul 1 r]
        simp
  -- conclude: S ≤ (e·m/r)^r
  have hC : S * q ^ r ≤ e ^ r := by
    calc
      S * q ^ r = q ^ r * S := by ring
      _ ≤ (1 + q) ^ m := hA
      _ ≤ e ^ r := hB
  have hqpowpos : 0 < q ^ r := pow_pos hqpos r
  have hdiv : e ^ r / q ^ r = (e * (m : ℝ) / (r : ℝ)) ^ r := by
    rw [← div_pow]
    congr 1
    dsimp [q]
    field_simp [hm0, hr0]
  have hfin : S ≤ e ^ r / q ^ r := (le_div_iff₀ hqpowpos).2 hC
  calc
    S ≤ e ^ r / q ^ r := hfin
    _ = (e * (m : ℝ) / (r : ℝ)) ^ r := hdiv

/-- For `0 ≤ τ ≤ 1`, `ℓ ≤ r ≤ m` we have `τ^(m-ℓ) ≤ τ^(m-r)`. -/
lemma tau_pow_sub_le {m r : ℕ} {τ : ℝ} (hrm : r ≤ m) {ℓ : ℕ} (hℓ : ℓ ≤ r)
    (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) : τ ^ (m - ℓ) ≤ τ ^ (m - r) := by
  have hsub : m - ℓ = (m - r) + (r - ℓ) := by omega
  calc
    τ ^ (m - ℓ) = τ ^ ((m - r) + (r - ℓ)) := by rw [hsub]
    _ = τ ^ (m - r) * τ ^ (r - ℓ) := by rw [pow_add]
    _ ≤ τ ^ (m - r) * 1 := by
      exact mul_le_mul_of_nonneg_left (pow_le_one₀ hτ0 hτ1) (pow_nonneg hτ0 (m - r))
    _ = τ ^ (m - r) := by rw [mul_one]

theorem tail_choose_pow_le {m r : ℕ} (hr : 0 < r) (hrm : r ≤ m) {τ : ℝ}
    (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) :
    (∑ ℓ ∈ Finset.range (r + 1), (m.choose ℓ : ℝ) * τ ^ (m - ℓ)) ≤
      (Real.exp 1 * (m : ℝ) / (r : ℝ)) ^ r * τ ^ (m - r) := by
  have hS : (∑ ℓ ∈ Finset.range (r + 1), (m.choose ℓ : ℝ)) ≤
      (Real.exp 1 * (m : ℝ) / (r : ℝ)) ^ r := sum_choose_lower_le m r hr hrm
  calc
    (∑ ℓ ∈ Finset.range (r + 1), (m.choose ℓ : ℝ) * τ ^ (m - ℓ))
        ≤ ∑ ℓ ∈ Finset.range (r + 1), (m.choose ℓ : ℝ) * τ ^ (m - r) := by
          apply Finset.sum_le_sum
          intro ℓ hℓ
          exact mul_le_mul_of_nonneg_left
            (tau_pow_sub_le hrm (Nat.lt_succ_iff.mp (mem_range.mp hℓ)) hτ0 hτ1)
            (Nat.cast_nonneg _)
    _ = (∑ ℓ ∈ Finset.range (r + 1), (m.choose ℓ : ℝ)) * τ ^ (m - r) := by
          rw [Finset.sum_mul]
    _ ≤ (Real.exp 1 * (m : ℝ) / (r : ℝ)) ^ r * τ ^ (m - r) := by
          exact mul_le_mul_of_nonneg_right hS (pow_nonneg hτ0 (m - r))

end Commons.Nat.Choose