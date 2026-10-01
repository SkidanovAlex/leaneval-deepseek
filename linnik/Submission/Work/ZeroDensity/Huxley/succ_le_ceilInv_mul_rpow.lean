import Mathlib

namespace Work.ZeroDensity.Huxley

/-- For every `x ≥ 2` and every `a ≥ 0`: `a + 1 ≤ ⌈1/δ⌉ · x^{δa}`, uniformly in `x` and `a`.
Proof idea: with `k = ⌈1/δ⌉₊` (so `kδ ≥ 1`) write `a = k*q + r` with `r < k`; then
`a + 1 ≤ k*(q+1) ≤ k*2^q` (`Nat.lt_two_pow_self`) and `x^{aδ} = (x^{kδ})^q * x^{rδ} ≥ 2^q * 1 = 2^q`
because `x^{kδ} ≥ 2^{kδ} ≥ 2^1 = 2` and `x^{rδ} ≥ 1`. -/
lemma succ_le_ceilInv_mul_rpow {δ : ℝ} (hδ : 0 < δ) (x a : ℕ) (hx : 2 ≤ x) :
    (a : ℝ) + 1 ≤ (⌈(1 : ℝ) / δ⌉₊ : ℝ) * (x : ℝ) ^ ((a : ℝ) * δ) := by
  set k : ℕ := ⌈(1 : ℝ) / δ⌉₊ with hk
  have hkpos : 0 < k := by
    rw [hk]; exact Nat.ceil_pos.mpr (one_div_pos.mpr hδ)
  have hkr : (1 : ℝ) ≤ (k : ℝ) * δ := by
    have h1 : (1 : ℝ) / δ ≤ (k : ℝ) := by
      rw [hk]; exact Nat.le_ceil _
    have h2 := mul_le_mul_of_nonneg_right h1 (le_of_lt hδ)
    rwa [div_mul_cancel₀ _ (ne_of_gt hδ)] at h2
  have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have hx2 : (2 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
  have hxpos : (0 : ℝ) < (x : ℝ) := by linarith
  have hx1 : (1 : ℝ) ≤ (x : ℝ) := by linarith
  obtain ⟨q, r, hr, ha⟩ : ∃ q r : ℕ, r < k ∧ a = k * q + r :=
    ⟨a / k, a % k, Nat.mod_lt a hkpos, (Nat.div_add_mod a k).symm⟩
  have hA : (2 : ℝ) ^ q ≤ (x : ℝ) ^ ((a : ℝ) * δ) := by
    have he : (k : ℝ) * δ * (q : ℝ) + (r : ℝ) * δ = (a : ℝ) * δ := by
      rw [ha]; push_cast; ring
    rw [← he, Real.rpow_add hxpos, Real.rpow_mul (le_of_lt hxpos), Real.rpow_natCast]
    have hxe : (2 : ℝ) ≤ (x : ℝ) ^ ((k : ℝ) * δ) := by
      have h1 : (2 : ℝ) ^ ((k : ℝ) * δ) ≤ (x : ℝ) ^ ((k : ℝ) * δ) :=
        Real.rpow_le_rpow (by norm_num) hx2 (le_trans (by norm_num) hkr)
      have h2 : (2 : ℝ) ≤ (2 : ℝ) ^ ((k : ℝ) * δ) := by
        have h3 := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hkr
        simpa using h3
      linarith
    have hpow : (2 : ℝ) ^ q ≤ ((x : ℝ) ^ ((k : ℝ) * δ)) ^ q :=
      pow_le_pow_left₀ (by norm_num) hxe q
    have hle1 : (1 : ℝ) ≤ (x : ℝ) ^ ((r : ℝ) * δ) :=
      Real.one_le_rpow hx1 (by positivity)
    exact le_trans hpow (le_mul_of_one_le_right (by positivity) hle1)
  have ha1 : (a : ℝ) + 1 ≤ (k : ℝ) * ((q : ℝ) + 1) := by
    have hnat : a + 1 ≤ k * (q + 1) := by
      rw [ha, Nat.mul_add, Nat.mul_one]
      omega
    exact_mod_cast hnat
  have hq : (q : ℝ) + 1 ≤ (2 : ℝ) ^ q := by
    have h := Nat.lt_two_pow_self (n := q)
    have hnat : q + 1 ≤ 2 ^ q := Nat.succ_le_iff.mpr h
    exact_mod_cast hnat
  calc (a : ℝ) + 1 ≤ (k : ℝ) * ((q : ℝ) + 1) := ha1
    _ ≤ (k : ℝ) * (2 : ℝ) ^ q := mul_le_mul_of_nonneg_left hq hk0
    _ ≤ (k : ℝ) * (x : ℝ) ^ ((a : ℝ) * δ) := mul_le_mul_of_nonneg_left hA hk0

end Work.ZeroDensity.Huxley
