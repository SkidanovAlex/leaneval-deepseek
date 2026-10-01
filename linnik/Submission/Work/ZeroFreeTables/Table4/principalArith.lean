import Mathlib

namespace Work.ZeroFreeTables.Table4

open Filter
open scoped Topology

/-- For `k ≥ 1`, `c / x ^ k → 0` as `x → +∞`. -/
lemma principalArith_const_div_pow (c : ℝ) {k : ℕ} (hk : 1 ≤ k) :
    Tendsto (fun L : ℝ => c / L ^ k) atTop (𝓝 0) := by
  have hL : Tendsto (fun L : ℝ => L⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have h0 : (0 : ℝ) ^ k = 0 := zero_pow (by omega)
  have h := (hL.pow k).const_mul c
  rw [h0, mul_zero] at h
  refine h.congr' (Eventually.of_forall fun L => ?_)
  show c * L⁻¹ ^ k = c / L ^ k
  rw [div_eq_mul_inv, inv_pow]

/-- `(log x)^n / x^m → 0` for `m ≥ 1`. -/
lemma principalArith_log_pow_div_pow (n m : ℕ) (hm : 1 ≤ m) :
    Tendsto (fun x : ℝ => Real.log x ^ n / x ^ m) atTop (𝓝 0) := by
  have hmain : Tendsto (fun x : ℝ => Real.log x ^ n / x) atTop (𝓝 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 n one_ne_zero
  rcases eq_or_lt_of_le hm with h | h
  · subst h
    simpa using hmain
  · have hpow : Tendsto (fun x : ℝ => 1 / x ^ (m - 1)) atTop (𝓝 0) :=
      principalArith_const_div_pow 1 (k := m - 1) (by omega)
    have hprod : Tendsto (fun x : ℝ => (Real.log x ^ n / x) * (1 / x ^ (m - 1)))
        atTop (𝓝 0) := by
      simpa using hmain.mul hpow
    refine hprod.congr' (Eventually.of_forall fun x => ?_)
    have hx : x ^ m = x * x ^ (m - 1) := by
      conv_lhs => rw [← Nat.sub_add_cancel hm]
      rw [pow_succ, mul_comm]
    show (Real.log x ^ n / x) * (1 / x ^ (m - 1)) = Real.log x ^ n / x ^ m
    rw [hx, div_mul_div_comm, mul_one]

/-- `(log x + 2)^n / x^m → 0` for `m ≥ 1`. -/
lemma principalArith_log_add_pow_div_pow (n m : ℕ) (hm : 1 ≤ m) :
    Tendsto (fun x : ℝ => (Real.log x + 2) ^ n / x ^ m) atTop (𝓝 0) := by
  have hg : Tendsto (fun x : ℝ => 2 ^ n * (Real.log x ^ n / x ^ m)) atTop (𝓝 0) := by
    simpa using (principalArith_log_pow_div_pow n m hm).const_mul (2 ^ n : ℝ)
  refine squeeze_zero' ?_ ?_ hg
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    have hlog : 0 ≤ Real.log x := Real.log_nonneg hx
    have hnum : 0 ≤ (Real.log x + 2) ^ n := pow_nonneg (by linarith) n
    have hden : 0 < x ^ m := pow_pos (lt_of_lt_of_le zero_lt_one hx) m
    exact div_nonneg hnum hden.le
  · filter_upwards [eventually_ge_atTop (Real.exp 2)] with x hx
    have hxpos : 0 < x := lt_of_lt_of_le (Real.exp_pos 2) hx
    have hlog2 : 2 ≤ Real.log x := by
      have h := Real.log_le_log (Real.exp_pos 2) hx
      rwa [Real.log_exp] at h
    have hpos : 0 ≤ Real.log x + 2 := by linarith
    have hle : Real.log x + 2 ≤ 2 * Real.log x := by linarith
    have hpow : (Real.log x + 2) ^ n ≤ 2 ^ n * Real.log x ^ n := by
      calc (Real.log x + 2) ^ n ≤ (2 * Real.log x) ^ n := pow_le_pow_left₀ hpos hle n
        _ = 2 ^ n * Real.log x ^ n := by rw [mul_pow]
    show (Real.log x + 2) ^ n / x ^ m ≤ 2 ^ n * (Real.log x ^ n / x ^ m)
    calc (Real.log x + 2) ^ n / x ^ m ≤ (2 ^ n * Real.log x ^ n) / x ^ m :=
          div_le_div_of_nonneg_right hpow (pow_pos hxpos m).le
      _ = 2 ^ n * (Real.log x ^ n / x ^ m) := by rw [mul_div_assoc]

theorem principalArith (M0 C A ε : ℝ) (hM0 : 0 < M0) (hC : 0 < C) (hA : 0 ≤ A) (hε : 0 < ε) :
    ∃ L₀ : ℝ, 1 ≤ L₀ ∧ ∀ L : ℝ, L₀ ≤ L →
      M0 * (1 + A / L + A ^ 2 / (3 * L ^ 2)) / L + 2 * C * (Real.log L + 2) ^ 2 / L
        + 4 * A * C * (Real.log L + 2) ^ 3 / L ^ 2
        + (16 / 3) * A ^ 2 * C * (Real.log L + 2) ^ 4 / L ^ 3 ≤ ε := by
  have hAL : Tendsto (fun L : ℝ => A / L) atTop (𝓝 0) := by
    simpa using principalArith_const_div_pow A (k := 1) (by norm_num)
  have hAL2 : Tendsto (fun L : ℝ => A ^ 2 / (3 * L ^ 2)) atTop (𝓝 0) := by
    have h := principalArith_const_div_pow (A ^ 2 / 3) (k := 2) (by norm_num)
    refine h.congr' (Eventually.of_forall fun L => ?_)
    show (A ^ 2 / 3) / L ^ 2 = A ^ 2 / (3 * L ^ 2)
    rw [div_div]
  have hP : Tendsto (fun L : ℝ => 1 + A / L + A ^ 2 / (3 * L ^ 2)) atTop (𝓝 1) := by
    have h : Tendsto (fun L : ℝ => 1 + A / L + A ^ 2 / (3 * L ^ 2)) atTop (𝓝 (1 + 0 + 0)) :=
      ((tendsto_const_nhds (x := (1 : ℝ)) (f := atTop)).add hAL).add hAL2
    simpa using h
  have hL1 : Tendsto (fun L : ℝ => (1 : ℝ) / L) atTop (𝓝 0) := by
    simpa using principalArith_const_div_pow (1 : ℝ) (k := 1) (by norm_num)
  have hT1 : Tendsto (fun L : ℝ => M0 * (1 + A / L + A ^ 2 / (3 * L ^ 2)) / L) atTop (𝓝 0) := by
    have h : Tendsto (fun L : ℝ => M0 * ((1 + A / L + A ^ 2 / (3 * L ^ 2)) * (1 / L)))
        atTop (𝓝 0) := by
      simpa using (hP.mul hL1).const_mul M0
    refine h.congr' (Eventually.of_forall fun L => ?_)
    show M0 * ((1 + A / L + A ^ 2 / (3 * L ^ 2)) * (1 / L))
        = M0 * (1 + A / L + A ^ 2 / (3 * L ^ 2)) / L
    ring
  have hT2 : Tendsto (fun L : ℝ => 2 * C * (Real.log L + 2) ^ 2 / L) atTop (𝓝 0) := by
    have h : Tendsto (fun L : ℝ => (2 * C) * ((Real.log L + 2) ^ 2 / L)) atTop (𝓝 0) := by
      simpa using (principalArith_log_add_pow_div_pow 2 1 (by norm_num)).const_mul (2 * C)
    refine h.congr' (Eventually.of_forall fun L => ?_)
    show (2 * C) * ((Real.log L + 2) ^ 2 / L) = 2 * C * (Real.log L + 2) ^ 2 / L
    ring
  have hT3 : Tendsto (fun L : ℝ => 4 * A * C * (Real.log L + 2) ^ 3 / L ^ 2) atTop (𝓝 0) := by
    have h : Tendsto (fun L : ℝ => (4 * A * C) * ((Real.log L + 2) ^ 3 / L ^ 2)) atTop (𝓝 0) := by
      simpa using (principalArith_log_add_pow_div_pow 3 2 (by norm_num)).const_mul (4 * A * C)
    refine h.congr' (Eventually.of_forall fun L => ?_)
    show (4 * A * C) * ((Real.log L + 2) ^ 3 / L ^ 2) = 4 * A * C * (Real.log L + 2) ^ 3 / L ^ 2
    ring
  have hT4 : Tendsto (fun L : ℝ => (16 / 3) * A ^ 2 * C * (Real.log L + 2) ^ 4 / L ^ 3)
      atTop (𝓝 0) := by
    have h : Tendsto (fun L : ℝ => ((16 / 3) * A ^ 2 * C) * ((Real.log L + 2) ^ 4 / L ^ 3))
        atTop (𝓝 0) := by
      simpa using
        (principalArith_log_add_pow_div_pow 4 3 (by norm_num)).const_mul ((16 / 3) * A ^ 2 * C)
    refine h.congr' (Eventually.of_forall fun L => ?_)
    show ((16 / 3) * A ^ 2 * C) * ((Real.log L + 2) ^ 4 / L ^ 3)
        = (16 / 3) * A ^ 2 * C * (Real.log L + 2) ^ 4 / L ^ 3
    ring
  have hsum : Tendsto (fun L : ℝ =>
      M0 * (1 + A / L + A ^ 2 / (3 * L ^ 2)) / L + 2 * C * (Real.log L + 2) ^ 2 / L
        + 4 * A * C * (Real.log L + 2) ^ 3 / L ^ 2
        + (16 / 3) * A ^ 2 * C * (Real.log L + 2) ^ 4 / L ^ 3) atTop (𝓝 0) := by
    simpa using ((hT1.add hT2).add hT3).add hT4
  have hev : ∀ᶠ L in atTop, (M0 * (1 + A / L + A ^ 2 / (3 * L ^ 2)) / L
        + 2 * C * (Real.log L + 2) ^ 2 / L
        + 4 * A * C * (Real.log L + 2) ^ 3 / L ^ 2
        + (16 / 3) * A ^ 2 * C * (Real.log L + 2) ^ 4 / L ^ 3) < ε :=
    hsum.eventually (Iio_mem_nhds hε)
  rw [Filter.eventually_atTop] at hev
  obtain ⟨a, ha⟩ := hev
  exact ⟨max a 1, le_max_right a 1,
    fun L hL => le_of_lt (ha L (le_trans (le_max_left a 1) hL))⟩

end Work.ZeroFreeTables.Table4
