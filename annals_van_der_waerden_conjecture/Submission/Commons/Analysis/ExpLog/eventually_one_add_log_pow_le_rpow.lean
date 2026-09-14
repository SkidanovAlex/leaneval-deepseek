import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace Commons.Analysis.ExpLog

open Filter

/-- For any real exponent `a > 0` and any constant `c`, eventually `c ≤ H ^ a` along `H : ℕ`. -/
lemma eventually_natCast_rpow_atTop_ge (c a : ℝ) (ha : 0 < a) :
    ∀ᶠ H : ℕ in Filter.atTop, c ≤ (H : ℝ) ^ a := by
  have h : Tendsto (fun H : ℕ => (H : ℝ) ^ a) Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop ha).comp tendsto_natCast_atTop_atTop
  exact h.eventually_ge_atTop c

/-- `log` grows slower than any positive power, along `H : ℕ`. -/
lemma eventually_log_natCast_le_rpow (a : ℝ) (ha : 0 < a) :
    ∀ᶠ H : ℕ in Filter.atTop, Real.log (H : ℝ) ≤ (H : ℝ) ^ a := by
  have h := (isLittleO_log_rpow_atTop ha).eventuallyLE
  have h' : ∀ᶠ x : ℝ in Filter.atTop, Real.log x ≤ x ^ a := by
    filter_upwards [h, eventually_ge_atTop (1 : ℝ)] with x hx hx1
    rwa [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg hx1),
      abs_of_nonneg (Real.rpow_nonneg (le_trans zero_le_one hx1) a)] at hx
  exact tendsto_natCast_atTop_atTop.eventually h'

theorem eventually_one_add_log_pow_le_rpow (K M : ℕ) (s : ℝ) (hs : 0 < s) :
    ∀ᶠ H : ℕ in Filter.atTop, (1 + Real.log ((H : ℝ) ^ M)) ^ K ≤ (H : ℝ) ^ s := by
  by_cases hK : K = 0
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with H hH
    rw [hK, pow_zero]
    exact Real.one_le_rpow (by exact_mod_cast hH) (le_of_lt hs)
  · have hKpos : (0 : ℝ) < (K : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero hK
    set b : ℝ := s / (2 * (K : ℝ)) with hb
    have hbpos : 0 < b := by
      rw [hb]; exact div_pos hs (by linarith)
    have hbK : b * (K : ℝ) = s / 2 := by
      rw [hb]; field_simp
    have hlog : ∀ᶠ H : ℕ in Filter.atTop, Real.log (H : ℝ) ≤ (H : ℝ) ^ b :=
      eventually_log_natCast_le_rpow b hbpos
    have h1b : ∀ᶠ H : ℕ in Filter.atTop, (1 : ℝ) ≤ (H : ℝ) ^ b :=
      eventually_natCast_rpow_atTop_ge 1 b hbpos
    have hconst : ∀ᶠ H : ℕ in Filter.atTop, ((M : ℝ) + 1) ^ K ≤ (H : ℝ) ^ (s / 2) :=
      eventually_natCast_rpow_atTop_ge (((M : ℝ) + 1) ^ K) (s / 2) (by linarith)
    filter_upwards [hlog, h1b, hconst, eventually_ge_atTop (1 : ℕ)] with H hlogH h1H hconstH hH
    have hH1 : (1 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH
    have hH0 : (0 : ℝ) ≤ (H : ℝ) := le_trans zero_le_one hH1
    have hlogH0 : 0 ≤ Real.log (H : ℝ) := Real.log_nonneg hH1
    rw [Real.log_pow]
    have hbase_nonneg : 0 ≤ 1 + (M : ℝ) * Real.log (H : ℝ) := by
      have : 0 ≤ (M : ℝ) * Real.log (H : ℝ) := mul_nonneg (Nat.cast_nonneg M) hlogH0
      linarith
    have hstep : 1 + (M : ℝ) * Real.log (H : ℝ) ≤ ((M : ℝ) + 1) * (H : ℝ) ^ b := by
      have h1 : (M : ℝ) * Real.log (H : ℝ) ≤ (M : ℝ) * (H : ℝ) ^ b :=
        mul_le_mul_of_nonneg_left hlogH (Nat.cast_nonneg M)
      nlinarith [h1, h1H]
    have hpow : (1 + (M : ℝ) * Real.log (H : ℝ)) ^ K ≤ (((M : ℝ) + 1) * (H : ℝ) ^ b) ^ K :=
      pow_le_pow_left₀ hbase_nonneg hstep K
    have hHbK : ((H : ℝ) ^ b) ^ K = (H : ℝ) ^ (s / 2) := by
      rw [← Real.rpow_natCast ((H : ℝ) ^ b) K, ← Real.rpow_mul hH0 b (K : ℝ), hbK]
    calc
      (1 + (M : ℝ) * Real.log (H : ℝ)) ^ K
          ≤ (((M : ℝ) + 1) * (H : ℝ) ^ b) ^ K := hpow
      _ = ((M : ℝ) + 1) ^ K * (H : ℝ) ^ (s / 2) := by rw [mul_pow, hHbK]
      _ ≤ (H : ℝ) ^ (s / 2) * (H : ℝ) ^ (s / 2) :=
            mul_le_mul_of_nonneg_right hconstH (Real.rpow_nonneg hH0 (s / 2))
      _ = (H : ℝ) ^ s := by
            rw [← Real.rpow_add (by linarith : (0 : ℝ) < (H : ℝ)),
              show s / 2 + s / 2 = s by ring]

end Commons.Analysis.ExpLog