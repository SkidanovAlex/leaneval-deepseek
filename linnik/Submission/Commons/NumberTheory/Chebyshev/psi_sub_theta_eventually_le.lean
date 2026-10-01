import Mathlib
import Submission.Commons.NumberTheory.Chebyshev.lcmUpto_le_three_pow

open Filter

namespace Commons.NumberTheory.Chebyshev

/-- The Chebyshev `ψ`-function is linearly bounded: `ψ t ≤ (log 3) * t` for `t ≥ 0`.
This follows from `ψ n = log (lcm(1,…,n))` and Hanson's bound `lcm(1,…,n) ≤ 3 ^ n`. -/
lemma psi_le_log3_mul_real (t : ℝ) (ht : 0 ≤ t) :
    Chebyshev.psi t ≤ Real.log 3 * t := by
  have hfloor : ((⌊t⌋₊ : ℕ) : ℝ) ≤ t := Nat.floor_le ht
  have hlog3 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  calc Chebyshev.psi t = Chebyshev.psi ((⌊t⌋₊ : ℕ) : ℝ) := Chebyshev.psi_eq_psi_coe_floor t
    _ = Real.log ((⌊t⌋₊).lcmUpto : ℝ) := Chebyshev.psi_eq_log_lcmUpto ⌊t⌋₊
    _ ≤ Real.log (((3 : ℕ) ^ ⌊t⌋₊ : ℕ) : ℝ) := by
          apply Real.log_le_log
          · exact_mod_cast Nat.lcmUpto_pos ⌊t⌋₊
          · exact_mod_cast lcmUpto_le_three_pow ⌊t⌋₊
    _ = Real.log 3 * ((⌊t⌋₊ : ℕ) : ℝ) := by
          rw [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]
          ring
    _ ≤ Real.log 3 * t := mul_le_mul_of_nonneg_left hfloor hlog3

/-- For real exponents `b < a` and any `c > 0`, eventually `x ^ b ≤ c * x ^ a`
(as `x → ∞`). -/
private lemma eventually_rpow_le_mul_rpow {a b c : ℝ} (hb : b < a) (hc : 0 < c) :
    ∀ᶠ x : ℝ in Filter.atTop, x ^ b ≤ c * x ^ a := by
  have hd : 0 < a - b := sub_pos.mpr hb
  have hlt : ∀ᶠ x : ℝ in Filter.atTop, x ^ (-(a - b)) ≤ c :=
    (tendsto_rpow_neg_atTop hd).eventually (eventually_le_nhds hc)
  filter_upwards [hlt, eventually_ge_atTop (1 : ℝ)] with x hx hx1
  have hx0 : (0 : ℝ) < x := by linarith
  have hsplit : x ^ a * x ^ (-(a - b)) = x ^ b := by
    rw [← Real.rpow_add hx0]
    congr 1
    ring
  have hxa : 0 ≤ x ^ a := Real.rpow_nonneg hx0.le a
  calc x ^ b = x ^ a * x ^ (-(a - b)) := hsplit.symm
    _ ≤ x ^ a * c := mul_le_mul_of_nonneg_left hx hxa
    _ = c * x ^ a := by ring

lemma psi_sub_theta_eventually_le :
    ∀ᶠ x : ℕ in Filter.atTop, Chebyshev.psi (x : ℝ) - Chebyshev.theta (x : ℝ) ≤ 1.099 * Real.sqrt x := by
  have hlog3lt : Real.log 3 < 1.099 := lt_trans Real.log_three_lt_d9 (by norm_num)
  have hlog3pos : 0 < Real.log 3 := Real.log_pos (by norm_num)
  set g : ℝ := 1.099 - Real.log 3 with hgdef
  have hg : 0 < g := by rw [hgdef]; linarith
  have hR : ∀ᶠ x : ℝ in Filter.atTop,
      Chebyshev.psi x - Chebyshev.theta x ≤ 1.099 * Real.sqrt x := by
    have h13 : ∀ᶠ x : ℝ in Filter.atTop,
        Real.log 3 * x ^ (1 / 3 : ℝ) ≤ (g / 4) * x ^ (1 / 2 : ℝ) := by
      have hc : 0 < (g / 4) / Real.log 3 := div_pos (by linarith) hlog3pos
      filter_upwards [eventually_rpow_le_mul_rpow (a := (1 / 2 : ℝ)) (b := (1 / 3 : ℝ))
          (c := (g / 4) / Real.log 3) (by norm_num) hc] with x hx
      calc Real.log 3 * x ^ (1 / 3 : ℝ)
          ≤ Real.log 3 * (((g / 4) / Real.log 3) * x ^ (1 / 2 : ℝ)) :=
              mul_le_mul_of_nonneg_left hx hlog3pos.le
        _ = (g / 4) * x ^ (1 / 2 : ℝ) := by
              have hne : Real.log 3 ≠ 0 := ne_of_gt hlog3pos
              field_simp
    have h15 : ∀ᶠ x : ℝ in Filter.atTop,
        Real.log 3 * x ^ (1 / 5 : ℝ) ≤ (g / 4) * x ^ (1 / 2 : ℝ) := by
      have hc : 0 < (g / 4) / Real.log 3 := div_pos (by linarith) hlog3pos
      filter_upwards [eventually_rpow_le_mul_rpow (a := (1 / 2 : ℝ)) (b := (1 / 5 : ℝ))
          (c := (g / 4) / Real.log 3) (by norm_num) hc] with x hx
      calc Real.log 3 * x ^ (1 / 5 : ℝ)
          ≤ Real.log 3 * (((g / 4) / Real.log 3) * x ^ (1 / 2 : ℝ)) :=
              mul_le_mul_of_nonneg_left hx hlog3pos.le
        _ = (g / 4) * x ^ (1 / 2 : ℝ) := by
              have hne : Real.log 3 ≠ 0 := ne_of_gt hlog3pos
              field_simp
    filter_upwards [h13, h15, eventually_ge_atTop (1 : ℝ)] with x h13x h15x hx1
    have hx0 : (0 : ℝ) < x := by linarith
    have hxhalf : 0 ≤ x ^ (1 / 2 : ℝ) := Real.rpow_nonneg hx0.le _
    have hCP : Chebyshev.psi x - Chebyshev.theta x ≤
        Chebyshev.psi (x ^ (1 / 2 : ℝ)) + Chebyshev.psi (x ^ (1 / 3 : ℝ))
          + Chebyshev.psi (x ^ (1 / 5 : ℝ)) := by
      simpa only [inv_eq_one_div] using Chebyshev.psi_sub_theta_le_psi_add_psi_add_psi x
    have hsum : Real.log 3 * x ^ (1 / 3 : ℝ) + Real.log 3 * x ^ (1 / 5 : ℝ)
        ≤ (g / 2) * x ^ (1 / 2 : ℝ) := by
      nlinarith [h13x, h15x]
    have hb : Real.log 3 + g / 2 ≤ 1.099 := by
      rw [hgdef]; nlinarith [hlog3lt]
    calc Chebyshev.psi x - Chebyshev.theta x
        ≤ Chebyshev.psi (x ^ (1 / 2 : ℝ)) + Chebyshev.psi (x ^ (1 / 3 : ℝ))
            + Chebyshev.psi (x ^ (1 / 5 : ℝ)) := hCP
      _ ≤ Real.log 3 * x ^ (1 / 2 : ℝ) + Real.log 3 * x ^ (1 / 3 : ℝ)
            + Real.log 3 * x ^ (1 / 5 : ℝ) := by
            have h1 := psi_le_log3_mul_real (x ^ (1 / 2 : ℝ)) (Real.rpow_nonneg hx0.le _)
            have h3 := psi_le_log3_mul_real (x ^ (1 / 3 : ℝ)) (Real.rpow_nonneg hx0.le _)
            have h5 := psi_le_log3_mul_real (x ^ (1 / 5 : ℝ)) (Real.rpow_nonneg hx0.le _)
            linarith
      _ = Real.log 3 * x ^ (1 / 2 : ℝ)
            + (Real.log 3 * x ^ (1 / 3 : ℝ) + Real.log 3 * x ^ (1 / 5 : ℝ)) := by ring
      _ ≤ Real.log 3 * x ^ (1 / 2 : ℝ) + (g / 2) * x ^ (1 / 2 : ℝ) := by linarith [hsum]
      _ = (Real.log 3 + g / 2) * x ^ (1 / 2 : ℝ) := by ring
      _ ≤ 1.099 * x ^ (1 / 2 : ℝ) := mul_le_mul_of_nonneg_right hb hxhalf
      _ = 1.099 * Real.sqrt x := by rw [Real.sqrt_eq_rpow]
  exact tendsto_natCast_atTop_atTop.eventually hR

end Commons.NumberTheory.Chebyshev
