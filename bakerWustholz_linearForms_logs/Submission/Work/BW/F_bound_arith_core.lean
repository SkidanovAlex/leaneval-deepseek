import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- Numeric core: `4 π n (9n)^n ≤ 7 · 9^n · (n+1)^{n+1}` for `n ≥ 1`.
This combines the numerical bound `π < 3.15` with the elementary Bernoulli
inequality `(1 + 1/n)^{n+1} ≥ 2`, i.e. `2 n^{n+1} ≤ (n+1)^{n+1}`. -/
lemma pi_pow_numeric_core (n : ℕ) (hn : 1 ≤ n) :
    4 * Real.pi * (n : ℝ) * (9 * (n : ℝ)) ^ n ≤ 7 * 9 ^ n * ((n : ℝ) + 1) ^ (n + 1) := by
  have hx1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hxpos : (0 : ℝ) < (n : ℝ) := lt_of_lt_of_le zero_lt_one hx1
  have hp14 : 4 * Real.pi < 14 := by linarith [Real.pi_lt_d2]
  have h2x : 2 * (n : ℝ) ^ (n + 1) ≤ ((n : ℝ) + 1) ^ (n + 1) := by
    have hinv : (0 : ℝ) < 1 / (n : ℝ) := one_div_pos.mpr hxpos
    have hbern : 1 + ((n + 1 : ℕ) : ℝ) * (1 / (n : ℝ)) ≤ (1 + 1 / (n : ℝ)) ^ (n + 1) :=
      one_add_mul_le_pow (by linarith : (-2 : ℝ) ≤ 1 / (n : ℝ)) (n + 1)
    have h1x : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) * (1 / (n : ℝ)) := by
      rw [mul_one_div, le_div_iff₀ hxpos]
      push_cast
      linarith
    have hge2alt : (2 : ℝ) ≤ 1 + ((n + 1 : ℕ) : ℝ) * (1 / (n : ℝ)) := by linarith
    have hge2 : (2 : ℝ) ≤ (1 + 1 / (n : ℝ)) ^ (n + 1) := le_trans hge2alt hbern
    have hxp : (0 : ℝ) ≤ (n : ℝ) ^ (n + 1) := (pow_pos hxpos (n + 1)).le
    calc 2 * (n : ℝ) ^ (n + 1) ≤ (1 + 1 / (n : ℝ)) ^ (n + 1) * (n : ℝ) ^ (n + 1) :=
          mul_le_mul_of_nonneg_right hge2 hxp
      _ = ((n : ℝ) + 1) ^ (n + 1) := by
            rw [← mul_pow]
            congr 1
            field_simp
  have hcore : 4 * Real.pi * (n : ℝ) ^ (n + 1) ≤ 7 * ((n : ℝ) + 1) ^ (n + 1) := by
    have hX : (0 : ℝ) ≤ (n : ℝ) ^ (n + 1) := (pow_pos hxpos (n + 1)).le
    have h1 : 4 * Real.pi * (n : ℝ) ^ (n + 1) ≤ 14 * (n : ℝ) ^ (n + 1) :=
      mul_le_mul_of_nonneg_right hp14.le hX
    linarith [h2x]
  have h9 : (0 : ℝ) ≤ 9 ^ n := by positivity
  have key : 4 * Real.pi * (n : ℝ) * (9 * (n : ℝ)) ^ n
      = 9 ^ n * (4 * Real.pi * (n : ℝ) ^ (n + 1)) := by
    rw [mul_pow]
    rw [show (4 : ℝ) * Real.pi * (n : ℝ) * (9 ^ n * (n : ℝ) ^ n)
          = 9 ^ n * (4 * Real.pi * ((n : ℝ) * (n : ℝ) ^ n)) by ring]
    rw [← pow_succ' (n : ℝ) n]
  calc 4 * Real.pi * (n : ℝ) * (9 * (n : ℝ)) ^ n
      = 9 ^ n * (4 * Real.pi * (n : ℝ) ^ (n + 1)) := key
    _ ≤ 9 ^ n * (7 * ((n : ℝ) + 1) ^ (n + 1)) := mul_le_mul_of_nonneg_left hcore h9
    _ = 7 * 9 ^ n * ((n : ℝ) + 1) ^ (n + 1) := by ring

lemma F_bound_arith_core {m n : ℕ} {d Q : ℝ} (hd : 1 ≤ d) (hn : 1 ≤ n) (hnm : n ≤ m - 1)
    (hQ : (1 / d) ^ (m - n) ≤ Q) :
    4 * Real.pi * (n : ℝ) * (9 * (n : ℝ) * d ^ 3) ^ n ≤
      (9 * (m : ℝ) * d ^ 3) ^ m * Q * (1 - 2 / (9 * d ^ 2)) := by
  -- basic facts
  have hnm1 : n + 1 ≤ m := by omega
  have hk_eq : n + (m - n) = m := by omega
  have hm1nat : 1 ≤ m := by omega
  have dpos : 0 < d := lt_of_lt_of_le zero_lt_one hd
  have hd2 : (1 : ℝ) ≤ d ^ 2 := one_le_pow₀ hd
  have hdk : (1 : ℝ) ≤ (d ^ 2) ^ (m - n) := one_le_pow₀ hd2
  have hfrac : (2 : ℝ) / (9 * d ^ 2) ≤ 2 / 9 := by
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < 9 * d ^ 2)]
    nlinarith [hd2]
  have hZ : (7 : ℝ) / 9 ≤ 1 - 2 / (9 * d ^ 2) := by linarith
  have hZ0 : (0 : ℝ) ≤ 1 - 2 / (9 * d ^ 2) := by linarith
  -- monotonicity of `x ↦ (9x)^x` in base and exponent
  have hcast : ((n : ℝ) + 1) ≤ (m : ℝ) := by exact_mod_cast hnm1
  have hbase : (9 : ℝ) * ((n : ℝ) + 1) ≤ 9 * (m : ℝ) := by
    have := mul_le_mul_of_nonneg_left hcast (by norm_num : (0 : ℝ) ≤ 9)
    simpa using this
  have hm1R : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1nat
  have hb2 : (1 : ℝ) ≤ 9 * (m : ℝ) := by linarith
  have hA : 9 * 9 ^ n * ((n : ℝ) + 1) ^ (n + 1) ≤ (9 * (m : ℝ)) ^ m := by
    have h1 : (9 * ((n : ℝ) + 1)) ^ (n + 1) ≤ (9 * (m : ℝ)) ^ (n + 1) :=
      pow_le_pow_left₀ (by positivity) hbase (n + 1)
    have h2 : (9 * (m : ℝ)) ^ (n + 1) ≤ (9 * (m : ℝ)) ^ m :=
      pow_le_pow_right₀ hb2 hnm1
    have h3 : (9 * ((n : ℝ) + 1)) ^ (n + 1) = 9 * 9 ^ n * ((n : ℝ) + 1) ^ (n + 1) := by
      rw [mul_pow, pow_succ' 9 n]
    rw [h3] at h1
    exact le_trans h1 h2
  -- the numeric core
  have hnum := pi_pow_numeric_core n hn
  have hbig : 7 * 9 ^ n * ((n : ℝ) + 1) ^ (n + 1) ≤
      (9 * (m : ℝ)) ^ m * (d ^ 2) ^ (m - n) * (1 - 2 / (9 * d ^ 2)) := by
    calc 7 * 9 ^ n * ((n : ℝ) + 1) ^ (n + 1)
        = (9 * 9 ^ n * ((n : ℝ) + 1) ^ (n + 1)) * 1 * ((7 : ℝ) / 9) := by ring
      _ ≤ (9 * (m : ℝ)) ^ m * (d ^ 2) ^ (m - n) * (1 - 2 / (9 * d ^ 2)) := by
          apply mul_le_mul
          · exact mul_le_mul hA hdk (by norm_num) (by positivity)
          · exact hZ
          · norm_num
          · positivity
  have hred : 4 * Real.pi * (n : ℝ) * (9 * (n : ℝ)) ^ n ≤
      (9 * (m : ℝ)) ^ m * (d ^ 2) ^ (m - n) * (1 - 2 / (9 * d ^ 2)) :=
    le_trans hnum hbig
  -- algebraic identity: absorb `(1/d)^(m-n)` and `(d^3)^n` into `(d^3)^m`
  have hmain : (9 * (m : ℝ) * d ^ 3) ^ m * (1 / d) ^ (m - n) * (1 - 2 / (9 * d ^ 2))
      = ((9 * (m : ℝ)) ^ m * (d ^ 2) ^ (m - n) * (1 - 2 / (9 * d ^ 2))) * (d ^ 3) ^ n := by
    have h1 : (9 * (m : ℝ) * d ^ 3) ^ m = (9 * (m : ℝ)) ^ m * (d ^ 3) ^ m := by rw [mul_pow]
    have h2 : (d ^ 3) ^ m = (d ^ 3) ^ n * (d ^ 3) ^ (m - n) := by
      nth_rewrite 1 [← hk_eq]
      rw [pow_add]
    have h3 : (d ^ 3) ^ (m - n) * (1 / d) ^ (m - n) = (d ^ 2) ^ (m - n) := by
      rw [← mul_pow]
      congr 1
      field_simp
    calc (9 * (m : ℝ) * d ^ 3) ^ m * (1 / d) ^ (m - n) * (1 - 2 / (9 * d ^ 2))
        = (9 * (m : ℝ)) ^ m * (d ^ 3) ^ m * (1 / d) ^ (m - n) * (1 - 2 / (9 * d ^ 2)) := by
          rw [h1]
      _ = (9 * (m : ℝ)) ^ m * ((d ^ 3) ^ n * (d ^ 3) ^ (m - n)) * (1 / d) ^ (m - n)
            * (1 - 2 / (9 * d ^ 2)) := by rw [h2]
      _ = (9 * (m : ℝ)) ^ m * (d ^ 3) ^ n * ((d ^ 3) ^ (m - n) * (1 / d) ^ (m - n))
            * (1 - 2 / (9 * d ^ 2)) := by ring
      _ = (9 * (m : ℝ)) ^ m * (d ^ 3) ^ n * (d ^ 2) ^ (m - n) * (1 - 2 / (9 * d ^ 2)) := by
          rw [h3]
      _ = ((9 * (m : ℝ)) ^ m * (d ^ 2) ^ (m - n) * (1 - 2 / (9 * d ^ 2))) * (d ^ 3) ^ n := by
          ring
  have h9md3 : (0 : ℝ) ≤ (9 * (m : ℝ) * d ^ 3) ^ m :=
    pow_nonneg (mul_nonneg (by positivity) (pow_nonneg (le_of_lt dpos) 3)) m
  have hlhs : (9 * (n : ℝ) * d ^ 3) ^ n = (9 * (n : ℝ)) ^ n * (d ^ 3) ^ n := by rw [mul_pow]
  have hd3n : (0 : ℝ) ≤ (d ^ 3) ^ n := pow_nonneg (pow_nonneg (le_of_lt dpos) 3) n
  have hmul := mul_le_mul_of_nonneg_right hred hd3n
  -- core inequality with `Q` replaced by `(1/d)^(m-n)`
  have key : 4 * Real.pi * (n : ℝ) * (9 * (n : ℝ) * d ^ 3) ^ n ≤
      (9 * (m : ℝ) * d ^ 3) ^ m * (1 / d) ^ (m - n) * (1 - 2 / (9 * d ^ 2)) := by
    rw [hlhs, hmain]
    calc 4 * Real.pi * (n : ℝ) * ((9 * (n : ℝ)) ^ n * (d ^ 3) ^ n)
        = (4 * Real.pi * (n : ℝ) * (9 * (n : ℝ)) ^ n) * (d ^ 3) ^ n := by ring
      _ ≤ ((9 * (m : ℝ)) ^ m * (d ^ 2) ^ (m - n) * (1 - 2 / (9 * d ^ 2))) * (d ^ 3) ^ n :=
          hmul
  -- upgrade `(1/d)^(m-n)` to `Q`
  have hQstep : (9 * (m : ℝ) * d ^ 3) ^ m * (1 / d) ^ (m - n) * (1 - 2 / (9 * d ^ 2))
      ≤ (9 * (m : ℝ) * d ^ 3) ^ m * Q * (1 - 2 / (9 * d ^ 2)) := by
    have h1 : (1 / d) ^ (m - n) * (1 - 2 / (9 * d ^ 2)) ≤ Q * (1 - 2 / (9 * d ^ 2)) :=
      mul_le_mul_of_nonneg_right hQ hZ0
    have h2 : (9 * (m : ℝ) * d ^ 3) ^ m * ((1 / d) ^ (m - n) * (1 - 2 / (9 * d ^ 2)))
        ≤ (9 * (m : ℝ) * d ^ 3) ^ m * (Q * (1 - 2 / (9 * d ^ 2))) :=
      mul_le_mul_of_nonneg_left h1 h9md3
    calc (9 * (m : ℝ) * d ^ 3) ^ m * (1 / d) ^ (m - n) * (1 - 2 / (9 * d ^ 2))
        = (9 * (m : ℝ) * d ^ 3) ^ m * ((1 / d) ^ (m - n) * (1 - 2 / (9 * d ^ 2))) := by ring
      _ ≤ (9 * (m : ℝ) * d ^ 3) ^ m * (Q * (1 - 2 / (9 * d ^ 2))) := h2
      _ = (9 * (m : ℝ) * d ^ 3) ^ m * Q * (1 - 2 / (9 * d ^ 2)) := by ring
  exact le_trans key hQstep

end Work.BW
