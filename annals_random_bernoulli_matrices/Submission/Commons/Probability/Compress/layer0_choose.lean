import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Submission.Commons.Nat.Choose.choose_le_exp_div

set_option autoImplicit false
open scoped BigOperators unitInterval Topology

namespace Commons.Probability.Compress

/-! ## Elementary helper lemmas for `layer0_choose`

The main theorem picks a small positive `ee` and a large `n₀` so that a
binomial-type term is eventually dominated by `(1 - p + ε)^n`.
-/

lemma floor_sub_one_lt (x : ℝ) : x - 1 < (Nat.floor x : ℝ) := by
  have h := Nat.lt_floor_add_one x
  linarith

/-- If `0 ≤ b` and integer `k ≤ x`, then `b^k ≤ (1+b)^x`. -/
lemma pow_le_add_one_rpow {b : ℝ} (hb0 : 0 ≤ b) {k : ℕ} {x : ℝ} (hkx : (k : ℝ) ≤ x) :
    b ^ k ≤ (1 + b) ^ x := by
  calc
    b ^ k ≤ (1 + b) ^ k := pow_le_pow_left₀ hb0 (by linarith) k
    _ = (1 + b) ^ ((k : ℝ)) := (Real.rpow_natCast (1 + b) k).symm
    _ ≤ (1 + b) ^ x := Real.rpow_le_rpow_of_exponent_le (by linarith) hkx

/-- Binomial bound: `C(n, floor (ee·n)) ≤ (2e/ee)^(ee·n)` (real exponent), for `n ≥ 2/ee`. -/
lemma binom_le {ee : ℝ} (hee0 : 0 < ee) (hee1 : ee < 1) {n : ℕ}
    (hn : (2 / ee) ≤ (n : ℝ)) :
    (n.choose (Nat.floor (ee * (n : ℝ))) : ℝ) ≤ (2 * Real.exp 1 / ee) ^ (ee * (n : ℝ)) := by
  let x : ℝ := ee * (n : ℝ)
  let k : ℕ := Nat.floor x
  have hxdef : x = ee * (n : ℝ) := rfl
  have hx0 : 0 ≤ x := by
    dsimp [x]
    positivity
  have hx2 : 2 ≤ x := by
    calc
      2 = (2 / ee) * ee := by field_simp [hee0.ne']
      _ ≤ (n : ℝ) * ee := mul_le_mul_of_nonneg_right hn hee0.le
      _ = x := by dsimp [x]; ring
  have hn0 : 0 < (n : ℝ) := by
    have hpos : 0 < 2 / ee := by positivity
    linarith
  have hk1 : 1 ≤ k := by
    have hx1 : (1 : ℝ) ≤ x := by linarith
    exact Nat.le_floor (a := x) (by simpa using hx1)
  have hk1pos : 0 < k := lt_of_lt_of_le Nat.zero_lt_one hk1
  have hk_le : (k : ℝ) ≤ x := by
    dsimp [k]
    exact Nat.floor_le hx0
  have hk_gt : x - 1 < (k : ℝ) := by
    dsimp [k]
    exact floor_sub_one_lt x
  have hx_lt_n : x < (n : ℝ) := by
    have hsub : ee - 1 < 0 := by linarith
    have hmul := mul_lt_mul_of_pos_right hsub hn0
    have hrel : (ee - 1) * (n : ℝ) = ee * (n : ℝ) - (n : ℝ) := by ring
    rw [hrel] at hmul
    rw [hxdef]
    linarith
  have hknr : (k : ℝ) ≤ (n : ℝ) := by
    exact le_trans hk_le (le_of_lt hx_lt_n)
  have hkn : k ≤ n := by
    exact_mod_cast hknr
  have hk_ge_half : x / 2 ≤ (k : ℝ) := by
    nlinarith [hk_gt, hx2]
  have hx_le_2k : x ≤ 2 * (k : ℝ) := by
    nlinarith [hk_ge_half]
  have hk0r : 0 < (k : ℝ) := by
    have : 0 < x / 2 := by nlinarith [hx2]
    linarith
  have hnk : (n : ℝ) / (k : ℝ) ≤ 2 / ee := by
    rw [div_le_div_iff₀ hk0r hee0]
    have hxle : (n : ℝ) * ee ≤ 2 * (k : ℝ) := by
      nlinarith [hx_le_2k, hxdef]
    simpa [mul_comm] using hxle
  have hC : (n.choose k : ℝ) ≤ (Real.exp 1 * (n : ℝ) / (k : ℝ)) ^ k := by
    exact Commons.Nat.Choose.choose_le_exp_div n k hk1pos hkn
  have hE_ratio : Real.exp 1 * (n : ℝ) / (k : ℝ) ≤ 2 * Real.exp 1 / ee := by
    calc
      Real.exp 1 * (n : ℝ) / (k : ℝ) = Real.exp 1 * ((n : ℝ) / (k : ℝ)) := by ring
      _ ≤ Real.exp 1 * (2 / ee) := mul_le_mul_of_nonneg_left hnk (Real.exp_pos 1).le
      _ = 2 * Real.exp 1 / ee := by ring
  have hnonneg : 0 ≤ Real.exp 1 * (n : ℝ) / (k : ℝ) := by positivity
  have hpow1 : (Real.exp 1 * (n : ℝ) / (k : ℝ)) ^ k ≤ (2 * Real.exp 1 / ee) ^ k := by
    exact pow_le_pow_left₀ hnonneg hE_ratio k
  have hbase1 : 1 ≤ 2 * Real.exp 1 / ee := by
    have hE1 : 1 ≤ Real.exp 1 := Real.one_le_exp zero_le_one
    have hnum : ee ≤ 2 * Real.exp 1 := by nlinarith
    rw [one_le_div₀ hee0]
    exact hnum
  calc
    (n.choose k : ℝ) ≤ (Real.exp 1 * (n : ℝ) / (k : ℝ)) ^ k := hC
    _ ≤ (2 * Real.exp 1 / ee) ^ k := hpow1
    _ = (2 * Real.exp 1 / ee) ^ ((k : ℝ)) := (Real.rpow_natCast (2 * Real.exp 1 / ee) k).symm
    _ ≤ (2 * Real.exp 1 / ee) ^ x := by
      exact Real.rpow_le_rpow_of_exponent_le hbase1 hk_le
    _ = (2 * Real.exp 1 / ee) ^ (ee * (n : ℝ)) := by
      rw [← hxdef]

/-- (e(n-1)/m)^m ≤ (e/ee) * (e/ee)^(ee·n), where `m = ceil (ee·(n-1))`, for `n ≥ 2`. -/
lemma ceil_pow_mul_le {ee : ℝ} (hee0 : 0 < ee) (hee1 : ee < 1) {n : ℕ} (hn : 2 ≤ n) :
    (Real.exp 1 * ((n - 1 : ℕ) : ℝ) /
        (Nat.ceil (ee * ((n - 1 : ℕ) : ℝ)) : ℝ)) ^ Nat.ceil (ee * ((n - 1 : ℕ) : ℝ))
      ≤ (Real.exp 1 / ee) * (Real.exp 1 / ee) ^ (ee * (n : ℝ)) := by
  let y : ℝ := ee * ((n - 1 : ℕ) : ℝ)
  let m : ℕ := Nat.ceil y
  let x : ℝ := ee * (n : ℝ)
  have hy0 : 0 ≤ y := by dsimp [y]; positivity
  have hy_gt0 : 0 < y := by
    dsimp [y]
    have hn0n : 0 < n - 1 := by omega
    exact mul_pos hee0 (by exact_mod_cast hn0n)
  have m_ge_y : y ≤ (m : ℝ) := by dsimp [m]; exact Nat.le_ceil y
  have m_lt_y1 : (m : ℝ) < y + 1 := by
    dsimp [m]
    exact Nat.ceil_lt_add_one hy0
  have m_le_y1 : (m : ℝ) ≤ y + 1 := le_of_lt m_lt_y1
  have hm_pos : 0 < (m : ℝ) := lt_of_lt_of_le hy_gt0 m_ge_y
  have h_ratio : ((n - 1 : ℕ) : ℝ) / (m : ℝ) ≤ 1 / ee := by
    rw [div_le_div_iff₀ hm_pos hee0]
    have hydef : y = ee * ((n - 1 : ℕ) : ℝ) := rfl
    nlinarith [m_ge_y, hydef]
  have hYm : Real.exp 1 * ((n - 1 : ℕ) : ℝ) / (m : ℝ) ≤ Real.exp 1 / ee := by
    calc
      Real.exp 1 * ((n - 1 : ℕ) : ℝ) / (m : ℝ) = Real.exp 1 * (((n - 1 : ℕ) : ℝ) / (m : ℝ)) := by ring
      _ ≤ Real.exp 1 * (1 / ee) := mul_le_mul_of_nonneg_left h_ratio (Real.exp_pos 1).le
      _ = Real.exp 1 / ee := by ring
  have hY_nonneg : 0 ≤ Real.exp 1 * ((n - 1 : ℕ) : ℝ) / (m : ℝ) := by positivity
  have hbase1 : 1 ≤ Real.exp 1 / ee := by
    have hE1 : 1 ≤ Real.exp 1 := Real.one_le_exp zero_le_one
    have hnum : ee ≤ Real.exp 1 := by linarith
    rw [one_le_div₀ hee0]
    exact hnum
  have hbpos : 0 < Real.exp 1 / ee := by positivity
  have hpow_base : (Real.exp 1 * ((n - 1 : ℕ) : ℝ) / (m : ℝ)) ^ m ≤ (Real.exp 1 / ee) ^ m := by
    exact pow_le_pow_left₀ hY_nonneg hYm m
  have hy_le_x : y ≤ x := by
    have hnm : (n - 1 : ℕ) ≤ n := Nat.sub_le _ _
    have hnmr : (((n - 1 : ℕ) : ℝ) ≤ (n : ℝ)) := by exact_mod_cast hnm
    dsimp [y, x]
    exact mul_le_mul_of_nonneg_left hnmr hee0.le
  calc
    (Real.exp 1 * ((n - 1 : ℕ) : ℝ) / (m : ℝ)) ^ m ≤ (Real.exp 1 / ee) ^ m := hpow_base
    _ = (Real.exp 1 / ee) ^ ((m : ℝ)) := (Real.rpow_natCast (Real.exp 1 / ee) m).symm
    _ ≤ (Real.exp 1 / ee) ^ (y + 1) := Real.rpow_le_rpow_of_exponent_le hbase1 m_le_y1
    _ = (Real.exp 1 / ee) * (Real.exp 1 / ee) ^ y := by
      rw [Real.rpow_add hbpos y 1, Real.rpow_one]
      ring
    _ ≤ (Real.exp 1 / ee) * (Real.exp 1 / ee) ^ x := by
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hbase1 hy_le_x) hbpos.le
    _ = (Real.exp 1 / ee) * (Real.exp 1 / ee) ^ (ee * (n : ℝ)) := by rfl

/-- q-part bound: `q^((n-1) - ceil(ee·(n-1))) ≤ (1/q²)·(q^(1-ee))^n` under `1 ≤ (1-ee)(n-1)`. -/
lemma qpow_ceil_le {q ee : ℝ} (hq0 : 0 < q) (hq1 : q ≤ 1) (hee0 : 0 < ee) (hee1 : ee < 1)
    {n : ℕ} (hcond : 1 ≤ (1 - ee) * ((n - 1 : ℕ) : ℝ)) :
    q ^ ((n - 1) - Nat.ceil (ee * ((n - 1 : ℕ) : ℝ))) ≤
      (1 / q ^ 2) * (q ^ (1 - ee)) ^ n := by
  let y : ℝ := ee * ((n - 1 : ℕ) : ℝ)
  let m : ℕ := Nat.ceil y
  let e0 : ℕ := (n - 1) - m
  have hy0 : 0 ≤ y := by dsimp [y]; positivity
  have hcei : (m : ℝ) < y + 1 := by dsimp [m]; exact Nat.ceil_lt_add_one hy0
  have hle_m : (m : ℝ) ≤ y + 1 := le_of_lt hcei
  have hy1 : y + 1 ≤ ((n - 1 : ℕ) : ℝ) := by
    dsimp [y]
    nlinarith [hcond]
  have hcond_m : (m : ℝ) ≤ ((n - 1 : ℕ) : ℝ) := le_trans hle_m hy1
  have hm_le_nm : m ≤ n - 1 := by exact_mod_cast hcond_m
  have hn2 : 2 ≤ n := by
    by_contra h
    have hnle : n ≤ 1 := by omega
    have hnmnat : n - 1 = 0 := by omega
    have hprod : (1 - ee) * ((n - 1 : ℕ) : ℝ) ≤ 0 := by
      rw [hnmnat]
      norm_num
    nlinarith
  have hrel : ((n - 1 : ℕ) : ℝ) + 1 = (n : ℝ) := by
    have hsubnat : (n - 1) + 1 = n := by omega
    calc
      ((n - 1 : ℕ) : ℝ) + (1 : ℝ) = ((n - 1 : ℕ) : ℝ) + ((1 : ℕ) : ℝ) := by norm_num
      _ = (((n - 1) + 1 : ℕ) : ℝ) := (Nat.cast_add (n - 1) 1).symm
      _ = (n : ℝ) := by rw [hsubnat]
  have he0r : ((e0 : ℕ) : ℝ) = ((n - 1 : ℕ) : ℝ) - (m : ℝ) := by
    dsimp [e0]
    rw [Nat.cast_sub hm_le_nm]
  have he0_ge : ((1 - ee) * ((n - 1 : ℕ) : ℝ)) - 1 ≤ ((e0 : ℕ) : ℝ) := by
    rw [he0r]
    have hydef : y = ee * ((n - 1 : ℕ) : ℝ) := rfl
    nlinarith
  have hc_le_e0 : (1 - ee) * (n : ℝ) - 2 ≤ ((e0 : ℕ) : ℝ) := by
    have hrel2 : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by linarith [hrel]
    nlinarith [he0_ge, hrel2]
  have hqpow : q ^ e0 ≤ q ^ ((1 - ee) * (n : ℝ) - 2) := by
    have hq_e0 : q ^ e0 = q ^ (((e0 : ℕ) : ℝ)) := (Real.rpow_natCast q e0).symm
    rw [hq_e0]
    exact Real.rpow_le_rpow_of_exponent_ge hq0 hq1 hc_le_e0
  have h1 : q ^ ((1 - ee) * (n : ℝ)) = (q ^ (1 - ee)) ^ n := by
    rw [Real.rpow_mul hq0.le (1 - ee) (n : ℝ)]
    rw [Real.rpow_natCast]
  have hc_eq : q ^ ((1 - ee) * (n : ℝ) - 2) = (1 / q ^ 2) * (q ^ (1 - ee)) ^ n := by
    calc
      q ^ ((1 - ee) * (n : ℝ) - 2) = q ^ (((1 - ee) * (n : ℝ)) + (-2 : ℝ)) := by ring_nf
      _ = q ^ ((1 - ee) * (n : ℝ)) * q ^ (-2 : ℝ) := by rw [Real.rpow_add hq0]
      _ = q ^ ((1 - ee) * (n : ℝ)) * (1 / q ^ 2) := by
        have hqneg : q ^ (-(2 : ℝ)) = 1 / q ^ 2 := by
          rw [Real.rpow_neg hq0.le (2 : ℝ)]
          field_simp [pow_ne_zero 2 hq0.ne']
          norm_num
        rw [hqneg]
      _ = (1 / q ^ 2) * (q ^ (1 - ee)) ^ n := by rw [h1]; ring
  calc
    q ^ e0 ≤ q ^ ((1 - ee) * (n : ℝ) - 2) := hqpow
    _ = (1 / q ^ 2) * (q ^ (1 - ee)) ^ n := hc_eq

/-- product of real powers `a^(ee·n) b^(ee·n) c^(ee·n) d^n = (a^ee b^ee c^ee d)^n` -/
lemma rpow_prod_pow (a b c d ee : ℝ) (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) (hc0 : 0 ≤ c) (hd0 : 0 ≤ d)
    (hee0 : 0 ≤ ee) (n : ℕ) :
    (a ^ (ee * (n : ℝ))) * (b ^ (ee * (n : ℝ))) * (c ^ (ee * (n : ℝ))) * d ^ n =
      (a ^ ee * b ^ ee * c ^ ee * d) ^ n := by
  have ha : a ^ (ee * (n : ℝ)) = (a ^ ee) ^ n := by
    rw [Real.rpow_mul ha0 ee (n : ℝ)]
    rw [Real.rpow_natCast]
  have hb : b ^ (ee * (n : ℝ)) = (b ^ ee) ^ n := by
    rw [Real.rpow_mul hb0 ee (n : ℝ)]
    rw [Real.rpow_natCast]
  have hc : c ^ (ee * (n : ℝ)) = (c ^ ee) ^ n := by
    rw [Real.rpow_mul hc0 ee (n : ℝ)]
    rw [Real.rpow_natCast]
  calc
    (a ^ (ee * (n : ℝ))) * (b ^ (ee * (n : ℝ))) * (c ^ (ee * (n : ℝ))) * d ^ n
        = (a ^ ee) ^ n * (b ^ ee) ^ n * (c ^ ee) ^ n * d ^ n := by rw [ha, hb, hc]
    _ = (a ^ ee * b ^ ee * c ^ ee * d) ^ n := by
      rw [← mul_pow]
      rw [← mul_pow]
      rw [← mul_pow]

lemma log_mul_self_le_two_sqrt {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) :
    x * Real.log (1 / x) ≤ 2 * Real.sqrt x := by
  have hsx : 0 < Real.sqrt x := Real.sqrt_pos.2 hx0
  have hlog : Real.log (1 / x) ≤ 2 / Real.sqrt x := by
    have htsq : (Real.sqrt x) ^ 2 = x := Real.sq_sqrt hx0.le
    calc
      Real.log (1 / x) = Real.log (1 / (Real.sqrt x) ^ 2) := by
        congr 1
        rw [htsq]
      _ = Real.log ((1 / Real.sqrt x) ^ 2) := by
        congr 1
        field_simp [hsx.ne']
      _ = 2 * Real.log (1 / Real.sqrt x) := by
        rw [Real.log_pow (1 / Real.sqrt x) 2]
        norm_num
      _ ≤ 2 * ((1 / Real.sqrt x) - 1) := by
        exact mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos (by positivity : 0 < 1 / Real.sqrt x)) (by norm_num)
      _ ≤ 2 / Real.sqrt x := by
        have h1 : (1 / Real.sqrt x) - 1 ≤ 1 / Real.sqrt x := by linarith
        calc
          2 * ((1 / Real.sqrt x) - 1) ≤ 2 * (1 / Real.sqrt x) := mul_le_mul_of_nonneg_left h1 (by norm_num)
          _ = 2 / Real.sqrt x := by ring
  calc
    x * Real.log (1 / x) ≤ x * (2 / Real.sqrt x) := mul_le_mul_of_nonneg_left hlog hx0.le
    _ = 2 * Real.sqrt x := by
      have hsxn : Real.sqrt x ≠ 0 := hsx.ne'
      field_simp [hsxn]
      ring_nf
      rw [Real.sq_sqrt hx0.le]

lemma log_one_add_div_sqrt_le {K ee : ℝ} (hK0 : 0 ≤ K) (hee0 : 0 < ee) (hee1 : ee < 1) :
    Real.log (1 + K / Real.sqrt ee) ≤ Real.log (1 + K) + (1 / 2) * Real.log (1 / ee) := by
  have hee1' : ee ≤ 1 := le_of_lt hee1
  have hsqrt : Real.sqrt ee ≤ 1 := (Real.sqrt_le_one).2 hee1'
  have hs : Real.sqrt ee > 0 := Real.sqrt_pos.2 hee0
  have h1 : 1 + K / Real.sqrt ee ≤ (1 + K) / Real.sqrt ee := by
    rw [le_div_iff₀ hs]
    calc
      (1 + K / Real.sqrt ee) * Real.sqrt ee = Real.sqrt ee + K := by field_simp [hs.ne']
      _ ≤ 1 + K := by nlinarith [hsqrt, hK0]
  have hpos1 : 0 < 1 + K / Real.sqrt ee := by positivity
  have hlog1 : Real.log (1 + K / Real.sqrt ee) ≤ Real.log ((1 + K) / Real.sqrt ee) :=
    Real.log_le_log hpos1 h1
  calc
    Real.log (1 + K / Real.sqrt ee) ≤ Real.log ((1 + K) / Real.sqrt ee) := hlog1
    _ = Real.log (1 + K) - Real.log (Real.sqrt ee) := by
      rw [Real.log_div (by positivity : (1 + K) ≠ 0) hs.ne']
    _ = Real.log (1 + K) + (1 / 2) * Real.log (1 / ee) := by
      have hlogsqrt : Real.log (Real.sqrt ee) = (1 / 2) * Real.log ee := by
        rw [Real.sqrt_eq_rpow ee]
        rw [Real.log_rpow hee0 (1 / 2)]
      rw [hlogsqrt]
      have hloginv : Real.log (1 / ee) = -Real.log ee := by
        rw [← inv_eq_one_div ee]
        exact Real.log_inv ee
      rw [hloginv]
      ring

/-- `log(2E/ee) = log(2E) + log(1/ee)` for `ee > 0`. -/
lemma log_div_add_log_inv {a ee : ℝ} (ha : 0 < a) (hee0 : 0 < ee) :
    Real.log (a / ee) = Real.log a + Real.log (1 / ee) := by
  calc
    Real.log (a / ee) = Real.log a - Real.log ee := by
      rw [Real.log_div ha.ne' hee0.ne']
    _ = Real.log a + Real.log (1 / ee) := by
      have hloginv : Real.log (1 / ee) = -Real.log ee := by
        rw [← inv_eq_one_div ee]
        exact Real.log_inv ee
      rw [hloginv]
      ring


/-- log of the geometric-factor product, bounded. -/
lemma s_log_le (q K ee : ℝ) (hq0 : 0 < q) (hK0 : 0 ≤ K) (hee0 : 0 < ee) (hee1 : ee < 1) :
    Real.log ((((2 * Real.exp 1 / ee) ^ ee) * ((1 + K / Real.sqrt ee) ^ ee)) *
        ((Real.exp 1 / ee) ^ ee) * q ^ (1 - ee))
    ≤ Real.log q + ee * (Real.log (1 / q) + Real.log (2 * Real.exp 1) + 1 + Real.log (1 + K)) +
        5 * Real.sqrt ee := by
  set F1 : ℝ := (2 * Real.exp 1 / ee) ^ ee with hF1def
  set F2 : ℝ := (1 + K / Real.sqrt ee) ^ ee with hF2def
  set F3 : ℝ := (Real.exp 1 / ee) ^ ee with hF3def
  set Q : ℝ := q ^ (1 - ee) with hQdef
  change Real.log (((F1 * F2) * F3) * Q) ≤
    Real.log q + ee * (Real.log (1 / q) + Real.log (2 * Real.exp 1) + 1 + Real.log (1 + K)) +
      5 * Real.sqrt ee
  have hF1p : 0 < F1 := by rw [hF1def]; positivity
  have hF2p : 0 < F2 := by rw [hF2def]; positivity
  have hF3p : 0 < F3 := by rw [hF3def]; positivity
  have hQp : 0 < Q := by rw [hQdef]; positivity
  have hlogS : Real.log (((F1 * F2) * F3) * Q) =
      ((Real.log F1 + Real.log F2) + Real.log F3) + Real.log Q := by
    calc
      Real.log (((F1 * F2) * F3) * Q) = Real.log ((F1 * F2) * F3) + Real.log Q := by
        rw [Real.log_mul (by positivity : (F1 * F2) * F3 ≠ 0) (by positivity : Q ≠ 0)]
      _ = (Real.log (F1 * F2) + Real.log F3) + Real.log Q := by
        rw [Real.log_mul (by positivity : F1 * F2 ≠ 0) (by positivity : F3 ≠ 0)]
      _ = ((Real.log F1 + Real.log F2) + Real.log F3) + Real.log Q := by
        rw [Real.log_mul (by positivity : F1 ≠ 0) (by positivity : F2 ≠ 0)]
  have hlogF1 : Real.log F1 = ee * (Real.log (2 * Real.exp 1) + Real.log (1 / ee)) := by
    rw [hF1def]
    rw [Real.log_rpow (by positivity : 0 < (2 * Real.exp 1) / ee) ee]
    rw [log_div_add_log_inv (by positivity : 0 < 2 * Real.exp 1) hee0]
  have hlogF3 : Real.log F3 = ee * (1 + Real.log (1 / ee)) := by
    rw [hF3def]
    rw [Real.log_rpow (by positivity : 0 < Real.exp 1 / ee) ee]
    rw [log_div_add_log_inv (Real.exp_pos 1) hee0]
    have hE1 : Real.log (Real.exp 1) = 1 := by simpa using (Real.log_exp (1 : ℝ))
    rw [hE1]
  have hlogQ : Real.log Q = (1 - ee) * Real.log q := by
    rw [hQdef]
    rw [Real.log_rpow hq0 (1 - ee)]
  have hlogF2_le : Real.log F2 ≤ ee * (Real.log (1 + K) + (1 / 2) * Real.log (1 / ee)) := by
    rw [hF2def]
    have hlr : Real.log ((1 + K / Real.sqrt ee) ^ ee) = ee * Real.log (1 + K / Real.sqrt ee) := by
      rw [Real.log_rpow (by positivity : 0 < 1 + K / Real.sqrt ee) ee]
    rw [hlr]
    exact mul_le_mul_of_nonneg_left (log_one_add_div_sqrt_le hK0 hee0 hee1) hee0.le
  have hw : ee * Real.log (1 / ee) ≤ 2 * Real.sqrt ee := by
    exact log_mul_self_le_two_sqrt hee0 (le_of_lt hee1)
  -- intermediate: expand all and bound F2-part
  have hstep : ((Real.log F1 + Real.log F2) + Real.log F3) + Real.log Q ≤
      (1 - ee) * Real.log q + ee * (Real.log (2 * Real.exp 1) + Real.log (1 + K) + 1) +
        (5 / 2) * (ee * Real.log (1 / ee)) := by
    have h1 : ((Real.log F1 + Real.log F2) + Real.log F3) + Real.log Q ≤
        ((Real.log F1 + ee * (Real.log (1 + K) + (1 / 2) * Real.log (1 / ee))) + Real.log F3) + Real.log Q := by
      nlinarith [hlogF2_le]
    calc
      ((Real.log F1 + Real.log F2) + Real.log F3) + Real.log Q ≤
          ((Real.log F1 + ee * (Real.log (1 + K) + (1 / 2) * Real.log (1 / ee))) + Real.log F3) + Real.log Q := h1
      _ = (1 - ee) * Real.log q + ee * (Real.log (2 * Real.exp 1) + Real.log (1 + K) + 1) +
          (5 / 2) * (ee * Real.log (1 / ee)) := by
        rw [hlogF1, hlogF3, hlogQ]
        ring
  have hstep2 : (1 - ee) * Real.log q + ee * (Real.log (2 * Real.exp 1) + Real.log (1 + K) + 1) +
        (5 / 2) * (ee * Real.log (1 / ee)) ≤
      Real.log q + ee * (Real.log (1 / q) + Real.log (2 * Real.exp 1) + 1 + Real.log (1 + K)) +
        5 * Real.sqrt ee := by
    have hqinv : Real.log (1 / q) = -Real.log q := by
      rw [← inv_eq_one_div q]
      exact Real.log_inv q
    have hw5 : (5 / 2) * (ee * Real.log (1 / ee)) ≤ 5 * Real.sqrt ee := by
      calc
        (5 / 2) * (ee * Real.log (1 / ee)) ≤ (5 / 2) * (2 * Real.sqrt ee) :=
          mul_le_mul_of_nonneg_left hw (by norm_num)
        _ = 5 * Real.sqrt ee := by ring
    rw [hqinv]
    nlinarith [hw5]
  calc
    Real.log (((F1 * F2) * F3) * Q) = ((Real.log F1 + Real.log F2) + Real.log F3) + Real.log Q := hlogS
    _ ≤ (1 - ee) * Real.log q + ee * (Real.log (2 * Real.exp 1) + Real.log (1 + K) + 1) +
        (5 / 2) * (ee * Real.log (1 / ee)) := hstep
    _ ≤ Real.log q + ee * (Real.log (1 / q) + Real.log (2 * Real.exp 1) + 1 + Real.log (1 + K)) +
        5 * Real.sqrt ee := hstep2

/-- Pointwise bound of the geometric product by `q·exp(κ·ee + 5√ee)`. -/
lemma s_bound (q K ee : ℝ) (hq0 : 0 < q) (hK0 : 0 ≤ K) (hee0 : 0 < ee) (hee1 : ee < 1) :
    ((((2 * Real.exp 1 / ee) ^ ee) * ((1 + K / Real.sqrt ee) ^ ee)) *
        ((Real.exp 1 / ee) ^ ee) * q ^ (1 - ee))
    ≤ Real.exp (Real.log q +
        ee * (Real.log (1 / q) + Real.log (2 * Real.exp 1) + 1 + Real.log (1 + K)) +
        5 * Real.sqrt ee) := by
  let S : ℝ := (((2 * Real.exp 1 / ee) ^ ee) * ((1 + K / Real.sqrt ee) ^ ee)) *
      ((Real.exp 1 / ee) ^ ee) * q ^ (1 - ee)
  have hSp : 0 < S := by dsimp [S]; positivity
  have hlog := s_log_le q K ee hq0 hK0 hee0 hee1
  have hlog2 : Real.log S ≤
      Real.log q + ee * (Real.log (1 / q) + Real.log (2 * Real.exp 1) + 1 + Real.log (1 + K)) +
        5 * Real.sqrt ee := by
    simpa [S] using hlog
  change S ≤ Real.exp (Real.log q +
      ee * (Real.log (1 / q) + Real.log (2 * Real.exp 1) + 1 + Real.log (1 + K)) +
      5 * Real.sqrt ee)
  exact (Real.log_le_iff_le_exp hSp).mp hlog2

/-- Choose `ee` small with the geometric product `≤ q + ε/2`. -/
lemma exists_ee_small (q K ε : ℝ) (hq0 : 0 < q) (hq1 : q ≤ 1) (hK0 : 0 ≤ K) (hε0 : 0 < ε) :
    ∃ ee : ℝ, 0 < ee ∧ ee ≤ 1 / 2 ∧
      ((((2 * Real.exp 1 / ee) ^ ee) * ((1 + K / Real.sqrt ee) ^ ee)) *
        ((Real.exp 1 / ee) ^ ee) * q ^ (1 - ee)) ≤ q + ε / 2 := by
  let θ : ℝ := Real.log ((q + ε / 2) / q)
  let κ : ℝ := Real.log (1 / q) + Real.log (2 * Real.exp 1) + 1 + Real.log (1 + K)
  have hqinv0 : 0 ≤ Real.log (1 / q) := by
    have h : (1 : ℝ) ≤ 1 / q := (one_le_div₀ hq0).2 hq1
    exact Real.log_nonneg h
  have h2E : 0 < Real.log (2 * Real.exp 1) := by
    apply Real.log_pos
    have hE1 : 1 ≤ Real.exp 1 := Real.one_le_exp zero_le_one
    nlinarith
  have h1K : 0 ≤ Real.log (1 + K) := Real.log_nonneg (by nlinarith [hK0])
  have hκ : 0 < κ := by
    dsimp [κ]
    nlinarith
  have hτ : 1 < (q + ε / 2) / q := by
    rw [one_lt_div₀ hq0]
    linarith
  have hθ : 0 < θ := by
    dsimp [θ]
    exact Real.log_pos hτ
  have hτpos : 0 < (q + ε / 2) / q := by positivity
  let ee : ℝ := min (min (θ / (2 * κ)) ((θ / 10) ^ 2)) (1 / 2)
  have hee0 : 0 < ee := by
    dsimp [ee]
    exact lt_min (lt_min (div_pos hθ (by positivity)) (sq_pos_of_pos (div_pos hθ (by norm_num)))) (by norm_num)
  have hee12 : ee ≤ 1 / 2 := by
    dsimp [ee]
    exact min_le_right _ _
  have hκe : κ * ee ≤ θ / 2 := by
    have hmin : ee ≤ θ / (2 * κ) := le_trans (min_le_left _ _) (min_le_left _ _)
    calc
      κ * ee ≤ κ * (θ / (2 * κ)) := mul_le_mul_of_nonneg_left hmin hκ.le
      _ = θ / 2 := by field_simp [hκ.ne']
  have hsqrt5 : 5 * Real.sqrt ee ≤ θ / 2 := by
    have hmin : ee ≤ (θ / 10) ^ 2 := le_trans (min_le_left _ _) (min_le_right _ _)
    have h10 : 0 ≤ θ / 10 := div_nonneg hθ.le (by norm_num)
    have hs : Real.sqrt ee ≤ θ / 10 := by
      calc
        Real.sqrt ee ≤ Real.sqrt ((θ / 10) ^ 2) := Real.sqrt_le_sqrt hmin
        _ = θ / 10 := Real.sqrt_sq h10
    calc
      5 * Real.sqrt ee ≤ 5 * (θ / 10) := mul_le_mul_of_nonneg_left hs (by norm_num)
      _ = θ / 2 := by ring
  have hθle : ee * κ + 5 * Real.sqrt ee ≤ θ := by
    nlinarith [hκe, hsqrt5]
  refine ⟨ee, hee0, hee12, ?_⟩
  have hee1 : ee < 1 := lt_of_le_of_lt hee12 (by norm_num)
  have hsb := s_bound q K ee hq0 hK0 hee0 hee1
  have hbnd : Real.exp (Real.log q +
      ee * (Real.log (1 / q) + Real.log (2 * Real.exp 1) + 1 + Real.log (1 + K)) +
      5 * Real.sqrt ee) ≤ q + ε / 2 := by
    calc
      Real.exp (Real.log q +
          ee * (Real.log (1 / q) + Real.log (2 * Real.exp 1) + 1 + Real.log (1 + K)) +
          5 * Real.sqrt ee)
          = q * Real.exp (ee * (Real.log (1 / q) + Real.log (2 * Real.exp 1) + 1 + Real.log (1 + K)) +
              5 * Real.sqrt ee) := by
            have hX : Real.log q +
                (ee * (Real.log (1 / q) + Real.log (2 * Real.exp 1) + 1 + Real.log (1 + K)) +
                  5 * Real.sqrt ee) =
                Real.log q + ee * (Real.log (1 / q) + Real.log (2 * Real.exp 1) + 1 + Real.log (1 + K)) +
                  5 * Real.sqrt ee := by ring
            rw [← hX]
            rw [Real.exp_add, Real.exp_log hq0]
      _ = q * Real.exp (ee * κ + 5 * Real.sqrt ee) := by
            rfl
      _ ≤ q * Real.exp θ := by
            exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hθle) hq0.le
      _ = q + ε / 2 := by
            have hqex : q * Real.exp θ = q * ((q + ε / 2) / q) := by
              congr 1
              dsimp [θ]
              rw [Real.exp_log hτpos]
            rw [hqex]
            field_simp [hq0.ne']
  exact le_trans hsb hbnd


/-- The main-term estimate: the product of binomial, geometric factor, ceiling-power and
`q`-power is bounded by a constant times `s^n`, for `n` large relative to `ee`. -/
lemma main_term_le (q K A ee : ℝ) (hq0 : 0 < q) (hq1 : q ≤ 1)
    (hK0 : 0 ≤ K) (hA0 : 0 ≤ A) (hee0 : 0 < ee) (hee1 : ee < 1)
    {n : ℕ} (hn2 : 2 ≤ n)
    (hcond1 : (2 / ee) ≤ (n : ℝ))
    (hcond2 : 1 ≤ (1 - ee) * ((n - 1 : ℕ) : ℝ)) :
    (A / Real.sqrt ee) * (n.choose (Nat.floor (ee * (n : ℝ))) : ℝ) *
        (K / Real.sqrt ee) ^ Nat.floor (ee * (n : ℝ)) *
        ((Real.exp 1 * ((n - 1 : ℕ) : ℝ) /
            (Nat.ceil (ee * ((n - 1 : ℕ) : ℝ)) : ℝ)) ^ Nat.ceil (ee * ((n - 1 : ℕ) : ℝ)) *
          q ^ ((n - 1) - Nat.ceil (ee * ((n - 1 : ℕ) : ℝ))))
      ≤ (A / Real.sqrt ee) * (Real.exp 1 / ee) * (1 / q ^ 2) *
          (((2 * Real.exp 1 / ee) ^ ee) * ((1 + K / Real.sqrt ee) ^ ee) *
              ((Real.exp 1 / ee) ^ ee) * q ^ (1 - ee)) ^ n := by
  let F0 : ℝ := A / Real.sqrt ee
  let k0 : ℕ := Nat.floor (ee * (n : ℝ))
  let m0 : ℕ := Nat.ceil (ee * ((n - 1 : ℕ) : ℝ))
  let e0 : ℕ := (n - 1) - m0
  let C0 : ℝ := (n.choose k0 : ℝ)
  let X0 : ℝ := K / Real.sqrt ee
  let Y0 : ℝ := Real.exp 1 * ((n - 1 : ℕ) : ℝ) / (m0 : ℝ)
  let B1 : ℝ := (2 * Real.exp 1 / ee) ^ (ee * (n : ℝ))
  let B2 : ℝ := (1 + K / Real.sqrt ee) ^ (ee * (n : ℝ))
  let C3 : ℝ := (Real.exp 1 / ee) * (Real.exp 1 / ee) ^ (ee * (n : ℝ))
  let B4 : ℝ := (1 / q ^ 2) * (q ^ (1 - ee)) ^ n
  have hF0 : 0 ≤ F0 := by dsimp [F0]; positivity
  have hC0 : 0 ≤ C0 := by dsimp [C0]; exact_mod_cast (Nat.zero_le _)
  have hX0 : 0 ≤ X0 := by dsimp [X0]; positivity
  have hY0 : 0 ≤ Y0 := by dsimp [Y0]; positivity
  have hq0pow : 0 ≤ q ^ e0 := pow_nonneg hq0.le e0
  have hB1 : 0 ≤ B1 := by dsimp [B1]; positivity
  have hB2 : 0 ≤ B2 := by dsimp [B2]; positivity
  have hC3 : 0 ≤ C3 := by dsimp [C3]; positivity
  have hB4 : 0 ≤ B4 := by dsimp [B4]; positivity
  have hC : C0 ≤ B1 := by
    dsimp [C0, B1]
    exact binom_le hee0 hee1 hcond1
  have hX : X0 ^ k0 ≤ B2 := by
    dsimp [X0, B2, k0]
    apply pow_le_add_one_rpow (b := K / Real.sqrt ee)
    · positivity
    · exact Nat.floor_le (by positivity)
  have hY : Y0 ^ m0 * q ^ e0 ≤ C3 * B4 := by
    have hY1 : Y0 ^ m0 ≤ C3 := by
      dsimp [Y0, C3, m0]
      exact ceil_pow_mul_le hee0 hee1 hn2
    have hQ : q ^ e0 ≤ B4 := by
      dsimp [e0, B4, m0]
      exact qpow_ceil_le hq0 hq1 hee0 hee1 hcond2
    calc
      Y0 ^ m0 * q ^ e0 ≤ C3 * q ^ e0 := mul_le_mul_of_nonneg_right hY1 hq0pow
      _ ≤ C3 * B4 := mul_le_mul_of_nonneg_left hQ hC3
  change F0 * C0 * X0 ^ k0 * (Y0 ^ m0 * q ^ e0) ≤
    F0 * (Real.exp 1 / ee) * (1 / q ^ 2) *
      (((2 * Real.exp 1 / ee) ^ ee) * ((1 + K / Real.sqrt ee) ^ ee) *
          ((Real.exp 1 / ee) ^ ee) * q ^ (1 - ee)) ^ n
  calc
    F0 * C0 * X0 ^ k0 * (Y0 ^ m0 * q ^ e0)
        = F0 * (C0 * (X0 ^ k0 * (Y0 ^ m0 * q ^ e0))) := by ring
    _ ≤ F0 * (B1 * (X0 ^ k0 * (Y0 ^ m0 * q ^ e0))) := by
      apply mul_le_mul_of_nonneg_left _ hF0
      have hR : 0 ≤ X0 ^ k0 * (Y0 ^ m0 * q ^ e0) := by positivity
      exact mul_le_mul_of_nonneg_right hC hR
    _ = F0 * B1 * X0 ^ k0 * (Y0 ^ m0 * q ^ e0) := by ring
    _ = F0 * B1 * (X0 ^ k0 * (Y0 ^ m0 * q ^ e0)) := by ring
    _ ≤ F0 * B1 * (B2 * (Y0 ^ m0 * q ^ e0)) := by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg hF0 hB1)
      have hR : 0 ≤ Y0 ^ m0 * q ^ e0 := by positivity
      exact mul_le_mul_of_nonneg_right hX hR
    _ = F0 * B1 * B2 * (Y0 ^ m0 * q ^ e0) := by ring
    _ ≤ F0 * B1 * B2 * (C3 * B4) := by
      apply mul_le_mul_of_nonneg_left hY (mul_nonneg (mul_nonneg hF0 hB1) hB2)
    _ = F0 * (Real.exp 1 / ee) * (1 / q ^ 2) *
          (B1 * B2 * (Real.exp 1 / ee) ^ (ee * (n : ℝ)) * (q ^ (1 - ee)) ^ n) := by
      have hc3 : C3 = (Real.exp 1 / ee) * (Real.exp 1 / ee) ^ (ee * (n : ℝ)) := rfl
      have hb4 : B4 = (1 / q ^ 2) * (q ^ (1 - ee)) ^ n := rfl
      rw [hc3, hb4]
      ring
    _ = F0 * (Real.exp 1 / ee) * (1 / q ^ 2) *
          (((2 * Real.exp 1 / ee) ^ ee) * ((1 + K / Real.sqrt ee) ^ ee) *
              ((Real.exp 1 / ee) ^ ee) * q ^ (1 - ee)) ^ n := by
      have hb1 : B1 = (2 * Real.exp 1 / ee) ^ (ee * (n : ℝ)) := rfl
      have hb2 : B2 = (1 + K / Real.sqrt ee) ^ (ee * (n : ℝ)) := rfl
      rw [hb1, hb2]
      have hP : ((2 * Real.exp 1 / ee) ^ (ee * (n : ℝ))) *
            ((1 + K / Real.sqrt ee) ^ (ee * (n : ℝ))) *
            ((Real.exp 1 / ee) ^ (ee * (n : ℝ))) * (q ^ (1 - ee)) ^ n =
          (((2 * Real.exp 1 / ee) ^ ee) * ((1 + K / Real.sqrt ee) ^ ee) *
              ((Real.exp 1 / ee) ^ ee) * q ^ (1 - ee)) ^ n := by
        exact rpow_prod_pow (2 * Real.exp 1 / ee) (1 + K / Real.sqrt ee) (Real.exp 1 / ee)
            (q ^ (1 - ee)) ee (by positivity) (by positivity) (by positivity) (by positivity)
            (by positivity) n
      rw [hP]

/-- If `0 ≤ a < b` and `M > 0`, then `M * a^n ≤ b^n` for all sufficiently large `n`. -/
lemma pow_smul_eventually_le {a b M : ℝ} (hb : 0 < b) (ha : 0 ≤ a) (hab : a < b) (hM : 0 < M) :
    ∃ N : ℕ, ∀ n ≥ N, M * a ^ n ≤ b ^ n := by
  have ht0 : 0 ≤ a / b := div_nonneg ha hb.le
  have ht1 : a / b < 1 := (div_lt_one hb).2 hab
  have hconv : Filter.Tendsto (fun n : ℕ => (a / b) ^ n) Filter.atTop (𝓝 (0 : ℝ)) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one ht0 ht1
  have hev : ∀ᶠ n : ℕ in Filter.atTop, (a / b) ^ n ≤ 1 / M := by
    have hsmall : ∀ᶠ y : ℝ in 𝓝 (0 : ℝ), y < 1 / M := eventually_lt_nhds (by positivity : (0 : ℝ) < 1 / M)
    exact hconv.eventually (hsmall.mono (by intro y hy; exact le_of_lt hy))
  rcases (Filter.eventually_atTop.mp hev) with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn
  have hpn := hN n hn
  have hMt : M * (a / b) ^ n ≤ 1 := by
    calc
      M * (a / b) ^ n ≤ M * (1 / M) := mul_le_mul_of_nonneg_left hpn hM.le
      _ = 1 := by field_simp [hM.ne']
  have hbpow : 0 < b ^ n := pow_pos hb n
  have heq : (M * a ^ n) / b ^ n = M * (a / b) ^ n := by
    rw [div_pow]
    exact mul_div_assoc M (a ^ n) (b ^ n)
  have hdiv : (M * a ^ n) / b ^ n ≤ 1 := by
    rwa [heq]
  exact (div_le_one hbpow).mp hdiv

/-- If `0 ≤ a < b`, then `a^n ≤ (1/2) * b^n` for all sufficiently large `n`. -/
lemma pow_eventually_le_half {a b : ℝ} (hb : 0 < b) (ha : 0 ≤ a) (hab : a < b) :
    ∃ N : ℕ, ∀ n ≥ N, a ^ n ≤ (1 / 2 : ℝ) * b ^ n := by
  rcases pow_smul_eventually_le (a := a) (b := b) (M := 2) hb ha hab (by norm_num) with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn
  have h2 : (2 : ℝ) * a ^ n ≤ b ^ n := hN n hn
  have ha0 : 0 ≤ a ^ n := pow_nonneg ha n
  nlinarith

theorem layer0_choose {p : I} (hp₀ : 0 < (p : ℝ)) (hp₁ : (p : ℝ) ≤ 1 / 2)
    {ε : ℝ} (hε₀ : 0 < ε) {γa : ℝ} (hγa : 0 < γa) {L : ℝ} (hL : 1 ≤ L)
    {C₀ A : ℝ} (hC₀ : 1 ≤ C₀) (hA : 1 ≤ A) :
    ∃ (ee : ℝ) (n₀ : ℕ), 0 < ee ∧ ee < 1 ∧ 2 ≤ n₀ ∧
      ∀ n : ℕ, n₀ ≤ n →
        (1 / 2 : ℝ) ^ n + (A / Real.sqrt ee) *
          (n.choose (Nat.floor (ee * (n : ℝ))) : ℝ) *
          (C₀ * (8 * L) / (γa * Real.sqrt ee)) ^ (Nat.floor (ee * (n : ℝ))) *
          (((Real.exp 1 * ((n - 1 : ℕ) : ℝ) /
              (Nat.ceil (ee * ((n - 1 : ℕ) : ℝ)) : ℝ)) ^
                Nat.ceil (ee * ((n - 1 : ℕ) : ℝ))) *
            (1 - (p : ℝ)) ^ ((n - 1) - Nat.ceil (ee * ((n - 1 : ℕ) : ℝ))))
          ≤ (1 - (p : ℝ) + ε) ^ n := by
  set q : ℝ := 1 - (p : ℝ) with hqdef
  let K : ℝ := C₀ * (8 * L) / γa
  have hq0 : 0 < q := by
    have hq : (1 / 2 : ℝ) ≤ 1 - (p : ℝ) := by linarith
    dsimp [q]
    linarith
  have hq1 : q ≤ 1 := by
    dsimp [q]
    have hpnonneg : 0 ≤ (p : ℝ) := (show (p : ℝ) ∈ Set.Icc 0 1 from p.2).1
    linarith
  have hqhalf : (1 / 2 : ℝ) ≤ q := by
    dsimp [q]
    linarith
  have hK0 : 0 ≤ K := by
    have hC₀pos : 0 < C₀ := by linarith
    dsimp [K]
    positivity
  have hA0 : 0 ≤ A := by linarith
  have hApos : 0 < A := by linarith
  obtain ⟨ee, hee0, hee12, hS⟩ := exists_ee_small q K ε hq0 hq1 hK0 hε₀
  have hee1 : ee < 1 := lt_of_le_of_lt hee12 (by norm_num)
  let s0 : ℝ := (((2 * Real.exp 1 / ee) ^ ee) * ((1 + K / Real.sqrt ee) ^ ee)) *
      ((Real.exp 1 / ee) ^ ee) * q ^ (1 - ee)
  have hS' : s0 ≤ q + ε / 2 := by
    simpa [s0] using hS
  have hs0pos : 0 ≤ s0 := by dsimp [s0]; positivity
  have hqeb : 0 < q + ε := by linarith
  have hb_gt_half : (1 / 2 : ℝ) < q + ε := by linarith
  have hs0lt : s0 < q + ε := lt_of_le_of_lt hS' (by linarith)
  obtain ⟨N1, hN1⟩ := pow_eventually_le_half (a := (1 / 2 : ℝ)) (b := q + ε) hqeb (by norm_num) hb_gt_half
  let D : ℝ := (A / Real.sqrt ee) * (Real.exp 1 / ee) * (1 / q ^ 2)
  have hDpos : 0 < D := by
    dsimp [D]
    positivity
  obtain ⟨N2, hN2⟩ := pow_smul_eventually_le (a := s0) (b := q + ε) (M := 2 * D) hqeb hs0pos hs0lt (by positivity)
  obtain ⟨Nbig, hNbig⟩ := exists_nat_gt (2 / ee)
  let N3 : ℕ := max 3 Nbig
  have hN3cond : ∀ n ≥ N3, (2 / ee) ≤ (n : ℝ) ∧ 1 ≤ (1 - ee) * ((n - 1 : ℕ) : ℝ) ∧ 2 ≤ n := by
    intro n hn
    have h3n : 3 ≤ n := le_trans (le_max_left _ _) hn
    have hNbn : Nbig ≤ n := le_trans (le_max_right _ _) hn
    have h2n : 2 ≤ n := by omega
    have hnR : (Nbig : ℝ) ≤ (n : ℝ) := by exact_mod_cast hNbn
    have hge2 : (2 / ee) ≤ (n : ℝ) := by
      have hlt : (2 / ee) < (Nbig : ℝ) := hNbig
      linarith
    have hge1 : 1 ≤ (1 - ee) * ((n - 1 : ℕ) : ℝ) := by
      have hsub : (1 / 2 : ℝ) ≤ 1 - ee := by linarith
      have hn1ge : 2 ≤ n - 1 := by omega
      have hn1R : (2 : ℝ) ≤ ((n - 1 : ℕ) : ℝ) := by exact_mod_cast hn1ge
      have hm1 : (1 / 2 : ℝ) * (2 : ℝ) ≤ (1 - ee) * ((n - 1 : ℕ) : ℝ) := by
        have hc0 : 0 ≤ (1 - ee) := by linarith
        exact mul_le_mul hsub hn1R (by norm_num) hc0
      norm_num at hm1
      exact hm1
    exact ⟨hge2, hge1, h2n⟩
  let n0 : ℕ := max (max N1 N2) (max N3 2)
  have hn0ge2 : 2 ≤ n0 := by
    dsimp [n0]
    omega
  refine ⟨ee, n0, hee0, hee1, hn0ge2, ?_⟩
  intro n hn
  have hnN1 : N1 ≤ n := by dsimp [n0] at hn; omega
  have hnN2 : N2 ≤ n := by dsimp [n0] at hn; omega
  have hnN3 : N3 ≤ n := by dsimp [n0] at hn; omega
  have hhcond := hN3cond n hnN3
  rcases hhcond with ⟨hcond1, hcond2, hn2⟩
  have hmt := main_term_le (q := q) (K := C₀ * (8 * L) / γa) (A := A) (ee := ee)
      hq0 hq1 hK0 hA0 hee0 hee1 hn2 hcond1 hcond2
  have hb : (C₀ * (8 * L) / γa) / Real.sqrt ee = C₀ * (8 * L) / (γa * Real.sqrt ee) := by
    field_simp [hγa.ne']
  have hmt0 : (A / Real.sqrt ee) * (n.choose (Nat.floor (ee * (n : ℝ))) : ℝ) *
        (C₀ * (8 * L) / (γa * Real.sqrt ee)) ^ Nat.floor (ee * (n : ℝ)) *
        (((Real.exp 1 * ((n - 1 : ℕ) : ℝ) /
            (Nat.ceil (ee * ((n - 1 : ℕ) : ℝ)) : ℝ)) ^ Nat.ceil (ee * ((n - 1 : ℕ) : ℝ)) *
          q ^ ((n - 1) - Nat.ceil (ee * ((n - 1 : ℕ) : ℝ)))))
      ≤ (A / Real.sqrt ee) * (Real.exp 1 / ee) * (1 / q ^ 2) * s0 ^ n := by
    rw [← hb]
    simpa [D, s0] using hmt
  have hDle : D * s0 ^ n ≤ (q + ε) ^ n / 2 := by
    have h2D := hN2 n hnN2
    have hpos1 : 0 < (q + ε) ^ n := pow_pos hqeb n
    dsimp [D] at h2D ⊢
    nlinarith
  have hMain0 : (A / Real.sqrt ee) * (n.choose (Nat.floor (ee * (n : ℝ))) : ℝ) *
        (C₀ * (8 * L) / (γa * Real.sqrt ee)) ^ Nat.floor (ee * (n : ℝ)) *
        (((Real.exp 1 * ((n - 1 : ℕ) : ℝ) /
            (Nat.ceil (ee * ((n - 1 : ℕ) : ℝ)) : ℝ)) ^ Nat.ceil (ee * ((n - 1 : ℕ) : ℝ)) *
          q ^ ((n - 1) - Nat.ceil (ee * ((n - 1 : ℕ) : ℝ)))))
      ≤ (q + ε) ^ n / 2 := by
    exact le_trans hmt0 (by
      simpa [D] using hDle)
  have hN1n : (1 / 2 : ℝ) ^ n ≤ (1 / 2) * (q + ε) ^ n := hN1 n hnN1
  have hB2 : (1 / 2 : ℝ) * (q + ε) ^ n = (q + ε) ^ n / 2 := by ring
  rw [← hB2] at hMain0
  have hgoal : (1 / 2 : ℝ) ^ n + (A / Real.sqrt ee) * (n.choose (Nat.floor (ee * (n : ℝ))) : ℝ) *
        (C₀ * (8 * L) / (γa * Real.sqrt ee)) ^ Nat.floor (ee * (n : ℝ)) *
        (((Real.exp 1 * ((n - 1 : ℕ) : ℝ) /
            (Nat.ceil (ee * ((n - 1 : ℕ) : ℝ)) : ℝ)) ^ Nat.ceil (ee * ((n - 1 : ℕ) : ℝ)) *
          q ^ ((n - 1) - Nat.ceil (ee * ((n - 1 : ℕ) : ℝ)))))
      ≤ (q + ε) ^ n := by
    nlinarith

  -- now rewrite q away (it was a `set`)
  simpa [q] using hgoal


end Commons.Probability.Compress