import Mathlib
import Submission.Work.BMF.halasz_series_aux

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Elementary bounds for the local Euler factors `gp`

For `f : ℕ → ℂ` with `f 1 = 1` and `‖f n‖ ≤ 1`, and `σ > 1`, we prove that the local
Euler factor `gp f p z = Σ_e f(p^e) (p^e)^{-z}` satisfies `‖gp f p z - 1‖ ≤ 2 p^{-σ}`
for `Re z > σ`, that `gp f p z ≠ 0`, and we record the resulting inverse bound.
-/

namespace Work.BMF

open LSeries

/-- Summability of `p^{-σ}` over the primes for `σ > 1`. -/
lemma summable_prime_rpow_neg (σ : ℝ) (hσ : 1 < σ) :
    Summable (fun p : Nat.Primes => (p : ℝ) ^ (-σ)) := by
  have h : Summable (fun n : ℕ => (n : ℝ) ^ (-σ)) := Real.summable_nat_rpow.mpr (by linarith)
  exact h.subtype Nat.Prime

/-- `((p)^e)^{w} = ((p)^w)^e` for `p > 0`. -/
lemma rpow_pow_eq (p : ℕ) (hp0 : (0:ℝ) < p) (e : ℕ) (w : ℝ) :
    ((p : ℝ) ^ e) ^ w = ((p : ℝ) ^ w) ^ e := by
  rw [← Real.rpow_natCast (p:ℝ) e]
  rw [← Real.rpow_mul (le_of_lt hp0) (e:ℝ) w, mul_comm (e:ℝ) w,
      Real.rpow_mul (le_of_lt hp0) w (e:ℝ), Real.rpow_natCast]

/-- Antitonicity of `x ↦ x^{-σ}` for `σ ≥ 0` on `(0,∞)`. -/
lemma rpow_neg_anti {x y σ : ℝ} (hx : 0 < x) (hxy : x ≤ y) (hσ : 0 ≤ σ) :
    y ^ (-σ) ≤ x ^ (-σ) := by
  rw [Real.rpow_neg hx.le, Real.rpow_neg (le_trans hx.le hxy), ← one_div, ← one_div]
  exact one_div_le_one_div_of_le (Real.rpow_pos_of_pos hx σ) (Real.rpow_le_rpow hx.le hxy hσ)

/-- Term bound: for `e ≥ 0`, `‖term f z (p^e)‖ ≤ R^e` with `R = p^{-σ}`. -/
lemma norm_term_prime_pow_le (f : ℕ → ℂ) (hb : ∀ n, ‖f n‖ ≤ 1)
    {p : ℕ} (hp : p.Prime) {z : ℂ} {σ : ℝ} (hσz : σ ≤ z.re) (e : ℕ) :
    ‖LSeries.term f z (p ^ e)‖ ≤ ((p : ℝ) ^ (-σ)) ^ e := by
  have hp1 : (1:ℝ) < (p:ℝ) := by exact_mod_cast hp.one_lt
  have hp0 : (0:ℝ) < (p:ℝ) := lt_trans zero_lt_one hp1
  have hp0n : p ≠ 0 := hp.ne_zero
  rcases Nat.eq_zero_or_pos e with h | h
  · subst h
    rw [Nat.pow_zero, LSeries.term_of_ne_zero (by norm_num : (1:ℕ) ≠ 0),
      Nat.cast_one, Complex.one_cpow, div_one, pow_zero]
    exact hb 1
  · have hpe0 : p ^ e ≠ 0 := pow_ne_zero _ hp0n
    rw [LSeries.norm_term_eq, ite_eq_right hpe0, Nat.cast_pow]
    have h1 : ‖f (p ^ e)‖ ≤ 1 := hb _
    calc ‖f (p ^ e)‖ / ((p:ℝ)^e) ^ z.re
        = ‖f (p ^ e)‖ * (((p:ℝ)^e) ^ z.re)⁻¹ := by rw [div_eq_mul_inv]
      _ ≤ (((p:ℝ)^e) ^ z.re)⁻¹ :=
          mul_le_of_le_one_left
            (inv_nonneg.mpr (Real.rpow_nonneg (pow_nonneg hp0.le e) z.re)) h1
      _ = ((p:ℝ) ^ (-z.re)) ^ e := by
          rw [rpow_pow_eq p hp0 e z.re, ← inv_pow,
            ← Real.rpow_neg (x := (p:ℝ)) (le_of_lt hp0) z.re]
      _ ≤ ((p:ℝ) ^ (-σ)) ^ e :=
          pow_le_pow_left₀ (Real.rpow_nonneg (le_of_lt hp0) (-z.re))
            (Real.rpow_le_rpow_of_exponent_le (le_of_lt hp1) (by linarith)) e

lemma gp_eq_one_add_tail (f : ℕ → ℂ) (hf1 : f 1 = 1) (hb : ∀ n, ‖f n‖ ≤ 1)
    {p : ℕ} (hp : p.Prime) {z : ℂ} (hz : 0 < z.re) :
    gp f p z = 1 + ∑' e : ℕ, LSeries.term f z (p ^ (e+1)) := by
  have hp1 : (1:ℝ) < (p:ℝ) := by exact_mod_cast hp.one_lt
  have hp0 : (0:ℝ) < (p:ℝ) := lt_trans zero_lt_one hp1
  have hR1 : ((p:ℝ)^(-z.re)) < 1 := by
    have := Real.rpow_lt_rpow_of_exponent_lt hp1 (show -z.re < (0:ℝ) by linarith)
    rwa [Real.rpow_zero] at this
  have hRn : ‖((p:ℝ)^(-z.re))‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hp0 _)]; exact hR1
  have hsum : Summable (fun e : ℕ => LSeries.term f z (p ^ e)) := by
    apply Summable.of_norm
    exact Summable.of_nonneg_of_le (fun e => norm_nonneg _)
      (fun e => norm_term_prime_pow_le f hb hp (le_refl z.re) e)
      (summable_geometric_of_norm_lt_one hRn)
  rw [gp]
  rw [Summable.tsum_eq_zero_add hsum, Nat.pow_zero,
    LSeries.term_of_ne_zero (by norm_num : (1:ℕ) ≠ 0), Nat.cast_one, Complex.one_cpow, hf1,
    div_one]

lemma gp_tail_bound (f : ℕ → ℂ) (hf1 : f 1 = 1) (hb : ∀ n, ‖f n‖ ≤ 1)
    {p : ℕ} (hp : p.Prime) {z : ℂ} {σ : ℝ} (hz : σ ≤ z.re) (hσ : 1 < σ) :
    ‖∑' e : ℕ, LSeries.term f z (p ^ (e+1))‖ ≤ 2 * (p:ℝ)^(-σ) := by
  have hp1 : (1:ℝ) < (p:ℝ) := by exact_mod_cast hp.one_lt
  have hp0 : (0:ℝ) < (p:ℝ) := lt_trans zero_lt_one hp1
  set R : ℝ := (p:ℝ)^(-σ) with hRdef
  have hRpos : 0 < R := Real.rpow_pos_of_pos hp0 _
  have hR1 : R < 1 := by
    rw [hRdef]
    have := Real.rpow_lt_rpow_of_exponent_lt hp1 (show -σ < (0:ℝ) by linarith)
    rwa [Real.rpow_zero] at this
  have hR2 : R ≤ 1/2 := by
    rw [hRdef, Real.rpow_neg (x := (p:ℝ)) hp0.le]
    have h2p : (2:ℝ) ≤ (p:ℝ)^σ := by
      calc (2:ℝ) = (2:ℝ)^(1:ℝ) := (Real.rpow_one 2).symm
        _ ≤ (2:ℝ)^σ :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) hσ.le
        _ ≤ (p:ℝ)^σ :=
            Real.rpow_le_rpow (by norm_num : (0:ℝ) ≤ 2) (by exact_mod_cast hp.two_le)
              (by linarith : (0:ℝ) ≤ σ)
    rw [show ((p:ℝ)^σ)⁻¹ = 1/((p:ℝ)^σ) from (one_div _).symm]
    exact one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 2) h2p
  have hsum : Summable (fun e : ℕ => R ^ (e+1)) := by
    have hge : Summable (fun e : ℕ => R ^ e) :=
      summable_geometric_of_norm_lt_one (by rwa [Real.norm_eq_abs, abs_of_pos hRpos])
    simpa [pow_succ'] using hge.mul_left R
  have htermnorm : Summable (fun e : ℕ => ‖LSeries.term f z (p ^ (e+1))‖) :=
    Summable.of_nonneg_of_le (fun e => norm_nonneg _)
      (fun e => norm_term_prime_pow_le f hb hp hz (e+1)) hsum
  have htsum : ∑' e : ℕ, R ^ (e+1) = R * (1 - R)⁻¹ := by
    rw [tsum_congr (fun e => by rw [pow_succ']), tsum_mul_left,
      tsum_geometric_of_norm_lt_one (by rwa [Real.norm_eq_abs, abs_of_pos hRpos])]
  have hRinv : (1 - R)⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ (by linarith) (by norm_num : (0:ℝ) < 2)]
    linarith
  calc ‖∑' e : ℕ, LSeries.term f z (p ^ (e+1))‖
      ≤ ∑' e : ℕ, ‖LSeries.term f z (p ^ (e+1))‖ :=
        norm_tsum_le_tsum_norm htermnorm
    _ ≤ ∑' e : ℕ, R ^ (e+1) :=
        Summable.tsum_le_tsum (fun e => norm_term_prime_pow_le f hb hp hz (e+1)) htermnorm hsum
    _ = R * (1 - R)⁻¹ := htsum
    _ ≤ R * 2 := mul_le_mul_of_nonneg_left hRinv hRpos.le
    _ = 2 * (p:ℝ)^(-σ) := by rw [hRdef]; ring

theorem norm_gp_sub_one_le (f : ℕ → ℂ) (hf1 : f 1 = 1) (hb : ∀ n, ‖f n‖ ≤ 1)
    {σ : ℝ} (hσ : 1 < σ) (p : ℕ) (hp : p.Prime) {z : ℂ} (hz : σ < z.re) :
    ‖gp f p z - 1‖ ≤ 2 * (p : ℝ) ^ (-σ) := by
  rw [gp_eq_one_add_tail f hf1 hb hp (lt_trans (by linarith) hz), add_sub_cancel_left]
  exact gp_tail_bound f hf1 hb hp (le_of_lt hz) hσ

/-- The modulus `2·2^{-σ}` is `< 1` for `σ > 1`. -/
lemma two_mul_rpow_neg_two_lt_one {σ : ℝ} (hσ : 1 < σ) : 2 * (2:ℝ)^(-σ) < 1 := by
  have h1 : (2:ℝ)^(-σ) < (2:ℝ)⁻¹ := by
    have := Real.rpow_lt_rpow_of_exponent_lt (x := (2:ℝ)) (by norm_num)
      (show -σ < (-(1:ℝ)) by linarith)
    rwa [Real.rpow_neg_one] at this
  have h2 : (2:ℝ)⁻¹ = 1/2 := by norm_num
  rw [h2] at h1
  linarith

theorem gp_ne_zero (f : ℕ → ℂ) (hf1 : f 1 = 1) (hb : ∀ n, ‖f n‖ ≤ 1)
    {σ : ℝ} (hσ : 1 < σ) (p : ℕ) (hp : p.Prime) {z : ℂ} (hz : σ < z.re) :
    gp f p z ≠ 0 := by
  intro h
  have hle := norm_gp_sub_one_le f hf1 hb hσ p hp hz
  have hmono : 2 * (p:ℝ)^(-σ) ≤ 2 * (2:ℝ)^(-σ) :=
    mul_le_mul_of_nonneg_left
      (rpow_neg_anti (by norm_num : (0:ℝ) < 2) (by exact_mod_cast hp.two_le)
        (by linarith : (0:ℝ) ≤ σ)) (by norm_num)
  have hlt := two_mul_rpow_neg_two_lt_one hσ
  rw [h] at hle
  have h0 : ‖(0:ℂ) - 1‖ = 1 := by norm_num
  rw [h0] at hle
  linarith

end Work.BMF
