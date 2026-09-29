import Mathlib

/-!
# `CisExpBoundB`: norm and error bounds for the truncated root of unity (Fx area)

Input to the `cis` word of paper Lemma 2.12 (Harvey–van der Hoeven).  Let
`N = 2^(p+60)`, let `r = Int.fmod j k ∈ [0,k)` be the nonnegative remainder of `j` mod `k`,
so that `θ = 2π r / k ∈ [0,2π)`, and let `R : ℤ` satisfy `|R − N θ| ≤ 3`.  The lemma
bounds, for the point `z = (−64 + R i)/N`:

* `‖exp z‖ = exp(−64/N) ≤ 1 − 32/N`;
* `‖exp z − exp(2πi r/k)‖ ≤ 67/N`;
* `(−64)² + R² ≤ (32 N)²`.

The proof decomposes `z = (θ i) + w` with `w = a + b i`, `a = −64/N ≤ 0`,
`b = R/N − θ`, and uses
`‖e^(a+bi) − 1‖ ≤ (1 − e^a) + |e^(bi) − 1| ≤ −a + |b| ≤ 64/N + 3/N`.
-/

namespace Work.Fx

/-- For `a ≤ 0` and real `b`: `‖exp (a + b i) − 1‖ ≤ −a + |b|`. -/
lemma norm_exp_add_mul_I_sub_one_le (a b : ℝ) (ha : a ≤ 0) :
    ‖Complex.exp ((a:ℂ) + (b:ℂ)*Complex.I) - 1‖ ≤ -a + |b| := by
  have hw : Complex.exp ((a:ℂ) + (b:ℂ)*Complex.I) - 1
      = Complex.exp ((b:ℂ)*Complex.I) * (Complex.exp (a:ℂ) - 1)
        + (Complex.exp ((b:ℂ)*Complex.I) - 1) := by
    rw [Complex.exp_add]; ring
  have hI : (b:ℂ) * Complex.I = Complex.I * (b:ℂ) := by ring
  have hnb : ‖Complex.exp ((b:ℂ)*Complex.I)‖ = 1 := by rw [hI, Complex.norm_exp_I_mul_ofReal]
  have hna : ‖Complex.exp (a:ℂ) - 1‖ = 1 - Real.exp a := by
    have h1 : Complex.exp (a:ℂ) = ((Real.exp a : ℝ) : ℂ) := (Complex.ofReal_exp a).symm
    have h2 : ((Real.exp a : ℝ) : ℂ) - 1 = ((Real.exp a - 1 : ℝ) : ℂ) := by push_cast; ring
    have h3 : Real.exp a - 1 ≤ 0 := by linarith [Real.exp_le_one_iff.mpr ha]
    have h4 : ‖((Real.exp a - 1 : ℝ) : ℂ)‖ = |Real.exp a - 1| := by
      simpa using RCLike.norm_ofReal (K := ℂ) (Real.exp a - 1)
    rw [h1, h2, h4, abs_of_nonpos h3]; ring
  have hnb1 : ‖Complex.exp ((b:ℂ)*Complex.I) - 1‖ ≤ |b| := by
    rw [hI]; simpa using Real.norm_exp_I_mul_ofReal_sub_one_le (x := b)
  have haexp : 1 - Real.exp a ≤ -a := by linarith [Real.add_one_le_exp a]
  rw [hw]
  calc ‖Complex.exp ((b:ℂ) * Complex.I) * (Complex.exp (a:ℂ) - 1)
        + (Complex.exp ((b:ℂ) * Complex.I) - 1)‖
      ≤ ‖Complex.exp ((b:ℂ) * Complex.I) * (Complex.exp (a:ℂ) - 1)‖
        + ‖Complex.exp ((b:ℂ) * Complex.I) - 1‖ := norm_add_le _ _
    _ = 1 * (1 - Real.exp a) + ‖Complex.exp ((b:ℂ) * Complex.I) - 1‖ := by rw [norm_mul, hnb, hna]
    _ ≤ 1 * (1 - Real.exp a) + |b| := by linarith
    _ ≤ -a + |b| := by linarith

/-- `exp (−a) ≤ 1 − a/2` for `0 ≤ a ≤ 2/3` (here `a = 64/N ≤ 2/3`). -/
lemma exp_neg_le_one_sub_half {a : ℝ} (h0 : 0 ≤ a) (h1 : a ≤ 2/3) :
    Real.exp (-a) ≤ 1 - a / 2 := by
  have hpos1 : (0:ℝ) < 1 + a := by linarith
  have hpos2 : (0:ℝ) < Real.exp a := Real.exp_pos a
  have hkey : 1 + a ≤ Real.exp a := by linarith [Real.add_one_le_exp a]
  have step1 : (Real.exp a)⁻¹ ≤ (1 + a)⁻¹ := by rw [inv_le_inv₀ hpos2 hpos1]; exact hkey
  have step2 : (1 + a)⁻¹ ≤ 1 - a / 2 := by
    rw [inv_le_iff_one_le_mul₀ hpos1]; nlinarith
  calc Real.exp (-a) = (Real.exp a)⁻¹ := Real.exp_neg a
    _ ≤ (1 + a)⁻¹ := step1
    _ ≤ 1 - a / 2 := step2

theorem CisExpBoundB (p : ℕ) (hp : 100 ≤ p) (j : ℤ) (k : ℕ) (hk : 1 ≤ k) (R : ℤ)
    (hR : |(R : ℝ) - 2 ^ (p + 60) * (2 * Real.pi * (Int.fmod j k : ℝ) / (k : ℝ))| ≤ 3) :
    ‖Complex.exp ((((-64 : ℤ) : ℂ) + (R : ℂ) * Complex.I) / (2 : ℂ) ^ (p + 60))‖
      ≤ 1 - 32 / (2 : ℝ) ^ (p + 60) ∧
    ‖Complex.exp ((((-64 : ℤ) : ℂ) + (R : ℂ) * Complex.I) / (2 : ℂ) ^ (p + 60))
        - Complex.exp (2 * Real.pi * Complex.I * ((Int.fmod j k : ℤ) : ℂ) / (k : ℂ))‖
      ≤ 67 / (2 : ℝ) ^ (p + 60) ∧
    ((-64 : ℝ) ^ 2 + (R : ℝ) ^ 2 ≤ (32 * 2 ^ (p + 60)) ^ 2) := by
  set N : ℝ := 2 ^ (p + 60) with hNdef
  set r : ℤ := Int.fmod j k with hrdef
  set θ : ℝ := 2 * Real.pi * (r:ℝ) / (k:ℝ) with hθdef
  have hkpos : 0 < k := hk
  have hkZ : (0:ℤ) < (k:ℤ) := by exact_mod_cast hkpos
  have hkRpos : (0:ℝ) < (k:ℝ) := by exact_mod_cast hkpos
  have hNpos : 0 < N := by rw [hNdef]; positivity
  have hN100 : 100 ≤ N := by
    rw [hNdef]
    calc (100:ℝ) ≤ 2^7 := by norm_num
      _ ≤ 2^(p+60) := pow_le_pow_right₀ (by norm_num) (by omega)
  have hr0 : 0 ≤ r := by
    rw [hrdef, Int.fmod_eq_emod_of_nonneg j (le_of_lt hkZ)]
    exact Int.emod_nonneg j (ne_of_gt hkZ)
  have hrk : r < (k:ℤ) := by
    rw [hrdef, Int.fmod_eq_emod_of_nonneg j (le_of_lt hkZ)]
    exact Int.emod_lt_of_pos j hkZ
  have hrR0 : (0:ℝ) ≤ (r:ℝ) := by exact_mod_cast hr0
  have hrkR : (r:ℝ) < (k:ℝ) := by exact_mod_cast hrk
  have hRθ : |(R:ℝ) - N * θ| ≤ 3 := by rw [hNdef, hθdef, hrdef]; exact hR
  have hθ0 : 0 ≤ θ := by
    rw [hθdef]
    exact div_nonneg (mul_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le) hrR0) hkRpos.le
  have hθ2π : θ ≤ 2 * Real.pi := by
    rw [hθdef, div_le_iff₀ hkRpos]
    exact mul_le_mul_of_nonneg_left (le_of_lt hrkR) (by positivity)
  have hz : (((-64 : ℤ) : ℂ) + (R : ℂ) * Complex.I) / (2 : ℂ) ^ (p + 60)
      = ((-64 / N : ℝ) : ℂ) + (((R:ℝ) / N : ℝ) : ℂ) * Complex.I := by
    have hcast : (2:ℂ) = ((2:ℝ):ℂ) := by norm_num
    rw [hNdef, hcast, ← Complex.ofReal_pow, div_eq_mul_inv, ← Complex.ofReal_inv]
    push_cast
    ring
  refine ⟨?_, ?_, ?_⟩
  · -- first conjunct: `‖exp z‖ ≤ 1 − 32/N`
    rw [Complex.norm_exp]
    have hre : ((((-64 : ℤ) : ℂ) + (R : ℂ) * Complex.I) / (2 : ℂ) ^ (p + 60)).re = -64/N := by
      rw [hz]; simp [Complex.add_re, Complex.mul_re]
    rw [hre]
    have hle : 64 / N ≤ 2/3 := by rw [div_le_iff₀ hNpos]; nlinarith [hN100]
    have key := exp_neg_le_one_sub_half (a := 64/N) (by positivity) hle
    have e1 : (-64:ℝ)/N = -(64/N) := by ring
    have e2 : (64/N)/2 = 32/N := by ring_nf
    rw [e1, ← e2]
    exact key
  · -- second conjunct: `‖exp z − exp(2πi r/k)‖ ≤ 67/N`
    have hE : Complex.exp (2 * Real.pi * Complex.I * ((Int.fmod j k : ℤ) : ℂ) / (k : ℂ))
        = Complex.exp (((θ:ℝ):ℂ) * Complex.I) := by
      congr 1
      rw [hθdef, hrdef]
      push_cast
      ring_nf
    have hz2 : (((-64 : ℤ) : ℂ) + (R : ℂ) * Complex.I) / (2 : ℂ) ^ (p + 60)
        = (((-64/N : ℝ):ℂ) + (((R:ℝ)/N - θ : ℝ):ℂ)*Complex.I) + ((θ:ℝ):ℂ)*Complex.I := by
      rw [hz]; push_cast; ring
    have hEnorm : ‖Complex.exp (((θ:ℝ):ℂ) * Complex.I)‖ = 1 := by
      rw [show ((θ:ℝ):ℂ) * Complex.I = Complex.I * (θ:ℂ) by ring, Complex.norm_exp_I_mul_ofReal]
    have hdiff : Complex.exp ((((-64/N : ℝ):ℂ) + (((R:ℝ)/N - θ : ℝ):ℂ)*Complex.I)
          + ((θ:ℝ):ℂ)*Complex.I)
        - Complex.exp (((θ:ℝ):ℂ)*Complex.I)
        = Complex.exp (((θ:ℝ):ℂ)*Complex.I)
          * (Complex.exp (((-64/N : ℝ):ℂ) + (((R:ℝ)/N - θ : ℝ):ℂ)*Complex.I) - 1) := by
      rw [Complex.exp_add]; ring
    rw [hE, hz2, hdiff, norm_mul, hEnorm, one_mul]
    have ha : (-64/N : ℝ) ≤ 0 := by
      rw [show (-64:ℝ)/N = -(64/N) by ring]; exact neg_nonpos.mpr (by positivity)
    have hb : |(R:ℝ)/N - θ| ≤ 3/N := by
      have e : (R:ℝ)/N - θ = ((R:ℝ) - N*θ)/N := by field_simp
      rw [e, abs_div, abs_of_pos hNpos]
      exact div_le_div_of_nonneg_right hRθ hNpos.le
    have key := norm_exp_add_mul_I_sub_one_le (-64/N) ((R:ℝ)/N - θ) ha
    have hgoal : -(-64/N : ℝ) + |(R:ℝ)/N - θ| ≤ 67/N := by
      have e : -(-64/N : ℝ) = 64/N := by ring
      have e3 : (64:ℝ)/N + 3/N = 67/N := by ring
      rw [e]; linarith [hb, e3]
    linarith [key, hgoal]
  · -- third conjunct: `(−64)² + R² ≤ (32N)²`
    have hRle : (R:ℝ) ≤ 9 * N := by
      have h := (abs_le.mp hRθ).2
      have h1 : N * θ ≤ N * (2*Real.pi) := mul_le_mul_of_nonneg_left hθ2π hNpos.le
      have hp8 : (2:ℝ) * Real.pi ≤ 8 := by linarith [Real.pi_le_four]
      have h2 : N * (2*Real.pi) ≤ N * 8 := mul_le_mul_of_nonneg_left hp8 hNpos.le
      nlinarith [h, h1, h2, hN100]
    have hRge : -9 * N ≤ (R:ℝ) := by
      have h := (abs_le.mp hRθ).1
      have h3 : 0 ≤ N * θ := mul_nonneg hNpos.le hθ0
      nlinarith [h, h3, hN100]
    have hRsq : (R:ℝ)^2 ≤ (9*N)^2 := by nlinarith [hRle, hRge]
    have hNsq : (64:ℝ)^2 ≤ N^2 := by nlinarith [hN100]
    nlinarith [hRsq, hNsq, hN100]

end Work.Fx
