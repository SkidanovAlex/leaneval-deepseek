import Mathlib
import Submission.Work.BMF.v7chi_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-! # The eventual arithmetic for `chi_prime_sum_twist`

See `Work.BMF.v7chi_arith` for the statement.  Everything here is a consequence of
`log y = o(y^r)` (`r > 0`) and `y^r → ∞`, uniformly in `N`, `u` because the only information
used about them is `N ≤ (log x)^A` and `|u| ≤ exp((log x)^{21/20})`.
-/

namespace Work.BMF

open Filter
open scoped Topology

noncomputable section

/-! ## Generic eventual estimates -/

lemma v7chi_ev_log_add_two_le {r ε : ℝ} (hr : 0 < r) (hε : 0 < ε) :
    ∀ᶠ y : ℝ in atTop, Real.log (y + 2) ≤ ε * y ^ r := by
  have h1 : ∀ᶠ y : ℝ in atTop, Real.log y ≤ (ε / 2) * y ^ r :=
    v7chi_ev_log_le_mul_rpow hr (by linarith)
  filter_upwards [h1, eventually_ge_atTop (2 : ℝ)] with y h1y hy2
  have hlog2 : Real.log 2 ≤ Real.log y := Real.log_le_log (by norm_num) hy2
  calc Real.log (y + 2) ≤ Real.log (2 * y) :=
        Real.log_le_log (by linarith) (by linarith)
    _ = Real.log 2 + Real.log y := Real.log_mul (by norm_num) (by linarith)
    _ ≤ ε / 2 * y ^ r + ε / 2 * y ^ r := by linarith
    _ = ε * y ^ r := by ring

lemma v7chi_ev_mul_pow_le_exp {r δ : ℝ} (hr : 0 < r) (hδ : 0 < δ) (C : ℝ) (k : ℕ) :
    ∀ᶠ y : ℝ in atTop, C * (y + 2) ^ k ≤ Real.exp (δ * y ^ r) := by
  by_cases hC : C ≤ 0
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with y hy
    exact le_trans (mul_nonpos_of_nonpos_of_nonneg hC (by positivity)) (Real.exp_pos _).le
  · have h1 : ∀ᶠ y : ℝ in atTop, C ≤ Real.exp ((δ / 2) * y ^ r) :=
      v7chi_ev_const_le_exp (by linarith) hr
    have h2 : ∀ᶠ y : ℝ in atTop, (y + 2) ^ k ≤ Real.exp ((δ / 2) * y ^ r) := by
      rcases Nat.eq_zero_or_pos k with hk | hk
      · subst hk
        filter_upwards [eventually_ge_atTop (0 : ℝ)] with y hy0
        simpa using Real.one_le_exp
          (mul_nonneg (by linarith : (0 : ℝ) ≤ δ / 2) (Real.rpow_nonneg hy0 r))
      · have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
        have h3 : ∀ᶠ y : ℝ in atTop, Real.log (y + 2) ≤ (δ / (2 * k)) * y ^ r :=
          v7chi_ev_log_add_two_le hr (div_pos hδ (by linarith : (0 : ℝ) < 2 * (k : ℝ)))
        filter_upwards [h3, eventually_ge_atTop (0 : ℝ)] with y hy hy0
        have hy2 : (0 : ℝ) < y + 2 := by linarith
        rw [← Real.log_le_iff_le_exp (pow_pos hy2 k), Real.log_pow]
        calc ((k : ℝ) * Real.log (y + 2)) ≤ (k : ℝ) * ((δ / (2 * (k : ℝ))) * y ^ r) :=
              mul_le_mul_of_nonneg_left hy (Nat.cast_nonneg k)
          _ = (δ / 2) * y ^ r := by
              field_simp
    filter_upwards [h1, h2, eventually_ge_atTop (0 : ℝ)] with y h1y h2y hy0
    calc C * (y + 2) ^ k ≤ Real.exp ((δ / 2) * y ^ r) * Real.exp ((δ / 2) * y ^ r) :=
          mul_le_mul h1y h2y (pow_nonneg (by linarith : (0 : ℝ) ≤ y + 2) k)
            (Real.exp_pos _).le
      _ = Real.exp (δ * y ^ r) := by
          rw [← Real.exp_add]; congr 1; ring

lemma v7chi_ev_exp_half_le {c : ℝ} (hc : 0 < c) :
    ∀ᶠ y : ℝ in atTop,
      Real.exp (y ^ (1 / 2 : ℝ) / 2) ≤ Real.exp (y ^ (1 / 2 : ℝ) - c * y ^ (1 / 12 : ℝ)) := by
  have h : ∀ᶠ y : ℝ in atTop, 2 * c ≤ y ^ (5 / 12 : ℝ) :=
    v7chi_ev_const_le_rpow (by norm_num : (0 : ℝ) < 5 / 12)
  filter_upwards [h, eventually_ge_atTop (1 : ℝ)] with y hy hy1
  rw [Real.exp_le_exp]
  have hy0 : (0 : ℝ) < y := by linarith
  have h' : 2 * c * y ^ (1 / 12 : ℝ) ≤ y ^ (5 / 12 : ℝ) * y ^ (1 / 12 : ℝ) :=
    mul_le_mul_of_nonneg_right hy (Real.rpow_nonneg hy0.le _)
  rw [← Real.rpow_add hy0, show (5 : ℝ) / 12 + 1 / 12 = 1 / 2 by norm_num] at h'
  linarith

lemma v7chi_ev_exp_half_le' {c : ℝ} (hc : 0 < c) :
    ∀ᶠ y : ℝ in atTop, Real.exp (y / 2) ≤ Real.exp (y - c * y ^ (1 / 12 : ℝ)) := by
  have h : ∀ᶠ y : ℝ in atTop, 2 * c ≤ y ^ (11 / 12 : ℝ) :=
    v7chi_ev_const_le_rpow (by norm_num : (0 : ℝ) < 11 / 12)
  filter_upwards [h, eventually_ge_atTop (1 : ℝ)] with y hy hy1
  rw [Real.exp_le_exp]
  have hy0 : (0 : ℝ) < y := by linarith
  have h' : 2 * c * y ^ (1 / 12 : ℝ) ≤ y ^ (11 / 12 : ℝ) * y ^ (1 / 12 : ℝ) :=
    mul_le_mul_of_nonneg_right hy (Real.rpow_nonneg hy0.le _)
  rw [← Real.rpow_add hy0, show (11 : ℝ) / 12 + 1 / 12 = 1 by norm_num, Real.rpow_one] at h'
  linarith

lemma v7chi_ev_const_le_mul_rpow {r ε C : ℝ} (hr : 0 < r) (hε : 0 < ε) :
    ∀ᶠ y : ℝ in atTop, C ≤ ε * y ^ r :=
  ((tendsto_const_mul_atTop_of_pos hε).mpr (tendsto_rpow_atTop hr)).eventually_ge_atTop C

set_option maxHeartbeats 4000000 in
/-- **Eventual uniform arithmetic for the contour of `chi_prime_sum_twist`.**

With `L = log x`, `T = v7chiT x = exp(√L)`, `U = v7chiU u T = |u| + T + 3`,
`D = v7chiD N u T = (log U)^{6/7}(log(N+2) + log log U)`,
`δ = v7chidelta c₄ c₅ (1/(20A)) N u T = min(min(c₄/(2D), c₅ N^{-1/(20A)}/2), 1/4)`,
`σ₁ = 1 - δ`, `B = v7chiB C₄ C₅ (1/(20A)) N u T = C₄ (log(N U))^4 + C₅ (N^{1/(20A)} + log(N+2)^2)`
and `x' = ⌊x⌋ + 1/2`, for `N ≥ 2`, `N ≤ (log x)^A` and `|u| ≤ exp((log x)^{21/20})`,
eventually in `x`, the nine inequalities needed by the final assembly hold. -/
theorem v7chi_arith (A c c₄ c₅ C₄ C₅ C_red C_p : ℝ)
    (hA : 0 < A) (hc : 0 < c) (hc₄ : 0 < c₄) (hc₅ : 0 < c₅) (hC₄ : 0 < C₄) (hC₅ : 0 < C₅)
    (hC_red : 0 ≤ C_red) (hC_p : 0 ≤ C_p) :
    ∀ᶠ x : ℝ in Filter.atTop, ∀ (N : ℕ) [NeZero N], 2 ≤ N → (N : ℝ) ≤ Real.log x ^ A →
      ∀ u : ℝ, |u| ≤ Real.exp (Real.log x ^ (21 / 20 : ℝ)) →
        let L := Real.log x
        let T := v7chiT x
        let δ := v7chidelta c₄ c₅ (1 / (20 * A)) N u T
        let σ₁ := 1 - δ
        let B := v7chiB C₄ C₅ (1 / (20 * A)) N u T
        let x' := (⌊x⌋₊ : ℝ) + 1 / 2
        (2 ≤ T ∧ 0 < δ ∧ δ ≤ 1 / 4 ∧ 2 ≤ x ∧ 1000 ≤ L ∧
          Real.exp (-(δ * L)) ≤ Real.exp (-(c * L ^ (1 / 12 : ℝ))) / (L + 2) ^ 20 ∧
          B * (3 + 3 * Real.log (2 + T / σ₁)) ≤ (1 / 16) * (L + 2) ^ 20 ∧
          16 * B * Real.exp 1 ≤ Real.exp (L ^ (1 / 2 : ℝ) - c * L ^ (1 / 12 : ℝ)) ∧
          16 * C_p * (L + 1) ^ 2 ≤ Real.exp (L ^ (1 / 2 : ℝ) - c * L ^ (1 / 12 : ℝ)) ∧
          8 * C_p * (L + 1) ≤ Real.exp (L - c * L ^ (1 / 12 : ℝ)) ∧
          4 * C_red * (A * Real.log (L + 2) + Real.log 2) * (L + 2) ≤
            Real.exp (L - c * L ^ (1 / 12 : ℝ)) ∧
          x' ≤ 2 * x ∧ Real.log x' ≤ L + 1) := by
  have hlog : Tendsto Real.log Filter.atTop Filter.atTop := Real.tendsto_log_atTop
  have expT : Tendsto (fun y : ℝ => Real.exp (y ^ (1 / 2 : ℝ))) Filter.atTop Filter.atTop :=
    Real.tendsto_exp_atTop.comp (tendsto_rpow_atTop (by norm_num))
  have expT' : Tendsto (fun y : ℝ => Real.exp (y ^ (21 / 20 : ℝ))) Filter.atTop Filter.atTop :=
    Real.tendsto_exp_atTop.comp (tendsto_rpow_atTop (by norm_num))
  -- (0) exactly two facts about x
  have ex1 : ∀ᶠ x : ℝ in Filter.atTop, 1000 ≤ Real.log x :=
    hlog.eventually (eventually_ge_atTop 1000)
  have ex3 : ∀ᶠ x : ℝ in Filter.atTop, (2 : ℝ) ≤ x := eventually_ge_atTop 2
  have ex2 : ∀ᶠ x : ℝ in Filter.atTop, 2 ≤ v7chiT x := by
    filter_upwards [hlog.eventually (expT.eventually_ge_atTop 2)] with x hx
    simpa only [v7chiT] using hx
  -- (1) facts depending only on `L = log x`
  have e3 : ∀ᶠ x : ℝ in Filter.atTop,
      Real.log (Real.log x) ≤ Real.log x ^ (21 / 20 : ℝ) := by
    filter_upwards [hlog.eventually (v7chi_ev_log_le_mul_rpow (r := 21 / 20) (ε := 1)
      (by norm_num) (by norm_num))] with x hx
    simpa using hx
  have e4 : ∀ᶠ x : ℝ in Filter.atTop, Real.log 2 ≤ Real.log (Real.log x) := by
    filter_upwards [ex1] with x hx
    exact Real.log_le_log (by norm_num) (le_trans (by norm_num : (2 : ℝ) ≤ 1000) hx)
  have e5 : ∀ᶠ x : ℝ in Filter.atTop, (3 : ℝ) ≤ Real.exp (Real.log x ^ (21 / 20 : ℝ)) :=
    hlog.eventually (expT'.eventually_ge_atTop 3)
  have e6 : ∀ᶠ x : ℝ in Filter.atTop,
      Real.log 3 + Real.log x ^ (21 / 20 : ℝ) ≤ (21 / 20) * Real.log x ^ (21 / 20 : ℝ) := by
    filter_upwards [hlog.eventually (v7chi_ev_const_le_mul_rpow (r := 21 / 20) (ε := 1 / 20)
      (C := Real.log 3) (by norm_num) (by norm_num))] with x hx
    linarith
  have e7 : ∀ᶠ x : ℝ in Filter.atTop, (2 : ℝ) ≤ Real.log x ^ A :=
    hlog.eventually (v7chi_ev_const_le_rpow hA (C := 2))
  have e8 : ∀ᶠ x : ℝ in Filter.atTop,
      Real.log (21 / 20) ≤ (1 / 20) * Real.log (Real.log x) := by
    filter_upwards [ex1] with x hx
    have h1 : Real.log (21 / 20) ≤ 1 / 20 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 21 / 20)
      linarith
    have h2 : (1 : ℝ) ≤ Real.log (Real.log x) := by
      rw [Real.le_log_iff_exp_le (by linarith : (0 : ℝ) < Real.log x)]
      have h3 : Real.exp 1 < 3 := Real.exp_one_lt_three
      linarith
    linarith
  have e9 : ∀ᶠ x : ℝ in Filter.atTop,
      (A + 1) ^ 2 * (Real.log (Real.log x)) ^ 2 ≤ (A + 4) ^ 4 * Real.log x ^ (21 / 5 : ℝ) := by
    have h1 : ∀ᶠ y : ℝ in Filter.atTop, (Real.log y) ^ 2 ≤ y ^ (21 / 5 : ℝ) := by
      filter_upwards [v7chi_ev_log_le_mul_rpow (r := 21 / 10) (ε := 1) (by norm_num) (by norm_num),
        eventually_ge_atTop (1 : ℝ)] with y hy hy1
      have hlog0 : 0 ≤ Real.log y := Real.log_nonneg hy1
      have hy0 : (0 : ℝ) < y := by linarith
      calc (Real.log y) ^ 2 ≤ (1 * y ^ (21 / 10 : ℝ)) ^ 2 := pow_le_pow_left₀ hlog0 hy 2
        _ = y ^ (21 / 5 : ℝ) := by
            rw [one_mul, pow_two, ← Real.rpow_add hy0,
              show (21 : ℝ) / 10 + 21 / 10 = 21 / 5 by norm_num]
    filter_upwards [hlog.eventually h1] with x hx
    have hA1 : (A + 1) ^ 2 ≤ (A + 4) ^ 4 := by
      have h1 : A + 1 ≤ A + 4 := by linarith
      have h2 : ((A + 4) ^ 2) ^ 2 = (A + 4) ^ 4 := by ring
      calc (A + 1) ^ 2 ≤ (A + 4) ^ 2 := pow_le_pow_left₀ (by linarith) h1 2
        _ ≤ ((A + 4) ^ 2) ^ 2 := by
            have h3 : (1 : ℝ) ≤ (A + 4) ^ 2 := one_le_pow₀ (by linarith : (1 : ℝ) ≤ A + 4)
            nlinarith [h3]
        _ = (A + 4) ^ 4 := h2
    exact mul_le_mul hA1 hx (sq_nonneg (Real.log (Real.log x))) (by positivity)
  have e10 : ∀ᶠ x : ℝ in Filter.atTop,
      144 * ((C₄ + 2 * C₅ + 1) * (A + 4) ^ 4) * Real.log x ^ (21 / 5 : ℝ) *
          Real.log x ^ (1 / 2 : ℝ) ≤ (Real.log x + 2) ^ 20 := by
    have h1 : ∀ᶠ y : ℝ in Filter.atTop,
        144 * ((C₄ + 2 * C₅ + 1) * (A + 4) ^ 4) ≤ y ^ (15 : ℝ) :=
      v7chi_ev_const_le_rpow (r := 15) (by norm_num)
        (C := 144 * ((C₄ + 2 * C₅ + 1) * (A + 4) ^ 4))
    filter_upwards [hlog.eventually h1, eventually_ge_atTop (Real.exp 1)] with x hy hy1
    set w := Real.log x with hw
    have hw1 : 1 ≤ w := by
      rw [hw, Real.le_log_iff_exp_le (by linarith only [hy1, Real.exp_pos 1])]
      exact hy1
    have hw0 : 0 < w := by linarith
    have hmul : w ^ (21 / 5 : ℝ) * w ^ (1 / 2 : ℝ) = w ^ (47 / 10 : ℝ) := by
      rw [← Real.rpow_add hw0]; norm_num
    have hle : w ^ (47 / 10 : ℝ) ≤ (w + 2) ^ 5 := by
      calc w ^ (47 / 10 : ℝ) ≤ (w + 2) ^ (47 / 10 : ℝ) :=
            Real.rpow_le_rpow hw0.le (by linarith) (by norm_num)
        _ ≤ (w + 2) ^ (5 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
        _ = (w + 2) ^ 5 := Real.rpow_natCast _ 5
    calc 144 * ((C₄ + 2 * C₅ + 1) * (A + 4) ^ 4) * w ^ (21 / 5 : ℝ) * w ^ (1 / 2 : ℝ)
        = (144 * ((C₄ + 2 * C₅ + 1) * (A + 4) ^ 4)) * w ^ (47 / 10 : ℝ) := by
          rw [← hmul]; ring
      _ ≤ w ^ (15 : ℝ) * w ^ (47 / 10 : ℝ) :=
          mul_le_mul_of_nonneg_right hy (Real.rpow_nonneg hw0.le _)
      _ ≤ (w + 2) ^ 15 * (w + 2) ^ 5 := by
          have h2 : w ^ (15 : ℝ) ≤ (w + 2) ^ 15 := by
            rw [← Real.rpow_natCast (w + 2) 15]
            exact Real.rpow_le_rpow hw0.le (by linarith) (by norm_num)
          exact mul_le_mul h2 hle (Real.rpow_nonneg hw0.le _) (by positivity)
      _ = (w + 2) ^ 20 := by rw [← pow_add]
  have e11 : ∀ᶠ x : ℝ in Filter.atTop,
      Real.log x ^ (21 / 5 : ℝ) ≤ (Real.log x + 2) ^ 5 := by
    filter_upwards [eventually_ge_atTop (Real.exp 1)] with x hx
    have hL0 : (0 : ℝ) < Real.log x := by
      apply Real.log_pos
      have h1 : (1 : ℝ) < Real.exp 1 := Real.one_lt_exp_iff.mpr (by norm_num)
      linarith
    calc Real.log x ^ (21 / 5 : ℝ) ≤ (Real.log x + 2) ^ (21 / 5 : ℝ) :=
          Real.rpow_le_rpow hL0.le (by linarith) (by norm_num)
      _ ≤ (Real.log x + 2) ^ (5 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
      _ = (Real.log x + 2) ^ 5 := Real.rpow_natCast _ 5
  have e12 : ∀ᶠ x : ℝ in Filter.atTop,
      16 * ((C₄ + 2 * C₅ + 1) * (A + 4) ^ 4) * Real.exp 1 * (Real.log x + 2) ^ 5 ≤
        Real.exp (Real.log x ^ (1 / 2 : ℝ) / 2) := by
    have h := v7chi_ev_mul_pow_le_exp (r := 1 / 2) (δ := 1 / 2)
      (C := 16 * ((C₄ + 2 * C₅ + 1) * (A + 4) ^ 4) * Real.exp 1) (k := 5) (by norm_num) (by norm_num)
    filter_upwards [hlog.eventually h] with x hx
    calc 16 * ((C₄ + 2 * C₅ + 1) * (A + 4) ^ 4) * Real.exp 1 * (Real.log x + 2) ^ 5
        ≤ Real.exp (1 / 2 * Real.log x ^ (1 / 2 : ℝ)) := hx
      _ = Real.exp (Real.log x ^ (1 / 2 : ℝ) / 2) := by
          congr 1
          ring_nf
  have e13 : ∀ᶠ x : ℝ in Filter.atTop,
      Real.exp (Real.log x ^ (1 / 2 : ℝ) / 2) ≤
        Real.exp (Real.log x ^ (1 / 2 : ℝ) - c * Real.log x ^ (1 / 12 : ℝ)) :=
    hlog.eventually (v7chi_ev_exp_half_le hc)
  have e14 : ∀ᶠ x : ℝ in Filter.atTop,
      16 * C_p * (Real.log x + 2) ^ 2 ≤ Real.exp (Real.log x ^ (1 / 2 : ℝ) / 2) := by
    have h := v7chi_ev_mul_pow_le_exp (r := 1 / 2) (δ := 1 / 2) (C := 16 * C_p) (k := 2)
      (by norm_num) (by norm_num)
    filter_upwards [hlog.eventually h] with x hx
    calc 16 * C_p * (Real.log x + 2) ^ 2 ≤ Real.exp (1 / 2 * Real.log x ^ (1 / 2 : ℝ)) := hx
      _ = Real.exp (Real.log x ^ (1 / 2 : ℝ) / 2) := by
          congr 1
          ring_nf
  have e15 : ∀ᶠ x : ℝ in Filter.atTop,
      8 * C_p * (Real.log x + 2) ≤ Real.exp (Real.log x / 2) := by
    have h := v7chi_ev_mul_pow_le_exp (r := 1) (δ := 1 / 2) (C := 8 * C_p) (k := 1)
      (by norm_num) (by norm_num)
    filter_upwards [hlog.eventually h] with x hx
    calc 8 * C_p * (Real.log x + 2) ≤ Real.exp (1 / 2 * Real.log x ^ (1 : ℝ)) := by
          simpa only [pow_one, Real.rpow_one] using hx
      _ = Real.exp (Real.log x / 2) := by
          congr 1
          rw [Real.rpow_one]
          ring_nf
  have e16 : ∀ᶠ x : ℝ in Filter.atTop,
      Real.exp (Real.log x / 2) ≤ Real.exp (Real.log x - c * Real.log x ^ (1 / 12 : ℝ)) :=
    hlog.eventually (v7chi_ev_exp_half_le' hc)
  have e17 : ∀ᶠ x : ℝ in Filter.atTop,
      4 * C_red * (A + 1) * (Real.log x + 2) ^ 3 ≤ Real.exp (Real.log x / 2) := by
    have h := v7chi_ev_mul_pow_le_exp (r := 1) (δ := 1 / 2) (C := 4 * C_red * (A + 1)) (k := 3)
      (by norm_num) (by norm_num)
    filter_upwards [hlog.eventually h] with x hx
    calc 4 * C_red * (A + 1) * (Real.log x + 2) ^ 3
        ≤ Real.exp (1 / 2 * Real.log x ^ (1 : ℝ)) := hx
      _ = Real.exp (1 / 2 * Real.log x) := by rw [Real.rpow_one]
      _ = Real.exp (Real.log x / 2) := by
          congr 1
          ring_nf
  have e22 : ∀ᶠ x : ℝ in Filter.atTop, Real.log 3 ≤ Real.log x ^ (1 / 2 : ℝ) := by
    filter_upwards [hlog.eventually (v7chi_ev_const_le_mul_rpow (r := 1 / 2) (ε := 1 / 2)
      (C := Real.log 3) (by norm_num) (by norm_num)), eventually_ge_atTop (1 : ℝ)]
      with x hx hx1
    have hL0 : 0 ≤ Real.log x := Real.log_nonneg hx1
    have h2 : 0 ≤ Real.log x ^ (1 / 2 : ℝ) := Real.rpow_nonneg hL0 _
    linarith
  have e18 : ∀ᶠ x : ℝ in Filter.atTop,
      16 * c * (A + 4) * Real.log (Real.log x) ≤ c₄ * Real.log x ^ (1 / 60 : ℝ) := by
    filter_upwards [hlog.eventually (v7chi_ev_log_le_mul_rpow (r := 1 / 60)
      (ε := c₄ / (16 * (c * (A + 4)))) (by norm_num) (by positivity))] with x hx
    have hpos : 0 < 16 * (c * (A + 4)) := by positivity
    calc 16 * c * (A + 4) * Real.log (Real.log x)
        = 16 * (c * (A + 4)) * Real.log (Real.log x) := by ring
      _ ≤ 16 * (c * (A + 4)) * (c₄ / (16 * (c * (A + 4))) * Real.log x ^ (1 / 60)) :=
          mul_le_mul_of_nonneg_left hx hpos.le
      _ = c₄ * Real.log x ^ (1 / 60 : ℝ) := by field_simp
  have e19 : ∀ᶠ x : ℝ in Filter.atTop,
      320 * (A + 4) * Real.log (Real.log x + 2) * Real.log (Real.log x) ≤
        c₄ * Real.log x ^ (1 / 10 : ℝ) := by
    set ε := min 1 (c₄ / (640 * (A + 4))) with hεdef
    have hεpos : 0 < ε := lt_min (by norm_num) (by positivity)
    have hε1 : ε ≤ 1 := min_le_left _ _
    have hε2 : ε ≤ c₄ / (640 * (A + 4)) := min_le_right _ _
    have h1 : ∀ᶠ y : ℝ in Filter.atTop, Real.log y ≤ ε * y ^ (1 / 20 : ℝ) :=
      v7chi_ev_log_le_mul_rpow (by norm_num) hεpos
    have h2 : ∀ᶠ y : ℝ in Filter.atTop, Real.log (y + 2) ≤ 2 * Real.log y := by
      filter_upwards [eventually_ge_atTop (4 : ℝ)] with y hy
      have hy0 : 0 < y := by linarith
      have hlogy : 1 ≤ Real.log y := by
        rw [Real.le_log_iff_exp_le hy0]
        have h3 : Real.exp 1 < 3 := Real.exp_one_lt_three
        linarith
      calc Real.log (y + 2) ≤ Real.log (2 * y) := Real.log_le_log (by linarith) (by linarith)
        _ = Real.log 2 + Real.log y := Real.log_mul (by norm_num) (by linarith)
        _ ≤ Real.log y + Real.log y := by linarith [Real.log_two_lt_d9]
        _ = 2 * Real.log y := by ring
    filter_upwards [hlog.eventually h1, hlog.eventually h2, eventually_ge_atTop (3 : ℝ)]
      with x h1x h2x hx3
    have hL0 : (0 : ℝ) < Real.log x := by
      apply Real.log_pos
      have h3 : Real.exp 1 < 3 := Real.exp_one_lt_three
      linarith
    have hlogL : 0 ≤ Real.log (Real.log x) := by
      apply Real.log_nonneg
      rw [Real.le_log_iff_exp_le (by linarith : (0 : ℝ) < x)]
      have h3 : Real.exp 1 < 3 := Real.exp_one_lt_three
      linarith
    have hexp : Real.log (Real.log x) * Real.log (Real.log x) ≤ ε * Real.log x ^ (1 / 10 : ℝ) := by
      have hp : (0 : ℝ) ≤ ε * Real.log x ^ (1 / 20 : ℝ) := by positivity
      have hmul := mul_le_mul h1x h1x hlogL hp
      have heq : (ε * Real.log x ^ (1 / 20 : ℝ)) * (ε * Real.log x ^ (1 / 20 : ℝ))
          = ε ^ 2 * Real.log x ^ (1 / 10 : ℝ) := by
        rw [show (ε * Real.log x ^ (1 / 20 : ℝ)) * (ε * Real.log x ^ (1 / 20 : ℝ))
            = (ε * ε) * (Real.log x ^ (1 / 20 : ℝ) * Real.log x ^ (1 / 20 : ℝ)) by ring,
          ← Real.rpow_add hL0, pow_two]
        norm_num
      rw [heq] at hmul
      calc Real.log (Real.log x) * Real.log (Real.log x) ≤ ε ^ 2 * Real.log x ^ (1 / 10 : ℝ) := hmul
        _ ≤ ε * Real.log x ^ (1 / 10 : ℝ) := by
            have hε2' : ε ^ 2 ≤ ε := by nlinarith
            exact mul_le_mul_of_nonneg_right hε2' (Real.rpow_nonneg hL0.le _)
    calc 320 * (A + 4) * Real.log (Real.log x + 2) * Real.log (Real.log x)
        ≤ 320 * (A + 4) * (2 * Real.log (Real.log x)) * Real.log (Real.log x) := by
          have hfac : 0 ≤ 320 * (A + 4) * Real.log (Real.log x) := by positivity
          have hh := mul_le_mul_of_nonneg_right h2x hfac
          nlinarith only [hh]
      _ = 640 * (A + 4) * (Real.log (Real.log x) * Real.log (Real.log x)) := by ring
      _ ≤ 640 * (A + 4) * (ε * Real.log x ^ (1 / 10 : ℝ)) :=
          mul_le_mul_of_nonneg_left hexp (by positivity)
      _ ≤ c₄ * Real.log x ^ (1 / 10 : ℝ) := by
          have hle : 640 * (A + 4) * ε ≤ c₄ := by
            calc 640 * (A + 4) * ε ≤ 640 * (A + 4) * (c₄ / (640 * (A + 4))) :=
                  mul_le_mul_of_nonneg_left hε2 (by positivity)
              _ = c₄ := by field_simp
          nlinarith only [hle, Real.rpow_nonneg hL0.le (1 / 10 : ℝ)]
  have e20 : ∀ᶠ x : ℝ in Filter.atTop,
      c * Real.log x ^ (1 / 12 : ℝ) + 20 * Real.log (Real.log x + 2) ≤
        c₅ * Real.log x ^ (19 / 20 : ℝ) / 2 := by
    have hA' : ∀ᶠ y : ℝ in Filter.atTop, 4 * c / c₅ ≤ y ^ (13 / 15 : ℝ) :=
      v7chi_ev_const_le_rpow (r := 13 / 15) (by norm_num) (C := 4 * c / c₅)
    have hB' : ∀ᶠ y : ℝ in Filter.atTop, Real.log (y + 2) ≤ (c₅ / 80) * y ^ (19 / 20 : ℝ) :=
      v7chi_ev_log_add_two_le (by norm_num) (by positivity)
    filter_upwards [hlog.eventually hA', hlog.eventually hB', eventually_ge_atTop (3 : ℝ)]
      with x hA'' hB'' hx3
    have hL0 : 0 < Real.log x := by
      apply Real.log_pos
      have h3 : Real.exp 1 < 3 := Real.exp_one_lt_three
      linarith
    have hp19 : 0 < Real.log x ^ (19 / 20 : ℝ) := Real.rpow_pos_of_pos hL0 _
    have hp12pos : 0 < Real.log x ^ (1 / 12 : ℝ) := Real.rpow_pos_of_pos hL0 _
    have h1 : c * Real.log x ^ (1 / 12 : ℝ) ≤ c₅ * Real.log x ^ (19 / 20 : ℝ) / 4 := by
      have hmul : (4 * c / c₅) * Real.log x ^ (1 / 12 : ℝ)
          ≤ Real.log x ^ (13 / 15 : ℝ) * Real.log x ^ (1 / 12 : ℝ) :=
        mul_le_mul_of_nonneg_right hA'' hp12pos.le
      rw [← Real.rpow_add hL0, show (13 : ℝ) / 15 + 1 / 12 = 19 / 20 by norm_num] at hmul
      have h3 : (c₅ / 4) * ((4 * c / c₅) * Real.log x ^ (1 / 12 : ℝ))
          ≤ (c₅ / 4) * Real.log x ^ (19 / 20 : ℝ) :=
        mul_le_mul_of_nonneg_left hmul (by positivity)
      have h4 : (c₅ / 4) * ((4 * c / c₅) * Real.log x ^ (1 / 12 : ℝ))
          = c * Real.log x ^ (1 / 12 : ℝ) := by field_simp
      have h5 : (c₅ / 4) * Real.log x ^ (19 / 20 : ℝ) = c₅ * Real.log x ^ (19 / 20 : ℝ) / 4 := by
        ring
      rw [h4, h5] at h3
      exact h3
    have h2 : 20 * Real.log (Real.log x + 2) ≤ c₅ * Real.log x ^ (19 / 20 : ℝ) / 4 := by
      have := mul_le_mul_of_nonneg_left hB'' (by norm_num : (0 : ℝ) ≤ 20)
      have he : 20 * ((c₅ / 80) * Real.log x ^ (19 / 20 : ℝ))
          = c₅ * Real.log x ^ (19 / 20 : ℝ) / 4 := by ring
      linarith [this, he.symm.le, he.le]
    linarith
  have e21 : ∀ᶠ x : ℝ in Filter.atTop,
      c * Real.log x ^ (1 / 12 : ℝ) + 20 * Real.log (Real.log x + 2) ≤ Real.log x / 4 := by
    have hA' : ∀ᶠ y : ℝ in Filter.atTop, 8 * c ≤ y ^ (11 / 12 : ℝ) :=
      v7chi_ev_const_le_rpow (r := 11 / 12) (by norm_num) (C := 8 * c)
    have hB' : ∀ᶠ y : ℝ in Filter.atTop, Real.log (y + 2) ≤ (1 / 160) * y ^ (1 : ℝ) :=
      v7chi_ev_log_add_two_le (r := 1) (by norm_num) (by norm_num)
    filter_upwards [hlog.eventually hA', hlog.eventually hB', eventually_ge_atTop (3 : ℝ)]
      with x hA'' hB'' hx3
    have hL0 : 0 < Real.log x := by
      apply Real.log_pos
      have h3 : Real.exp 1 < 3 := Real.exp_one_lt_three
      linarith
    have hp12pos : 0 < Real.log x ^ (1 / 12 : ℝ) := Real.rpow_pos_of_pos hL0 _
    have h1 : c * Real.log x ^ (1 / 12 : ℝ) ≤ Real.log x / 8 := by
      have hmul : 8 * c * Real.log x ^ (1 / 12 : ℝ)
          ≤ Real.log x ^ (11 / 12 : ℝ) * Real.log x ^ (1 / 12 : ℝ) :=
        mul_le_mul_of_nonneg_right hA'' hp12pos.le
      rw [← Real.rpow_add hL0, show (11 : ℝ) / 12 + 1 / 12 = 1 by norm_num,
        Real.rpow_one] at hmul
      linarith
    have h2 : 20 * Real.log (Real.log x + 2) ≤ Real.log x / 8 := by
      rw [Real.rpow_one] at hB''
      have := mul_le_mul_of_nonneg_left hB'' (by norm_num : (0 : ℝ) ≤ 20)
      linarith only [this]
    have hsum := add_le_add h1 h2
    linarith only [hsum]
  filter_upwards [ex1, ex3, ex2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16,
    e17, e18, e19, e20, e21, e22] with
    x h1000 hx2' hT2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22
  intro N _inst hN2 hNL u hu
  set L := Real.log x with hLdef
  set T := v7chiT x with hTdef
  set δ := v7chidelta c₄ c₅ (1 / (20 * A)) N u T with hδdef
  set B := v7chiB C₄ C₅ (1 / (20 * A)) N u T with hBdef
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (by omega : 1 ≤ N)
  have h1000L : 1000 ≤ L := h1000
  have hLpos : 0 < L := by linarith
  have hL2 : 1 ≤ L := by linarith
  have hLp2 : 0 < L + 2 := by linarith
  have hlogL : 0 < Real.log L := Real.log_pos (by linarith)
  have hTpos : 0 < T := by rw [hTdef]; exact v7chiT_pos x
  have hδpos : 0 < δ := by
    rw [hδdef]; exact v7chidelta_pos hc₄ hc₅ (by omega : 1 ≤ N) (le_of_lt (v7chiT_pos x))
  have hδ4 : δ ≤ 1 / 4 := by
    rw [hδdef]; exact v7chidelta_le_quarter c₄ c₅ (1 / (20 * A)) N u T
  have hU3 : 3 ≤ v7chiU u T := v7chiU_ge_three u T hTpos.le
  have hUpos : 0 < v7chiU u T := by linarith
  -- log N
  have hlogN_le : Real.log (N : ℝ) ≤ A * Real.log L := by
    calc Real.log (N : ℝ) ≤ Real.log (L ^ A) := Real.log_le_log (by linarith) hNL
      _ = A * Real.log L := Real.log_rpow hLpos A
  -- U ≤ exp(L^{21/20}) up to 3
  have hTle : T ≤ Real.exp (L ^ (21 / 20 : ℝ)) := by
    rw [hTdef, v7chiT]
    exact Real.exp_le_exp.mpr (Real.rpow_le_rpow_of_exponent_le hL2 (by norm_num))
  have hUle : v7chiU u T ≤ 3 * Real.exp (L ^ (21 / 20 : ℝ)) := by
    have := abs_le.mp hu
    simp only [v7chiU]
    linarith [hTle, h5]
  have hlogU : Real.log (v7chiU u T) ≤ (21 / 20) * L ^ (21 / 20 : ℝ) := by
    calc Real.log (v7chiU u T) ≤ Real.log (3 * Real.exp (L ^ (21 / 20 : ℝ))) :=
          Real.log_le_log hUpos hUle
      _ = Real.log 3 + L ^ (21 / 20 : ℝ) := by
          rw [Real.log_mul (by norm_num) (Real.exp_ne_zero _), Real.log_exp]
      _ ≤ (21 / 20) * L ^ (21 / 20 : ℝ) := h6
  have hlogNU : Real.log ((N : ℝ) * v7chiU u T) ≤ (A + 4) * L ^ (21 / 20 : ℝ) := by
    rw [Real.log_mul (by linarith) (ne_of_gt hUpos)]
    have h1 : A * Real.log L ≤ A * L ^ (21 / 20 : ℝ) := mul_le_mul_of_nonneg_left h3 hA.le
    have h2 : (0 : ℝ) ≤ L ^ (21 / 20 : ℝ) := Real.rpow_nonneg hLpos.le _
    linarith
  -- the B bound
  have hBbound : B ≤ (C₄ + 2 * C₅ + 1) * (A + 4) ^ 4 * L ^ (21 / 5 : ℝ) := by
    rw [hBdef, v7chiB]
    have hNU1 : (1 : ℝ) ≤ (N : ℝ) * v7chiU u T := by nlinarith [hN1, hU3]
    have hpow1 : Real.log ((N : ℝ) * v7chiU u T) ^ 4 ≤ ((A + 4) * L ^ (21 / 20 : ℝ)) ^ 4 :=
      pow_le_pow_left₀ (Real.log_nonneg hNU1) hlogNU 4
    have heq1 : ((A + 4) * L ^ (21 / 20 : ℝ)) ^ 4 = (A + 4) ^ 4 * L ^ (21 / 5 : ℝ) := by
      rw [mul_pow, ← Real.rpow_natCast (L ^ (21 / 20 : ℝ)) 4, ← Real.rpow_mul hLpos.le]
      norm_num
    have hpow2 : (N : ℝ) ^ (1 / (20 * A)) ≤ L ^ (1 / 20 : ℝ) := by
      have h := Real.rpow_le_rpow (Nat.cast_nonneg N) hNL (by positivity : (0 : ℝ) ≤ 1 / (20 * A))
      rw [← Real.rpow_mul hLpos.le] at h
      rwa [show A * (1 / (20 * A)) = 1 / 20 by field_simp] at h
    have hpow3 : Real.log ((N : ℝ) + 2) ^ 2 ≤ (A + 4) ^ 4 * L ^ (21 / 5 : ℝ) := by
      have hN2le : (N : ℝ) + 2 ≤ 2 * L ^ A := by linarith only [h7, hNL]
      have hlogN2 : Real.log ((N : ℝ) + 2) ≤ (A + 1) * Real.log L := by
        calc Real.log ((N : ℝ) + 2) ≤ Real.log (2 * L ^ A) :=
              Real.log_le_log (by positivity) hN2le
          _ = Real.log 2 + A * Real.log L := by
              rw [Real.log_mul (by norm_num) (by positivity), Real.log_rpow hLpos A]
          _ ≤ Real.log L + A * Real.log L := by linarith only [h4]
          _ = (A + 1) * Real.log L := by ring
      have hsq : Real.log ((N : ℝ) + 2) ^ 2 ≤ ((A + 1) * Real.log L) ^ 2 :=
        pow_le_pow_left₀ (Real.log_nonneg (by linarith : (1 : ℝ) ≤ (N : ℝ) + 2)) hlogN2 2
      rw [show ((A + 1) * Real.log L) ^ 2 = (A + 1) ^ 2 * (Real.log L) ^ 2 by ring] at hsq
      exact le_trans hsq h9
    have hlogNU4 : Real.log ((N : ℝ) * v7chiU u T) ^ 4 ≤ (A + 4) ^ 4 * L ^ (21 / 5 : ℝ) := by
      rw [← heq1]; exact hpow1
    have hL20 : L ^ (1 / 20 : ℝ) ≤ L ^ (21 / 5 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hL2 (by norm_num)
    have h21 : L ^ (21 / 5 : ℝ) ≤ (A + 4) ^ 4 * L ^ (21 / 5 : ℝ) := by
      have h1 : (1 : ℝ) ≤ (A + 4) ^ 4 := one_le_pow₀ (by linarith : (1 : ℝ) ≤ A + 4)
      nlinarith only [h1, Real.rpow_nonneg hLpos.le (21 / 5 : ℝ)]
    have hNsig : (N : ℝ) ^ (1 / (20 * A)) ≤ (A + 4) ^ 4 * L ^ (21 / 5 : ℝ) :=
      le_trans hpow2 (le_trans hL20 h21)
    have hK : (0 : ℝ) ≤ (A + 4) ^ 4 * L ^ (21 / 5 : ℝ) := by positivity
    nlinarith only [hlogNU4, hNsig, hpow3, hK, hC₄, hC₅]
  -- the D bound
  have hD : v7chiD N u T ≤ 4 * (A + 1) * (L ^ (9 / 10 : ℝ) * Real.log L) := by
    rw [v7chiD]
    have hlogU0 : 0 ≤ Real.log (v7chiU u T) := Real.log_nonneg (by linarith)
    have hpow : Real.log (v7chiU u T) ^ (6 / 7 : ℝ) ≤
        (21 / 20 : ℝ) ^ (6 / 7 : ℝ) * L ^ (9 / 10 : ℝ) := by
      calc Real.log (v7chiU u T) ^ (6 / 7 : ℝ) ≤ ((21 / 20) * L ^ (21 / 20 : ℝ)) ^ (6 / 7 : ℝ) :=
            Real.rpow_le_rpow hlogU0 hlogU (by norm_num)
        _ = (21 / 20 : ℝ) ^ (6 / 7 : ℝ) * (L ^ (21 / 20 : ℝ)) ^ (6 / 7 : ℝ) :=
            Real.mul_rpow (by norm_num) (Real.rpow_nonneg hLpos.le _)
        _ = (21 / 20 : ℝ) ^ (6 / 7 : ℝ) * L ^ (9 / 10 : ℝ) := by
            rw [← Real.rpow_mul hLpos.le]
            norm_num
    have hC : (21 / 20 : ℝ) ^ (6 / 7 : ℝ) ≤ 3 / 2 := by
      calc (21 / 20 : ℝ) ^ (6 / 7 : ℝ) ≤ (21 / 20 : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
        _ = 21 / 20 := Real.rpow_one _
        _ ≤ 3 / 2 := by norm_num
    have hstep1 : Real.log (v7chiU u T) ^ (6 / 7 : ℝ) ≤ (3 / 2) * L ^ (9 / 10 : ℝ) := by
      calc Real.log (v7chiU u T) ^ (6 / 7 : ℝ)
          ≤ (21 / 20 : ℝ) ^ (6 / 7 : ℝ) * L ^ (9 / 10 : ℝ) := hpow
        _ ≤ (3 / 2) * L ^ (9 / 10 : ℝ) :=
            mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg hLpos.le _)
    have hsum : Real.log ((N : ℝ) + 2) + Real.log (Real.log (v7chiU u T)) ≤
        (A + 21 / 10) * Real.log L := by
      have hN2le : (N : ℝ) + 2 ≤ 2 * L ^ A := by linarith only [h7, hNL]
      have hlogN2 : Real.log ((N : ℝ) + 2) ≤ (A + 1) * Real.log L := by
        calc Real.log ((N : ℝ) + 2) ≤ Real.log (2 * L ^ A) :=
              Real.log_le_log (by positivity) hN2le
          _ = Real.log 2 + A * Real.log L := by
              rw [Real.log_mul (by norm_num) (by positivity), Real.log_rpow hLpos A]
          _ ≤ Real.log L + A * Real.log L := by linarith only [h4]
          _ = (A + 1) * Real.log L := by ring
      have hll : Real.log (Real.log (v7chiU u T)) ≤ (11 / 10) * Real.log L := by
        have hpos : 0 < Real.log (v7chiU u T) := Real.log_pos (by linarith)
        have hmono : Real.log (Real.log (v7chiU u T))
            ≤ Real.log ((21 / 20) * L ^ (21 / 20 : ℝ)) := by
          apply Real.log_le_log hpos
          nlinarith only [hlogU, Real.rpow_pos_of_pos hLpos (21 / 20 : ℝ)]
        calc Real.log (Real.log (v7chiU u T)) ≤ Real.log ((21 / 20) * L ^ (21 / 20 : ℝ)) := hmono
          _ = Real.log (21 / 20) + (21 / 20) * Real.log L := by
              rw [Real.log_mul (by norm_num) (by positivity), Real.log_rpow hLpos]
          _ ≤ (1 / 20) * Real.log L + (21 / 20) * Real.log L := by linarith only [h8]
          _ = (11 / 10) * Real.log L := by ring
      calc Real.log ((N : ℝ) + 2) + Real.log (Real.log (v7chiU u T))
          ≤ (A + 1) * Real.log L + (11 / 10) * Real.log L := add_le_add hlogN2 hll
        _ = (A + 21 / 10) * Real.log L := by ring
    have hnon : 0 ≤ L ^ (9 / 10 : ℝ) * Real.log L :=
      mul_nonneg (Real.rpow_nonneg hLpos.le _) hlogL.le
    calc Real.log (v7chiU u T) ^ (6 / 7 : ℝ) *
            (Real.log ((N : ℝ) + 2) + Real.log (Real.log (v7chiU u T)))
        ≤ ((3 / 2) * L ^ (9 / 10 : ℝ)) * ((A + 21 / 10) * Real.log L) := by
          refine mul_le_mul hstep1 hsum ?_ ?_
          · have h1 : 0 ≤ Real.log ((N : ℝ) + 2) := Real.log_nonneg (by linarith)
            have h2 : 0 ≤ Real.log (Real.log (v7chiU u T)) :=
              Real.log_nonneg (by
                rw [Real.le_log_iff_exp_le hUpos]
                linarith [Real.exp_one_lt_three])
            linarith only [h1, h2]
          · positivity
      _ = ((3 / 2) * (A + 21 / 10)) * (L ^ (9 / 10 : ℝ) * Real.log L) := by ring
      _ ≤ (4 * (A + 1)) * (L ^ (9 / 10 : ℝ) * Real.log L) := by
          apply mul_le_mul_of_nonneg_right _ hnon
          nlinarith only [hA]
      _ = 4 * (A + 1) * (L ^ (9 / 10 : ℝ) * Real.log L) := by ring
  -- the δ bound
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hNinv : L ^ (-(1 / 20) : ℝ) ≤ (N : ℝ) ^ (-(1 / (20 * A))) := by
    have h : (N : ℝ) ^ (1 / (20 * A)) ≤ L ^ (1 / 20 : ℝ) := by
      calc (N : ℝ) ^ (1 / (20 * A)) ≤ (L ^ A) ^ (1 / (20 * A)) :=
            Real.rpow_le_rpow (Nat.cast_nonneg N) hNL (by positivity)
        _ = L ^ (1 / 20 : ℝ) := by
            rw [← Real.rpow_mul hLpos.le,
              show A * (1 / (20 * A)) = 1 / 20 by field_simp]
    have h2 : (L ^ (1 / 20 : ℝ))⁻¹ ≤ ((N : ℝ) ^ (1 / (20 * A)))⁻¹ := by
      have h3 : (1 : ℝ) / L ^ (1 / 20 : ℝ) ≤ 1 / (N : ℝ) ^ (1 / (20 * A)) :=
        one_div_le_one_div_of_le (Real.rpow_pos_of_pos hNpos _) h
      simpa only [one_div] using h3
    rwa [← Real.rpow_neg hLpos.le, ← Real.rpow_neg (Nat.cast_nonneg N)] at h2
  have hR2 : c * L ^ (1 / 12 : ℝ) + 20 * Real.log (L + 2) ≤ c₅ * L ^ (19 / 20 : ℝ) / 2 := h20
  have hR3 : c * L ^ (1 / 12 : ℝ) + 20 * Real.log (L + 2) ≤ L / 4 := h21
  have hδL : c * L ^ (1 / 12 : ℝ) + 20 * Real.log (L + 2) ≤ δ * L := by
    have hDpos : 0 < 2 * v7chiD N u T := by
      have h := v7chiD_pos N u T hTpos.le (by omega : 1 ≤ N)
      linarith only [h]
    have hBpos : 0 < 8 * (A + 1) * Real.log L := by positivity
    have hL10 : L ^ (9 / 10 : ℝ) * L ^ (1 / 10 : ℝ) = L := by
      rw [← Real.rpow_add hLpos]; norm_num
    have hR1 : c * L ^ (1 / 12 : ℝ) + 20 * Real.log (L + 2) ≤
        c₄ * L ^ (1 / 10 : ℝ) / (8 * (A + 1) * Real.log L) := by
      have hcomb : c₄ * L ^ (1 / 60 : ℝ) * L ^ (1 / 12 : ℝ) = c₄ * L ^ (1 / 10 : ℝ) := by
        rw [mul_assoc, ← Real.rpow_add hLpos,
          show (1 : ℝ) / 60 + 1 / 12 = 1 / 10 by norm_num]
      have hm := mul_le_mul_of_nonneg_right h18 (Real.rpow_nonneg hLpos.le (1 / 12 : ℝ))
      have hm2 : 16 * c * (A + 4) * Real.log L * L ^ (1 / 12 : ℝ) ≤ c₄ * L ^ (1 / 10 : ℝ) := by
        rw [hcomb] at hm; exact hm
      have hm1 : c * L ^ (1 / 12 : ℝ) ≤
          (c₄ * L ^ (1 / 10 : ℝ) / (8 * (A + 1) * Real.log L)) / 2 := by
        rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2), le_div_iff₀ hBpos]
        have hc16 : 16 * c * (A + 1) * Real.log L ≤ 16 * c * (A + 4) * Real.log L := by
          nlinarith only [hc, hlogL, hA]
        have h16 := mul_le_mul_of_nonneg_right hc16 (Real.rpow_nonneg hLpos.le (1 / 12 : ℝ))
        nlinarith only [h16, hm2]
      have hm3 : 20 * Real.log (L + 2) ≤
          (c₄ * L ^ (1 / 10 : ℝ) / (8 * (A + 1) * Real.log L)) / 2 := by
        rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2), le_div_iff₀ hBpos]
        have hlogLp : 0 ≤ Real.log (L + 2) := Real.log_nonneg (by linarith)
        have h320' : 320 * (A + 1) * Real.log (L + 2) * Real.log L
            ≤ 320 * (A + 4) * Real.log (L + 2) * Real.log L := by
          nlinarith only [hA, hlogL, hlogLp]
        nlinarith only [h19, h320', Real.rpow_nonneg hLpos.le (1 / 10 : ℝ)]
      linarith only [hm1, hm3]
    have hA1 : c₄ * L ^ (1 / 10 : ℝ) / (8 * (A + 1) * Real.log L) / L ≤
        c₄ / (2 * v7chiD N u T) := by
      rw [div_le_iff₀ hLpos,
        show c₄ / (2 * v7chiD N u T) * L = c₄ * L / (2 * v7chiD N u T) by ring,
        le_div_iff₀ hDpos]
      rw [show c₄ * L ^ (1 / 10 : ℝ) / (8 * (A + 1) * Real.log L) * (2 * v7chiD N u T)
            = c₄ * L ^ (1 / 10 : ℝ) * (2 * v7chiD N u T) / (8 * (A + 1) * Real.log L) by ring]
      rw [div_le_iff₀ hBpos]
      have hD4 : v7chiD N u T ≤ 4 * (A + 1) * (L ^ (9 / 10 : ℝ) * Real.log L) := hD
      have hfin : L ^ (1 / 10 : ℝ) * (2 * v7chiD N u T) ≤ 8 * (A + 1) * (L * Real.log L) := by
        have h1 : (2 : ℝ) * v7chiD N u T
            ≤ 8 * (A + 1) * (L ^ (9 / 10 : ℝ) * Real.log L) := by
          have h0 := mul_le_mul_of_nonneg_left hD4 (by norm_num : (0 : ℝ) ≤ 2)
          have heq : (2 : ℝ) * (4 * (A + 1) * (L ^ (9 / 10 : ℝ) * Real.log L))
              = 8 * (A + 1) * (L ^ (9 / 10 : ℝ) * Real.log L) := by ring
          linarith only [h0, heq.le, heq.ge]
        have h2 := mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg hLpos.le (1 / 10 : ℝ))
        calc L ^ (1 / 10 : ℝ) * (2 * v7chiD N u T)
            ≤ L ^ (1 / 10 : ℝ) * (8 * (A + 1) * (L ^ (9 / 10 : ℝ) * Real.log L)) := h2
          _ = 8 * (A + 1) * (L * Real.log L) := by
              rw [show L ^ (1 / 10 : ℝ) * (8 * (A + 1) * (L ^ (9 / 10 : ℝ) * Real.log L))
                    = 8 * (A + 1) * ((L ^ (1 / 10 : ℝ) * L ^ (9 / 10 : ℝ)) * Real.log L) by ring,
                show L ^ (1 / 10 : ℝ) * L ^ (9 / 10 : ℝ) = L by
                  rw [← Real.rpow_add hLpos]; norm_num]
      nlinarith only [hfin, hc₄]
    have hA2 : c₅ * L ^ (-(1 / 20) : ℝ) / 2 ≤ c₅ * (N : ℝ) ^ (-(1 / (20 * A))) / 2 :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hNinv hc₅.le) (by norm_num)
    have hδge : min (min (c₄ * L ^ (1 / 10 : ℝ) / (8 * (A + 1) * Real.log L) / L)
        (c₅ * L ^ (-(1 / 20) : ℝ) / 2)) (1 / 4) ≤ δ := by
      rw [hδdef, v7chidelta]
      refine le_min (le_min ?_ ?_) (min_le_right _ _)
      · exact (le_trans (le_trans (min_le_left _ _) (min_le_left _ _)) hA1)
      · exact (le_trans (le_trans (min_le_left _ _) (min_le_right _ _)) hA2)
    have hmul := mul_le_mul_of_nonneg_right hδge hLpos.le
    rw [min_mul_of_nonneg _ _ hLpos.le, min_mul_of_nonneg _ _ hLpos.le] at hmul
    have hmm : c * L ^ (1 / 12 : ℝ) + 20 * Real.log (L + 2)
        ≤ min (min (c₄ * L ^ (1 / 10 : ℝ) / (8 * (A + 1) * Real.log L) / L * L)
            (c₅ * L ^ (-(1 / 20) : ℝ) / 2 * L)) (1 / 4 * L) := by
      refine le_min (le_min ?_ ?_) ?_
      · rwa [div_mul_cancel₀ _ (ne_of_gt hLpos)]
      · have h : c₅ * L ^ (-(1 / 20) : ℝ) / 2 * L
            = c₅ * (L ^ (-(1 / 20) : ℝ) * L ^ (1 : ℝ)) / 2 := by
          rw [Real.rpow_one]; ring
        rw [h, ← Real.rpow_add hLpos, show -(1 / 20 : ℝ) + 1 = 19 / 20 by norm_num]
        exact hR2
      · linarith only [hR3]
    linarith only [hmm, hmul]
  -- (A) the second conjunct: exponential saving
  have hconj5 : Real.exp (-(δ * L)) ≤ Real.exp (-(c * L ^ (1 / 12 : ℝ))) / (L + 2) ^ 20 := by
    have h1 : Real.exp (-(δ * L)) ≤ Real.exp (-(c * L ^ (1 / 12 : ℝ) + 20 * Real.log (L + 2))) :=
      Real.exp_le_exp.mpr (by linarith only [hδL])
    have h2 : Real.exp (-(c * L ^ (1 / 12 : ℝ) + 20 * Real.log (L + 2)))
        = Real.exp (-(c * L ^ (1 / 12 : ℝ))) / (L + 2) ^ 20 := by
      rw [show -(c * L ^ (1 / 12 : ℝ) + 20 * Real.log (L + 2))
            = -(c * L ^ (1 / 12 : ℝ)) + -(20 * Real.log (L + 2)) by ring, Real.exp_add]
      congr 1
      have h4 : Real.exp (20 * Real.log (L + 2)) = (L + 2) ^ 20 := by
        rw [show (20 : ℝ) * Real.log (L + 2) = ((20 : ℕ) : ℝ) * Real.log (L + 2) by norm_num,
          Real.exp_nat_mul, Real.exp_log hLp2]
      rw [Real.exp_neg, h4]
    rw [h2] at h1; exact h1
  -- (B) the log-height bound
  have hσpos : 0 < 1 - δ := by linarith only [hδ4]
  have hlogT : 3 + 3 * Real.log (2 + T / (1 - δ)) ≤ 9 * L ^ (1 / 2 : ℝ) := by
    have h1 : 2 + T / (1 - δ) ≤ 3 * T := by
      have hmul : T / (1 - δ) ≤ T * (4 / 3) := by
        rw [div_le_iff₀ hσpos]; nlinarith only [hδ4, hTpos]
      linarith only [hmul, hT2]
    have h2 : Real.log (2 + T / (1 - δ)) ≤ 2 * L ^ (1 / 2 : ℝ) := by
      have hdiv : 0 < T / (1 - δ) := div_pos hTpos hσpos
      have hpos : 0 < 2 + T / (1 - δ) := by linarith only [hdiv]
      calc Real.log (2 + T / (1 - δ)) ≤ Real.log (3 * T) := Real.log_le_log hpos h1
        _ = Real.log 3 + L ^ (1 / 2 : ℝ) := by
            rw [Real.log_mul (by norm_num) (ne_of_gt hTpos)]
            congr 1
            rw [hTdef, v7chiT, Real.log_exp]
        _ ≤ 2 * L ^ (1 / 2 : ℝ) := by linarith only [h22]
    have h3 : (1 : ℝ) ≤ L ^ (1 / 2 : ℝ) := Real.one_le_rpow hL2 (by norm_num)
    linarith only [h2, h3]
  -- (C) the remaining conjuncts
  have hconj6 : B * (3 + 3 * Real.log (2 + T / (1 - δ))) ≤ (1 / 16) * (L + 2) ^ 20 := by
    have hpos3 : 0 ≤ 3 + 3 * Real.log (2 + T / (1 - δ)) := by
      have hdiv : 0 < T / (1 - δ) := div_pos hTpos hσpos
      have h0 : 0 ≤ Real.log (2 + T / (1 - δ)) := Real.log_nonneg (by linarith only [hdiv])
      linarith only [h0]
    have h1 : B * (3 + 3 * Real.log (2 + T / (1 - δ)))
        ≤ ((C₄ + 2 * C₅ + 1) * (A + 4) ^ 4 * L ^ (21 / 5 : ℝ)) * (9 * L ^ (1 / 2 : ℝ)) :=
      mul_le_mul hBbound hlogT hpos3 (by positivity)
    have h2 : ((C₄ + 2 * C₅ + 1) * (A + 4) ^ 4 * L ^ (21 / 5 : ℝ)) * (9 * L ^ (1 / 2 : ℝ))
        = 9 * (((C₄ + 2 * C₅ + 1) * (A + 4) ^ 4) * L ^ (21 / 5 : ℝ) * L ^ (1 / 2 : ℝ)) := by
      ring
    rw [h2] at h1
    have h3 : 9 * (((C₄ + 2 * C₅ + 1) * (A + 4) ^ 4) * L ^ (21 / 5 : ℝ) * L ^ (1 / 2 : ℝ))
        ≤ 9 * ((1 / 144) * (L + 2) ^ 20) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      linarith only [h10]
    have h4 : 9 * ((1 / 144) * (L + 2) ^ 20) = (1 / 16) * (L + 2) ^ 20 := by ring
    linarith only [h1, h3, h4.le, h4.ge]
  have hconj7 : 16 * B * Real.exp 1 ≤ Real.exp (L ^ (1 / 2 : ℝ) - c * L ^ (1 / 12 : ℝ)) := by
    have h1 : 16 * B * Real.exp 1
        ≤ 16 * ((C₄ + 2 * C₅ + 1) * (A + 4) ^ 4) * Real.exp 1 * L ^ (21 / 5 : ℝ) := by
      nlinarith only [hBbound, hC₄, hC₅, Real.exp_pos 1,
        Real.rpow_nonneg hLpos.le (21 / 5 : ℝ)]
    have h2 : 16 * ((C₄ + 2 * C₅ + 1) * (A + 4) ^ 4) * Real.exp 1 * L ^ (21 / 5 : ℝ)
        ≤ 16 * ((C₄ + 2 * C₅ + 1) * (A + 4) ^ 4) * Real.exp 1 * (L + 2) ^ 5 :=
      mul_le_mul_of_nonneg_left h11 (by positivity)
    linarith only [h1, h2, h12, h13]
  have hconj8 : 16 * C_p * (L + 1) ^ 2 ≤ Real.exp (L ^ (1 / 2 : ℝ) - c * L ^ (1 / 12 : ℝ)) := by
    have h1 : 16 * C_p * (L + 1) ^ 2 ≤ 16 * C_p * (L + 2) ^ 2 := by
      nlinarith only [hC_p, hLpos]
    linarith only [h1, h14, h13]
  have hconj9 : 8 * C_p * (L + 1) ≤ Real.exp (L - c * L ^ (1 / 12 : ℝ)) := by
    have h1 : 8 * C_p * (L + 1) ≤ 8 * C_p * (L + 2) := by
      nlinarith only [hC_p]
    linarith only [h1, h15, h16]
  have hconj10 : 4 * C_red * (A * Real.log (L + 2) + Real.log 2) * (L + 2) ≤
      Real.exp (L - c * L ^ (1 / 12 : ℝ)) := by
    have h1 : A * Real.log (L + 2) + Real.log 2 ≤ (A + 1) * (L + 2) := by
      have h2 : Real.log (L + 2) ≤ L + 2 := by
        have := Real.log_le_sub_one_of_pos hLp2
        linarith only [this]
      have h3 : Real.log 2 ≤ L + 2 := by
        have h4 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
        linarith only [h4, hLpos]
      nlinarith only [h2, h3, hA]
    have h4 : 4 * C_red * (A * Real.log (L + 2) + Real.log 2) * (L + 2)
        ≤ 4 * C_red * (A + 1) * (L + 2) ^ 3 := by
      have hmul := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 4 * C_red)
      have h5 := mul_le_mul_of_nonneg_right hmul hLp2.le
      calc 4 * C_red * (A * Real.log (L + 2) + Real.log 2) * (L + 2)
          = (4 * C_red * (A * Real.log (L + 2) + Real.log 2)) * (L + 2) := by ring
        _ ≤ (4 * C_red * ((A + 1) * (L + 2))) * (L + 2) := h5
        _ ≤ 4 * C_red * (A + 1) * (L + 2) ^ 3 := by
            have h6 : (4 * C_red * ((A + 1) * (L + 2))) * (L + 2)
                = 4 * C_red * (A + 1) * (L + 2) ^ 2 := by ring
            rw [h6]
            have h7 : (1 : ℝ) ≤ L + 2 := by linarith only [hLpos]
            have h8 : (L + 2) ^ 2 ≤ (L + 2) ^ 3 := by nlinarith only [h7]
            have h9 : (0 : ℝ) ≤ 4 * C_red * (A + 1) := by positivity
            exact mul_le_mul_of_nonneg_left h8 h9
    exact le_trans h4 (le_trans h17 h16)
  have hx2 : (2 : ℝ) ≤ x := hx2'
  have hx1 : (1 : ℝ) ≤ x := by linarith only [hx2]
  have hconj11 : (⌊x⌋₊ : ℝ) + 1 / 2 ≤ 2 * x := v7chiX_le_two_mul hx1
  have hconj12 : Real.log ((⌊x⌋₊ : ℝ) + 1 / 2) ≤ L + 1 := v7chiX_log_le hx2
  exact ⟨hT2, hδpos, hδ4, hx2, h1000, hconj5, hconj6, hconj7, hconj8, hconj9, hconj10, hconj11,
    hconj12⟩

end

end Work.BMF
