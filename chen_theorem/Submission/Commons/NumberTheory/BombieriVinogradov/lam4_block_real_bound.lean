import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.Algebra.EuclideanDomain.Field
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace Commons.NumberTheory.BombieriVinogradov

open scoped BigOperators

/-- `√(a+b) ≤ √a + √b` for `a,b ≥ 0`. -/
private lemma sqrt_add_le' {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a + b) ≤ Real.sqrt a + Real.sqrt b := by
  rw [Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  have h2 : (Real.sqrt a + Real.sqrt b)^2 = a + b + 2*(Real.sqrt a * Real.sqrt b) := by
    rw [add_sq, Real.sq_sqrt ha, Real.sq_sqrt hb]; ring
  rw [h2]
  have : 0 ≤ 2*(Real.sqrt a * Real.sqrt b) := by positivity
  linarith

/-- `√2 · √2 = 2`. -/
private lemma sqrt2_mul_sqrt2 : Real.sqrt 2 * Real.sqrt 2 = (2:ℝ) := by
  nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)]

/-- `√4 = 2`. -/
private lemma sqrt4 : Real.sqrt (4:ℝ) = 2 := by
  rw [show (4:ℝ) = 2^2 by norm_num, Real.sqrt_sq (show (0:ℝ) ≤ 2 by norm_num)]

/-- `2·√2·(√2·x) = 4x`. -/
private lemma two_sqrt2_sqrt2 (x : ℝ) : 2 * Real.sqrt 2 * (Real.sqrt 2 * x) = 4 * x := by
  have h : 2 * Real.sqrt 2 * (Real.sqrt 2 * x)
      = 2 * ((Real.sqrt 2 * Real.sqrt 2) * x) := by ring
  rw [h, sqrt2_mul_sqrt2]; ring

/-- `2·√2·(√2·Q·y) = 4Qy`. -/
private lemma two_sqrt2_sqrt2' (Q y : ℝ) :
    2 * Real.sqrt 2 * (Real.sqrt 2 * Q * y) = 4 * Q * y := by
  have h : 2 * Real.sqrt 2 * (Real.sqrt 2 * Q * y)
      = 2 * ((Real.sqrt 2 * Real.sqrt 2) * (Q * y)) := by ring
  rw [h, sqrt2_mul_sqrt2]; ring

/-- The key pair-product bound used in the `λ₄` dyadic-block estimate. -/
private lemma sqrt_pair_product_le (M N x Q : ℝ) (hM1 : 1 ≤ M) (hx1 : 1 ≤ x) (hMx : M ≤ x)
    (hN : N ≤ 2 * (x / M)) (hN1 : 1 ≤ N) (hQ1 : 1 ≤ Q) :
    (2 * M + Q * Real.sqrt (2 * M)) * (N + Q * Real.sqrt N)
      ≤ 2 * Real.sqrt 2 * (Real.sqrt 2 * x + Real.sqrt 2 * Q * Real.sqrt (x * M)
          + Q * x / Real.sqrt M + Q ^ 2 * Real.sqrt x) := by
  have hM0 : (0:ℝ) < M := by linarith
  have hMnn : (0:ℝ) ≤ M := le_of_lt hM0
  have hxnn : (0:ℝ) ≤ x := by linarith
  have hQ0 : (0:ℝ) < Q := by linarith
  have hQnn : (0:ℝ) ≤ Q := le_of_lt hQ0
  have hspos : 0 < Real.sqrt M := Real.sqrt_pos.mpr hM0
  have h1sqrt2 : (1:ℝ) ≤ Real.sqrt 2 := Real.one_le_sqrt.mpr (by norm_num)
  have hMN : M * N ≤ 2 * x := by
    have h1 : M * N ≤ M * (2 * (x / M)) := mul_le_mul_of_nonneg_left hN hMnn
    have hxM : M * (x / M) = x := by
      rw [← mul_div_assoc]
      exact mul_div_cancel_left₀ x (ne_of_gt hM0)
    have h2 : M * (2 * (x / M)) = 2 * x := by
      calc M * (2 * (x / M)) = 2 * (M * (x / M)) := by ring
        _ = 2 * x := by rw [hxM]
    linarith [h1, h2.le, h2.ge]
  have hexp : (2 * M + Q * Real.sqrt (2 * M)) * (N + Q * Real.sqrt N)
      = 2 * M * N + 2 * M * Q * Real.sqrt N + N * Q * Real.sqrt (2 * M)
        + Q ^ 2 * (Real.sqrt (2 * M) * Real.sqrt N) := by ring
  rw [hexp]
  have t1 : 2 * M * N ≤ 2 * Real.sqrt 2 * (Real.sqrt 2 * x) := by
    rw [two_sqrt2_sqrt2 x]; nlinarith [hMN]
  have t2 : 2 * M * Q * Real.sqrt N ≤ 2 * Real.sqrt 2 * (Real.sqrt 2 * Q * Real.sqrt (x * M)) := by
    have hcore : M * Real.sqrt N ≤ 2 * Real.sqrt (x * M) := by
      have h1 : M * Real.sqrt N = Real.sqrt (M ^ 2 * N) := by
        rw [Real.sqrt_mul (by positivity : (0:ℝ) ≤ M ^ 2) N, Real.sqrt_sq hMnn]
      rw [h1]
      have hle : M ^ 2 * N ≤ 4 * (x * M) := by nlinarith [hMN, hMnn, hxnn]
      calc Real.sqrt (M ^ 2 * N) ≤ Real.sqrt (4 * (x * M)) := Real.sqrt_le_sqrt hle
        _ = 2 * Real.sqrt (x * M) := by
            rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 4) (x * M), sqrt4]
    rw [two_sqrt2_sqrt2' Q (Real.sqrt (x * M))]
    have hmul : 2 * Q * (M * Real.sqrt N) ≤ 2 * Q * (2 * Real.sqrt (x * M)) :=
      mul_le_mul_of_nonneg_left hcore (by positivity : (0:ℝ) ≤ 2 * Q)
    nlinarith [hmul]
  have t3 : N * Q * Real.sqrt (2 * M) ≤ 2 * Real.sqrt 2 * (Q * x / Real.sqrt M) := by
    have hcore : N * Real.sqrt (2 * M) ≤ 2 * Real.sqrt 2 * x / Real.sqrt M := by
      rw [le_div_iff₀ hspos]
      have h1 : Real.sqrt (2 * M) * Real.sqrt M = Real.sqrt (2 * M * M) :=
        (Real.sqrt_mul (by linarith : (0:ℝ) ≤ 2 * M) M).symm
      have h2 : Real.sqrt (2 * M * M) = Real.sqrt 2 * M := by
        rw [show 2 * M * M = 2 * M ^ 2 by ring,
            Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2) (M ^ 2), Real.sqrt_sq hMnn]
      have he2 : N * Real.sqrt (2 * M) * Real.sqrt M = Real.sqrt 2 * (N * M) := by
        rw [mul_assoc, h1, h2]; ring
      rw [he2]
      nlinarith [hMN, Real.sqrt_nonneg 2]
    have heR : Q * (2 * Real.sqrt 2 * x / Real.sqrt M) = 2 * Real.sqrt 2 * (Q * x / Real.sqrt M) := by
      rw [← mul_div_assoc, ← mul_div_assoc]; ring
    have hmul : Q * (N * Real.sqrt (2 * M)) ≤ Q * (2 * Real.sqrt 2 * x / Real.sqrt M) :=
      mul_le_mul_of_nonneg_left hcore hQnn
    rw [heR] at hmul
    have : N * Q * Real.sqrt (2 * M) = Q * (N * Real.sqrt (2 * M)) := by ring
    rw [this]; exact hmul
  have t4 : Q ^ 2 * (Real.sqrt (2 * M) * Real.sqrt N)
      ≤ 2 * Real.sqrt 2 * (Q ^ 2 * Real.sqrt x) := by
    have hst : Real.sqrt (2 * M) * Real.sqrt N = Real.sqrt (2 * M * N) :=
      (Real.sqrt_mul (by linarith : (0:ℝ) ≤ 2 * M) N).symm
    rw [hst]
    have hcore : Real.sqrt (2 * M * N) ≤ 2 * Real.sqrt x := by
      have hle : 2 * M * N ≤ 4 * x := by nlinarith [hMN]
      calc Real.sqrt (2 * M * N) ≤ Real.sqrt (4 * x) := Real.sqrt_le_sqrt hle
        _ = 2 * Real.sqrt x := by
            rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 4) x, sqrt4]
    have step1 : Q ^ 2 * Real.sqrt (2 * M * N) ≤ Q ^ 2 * (2 * Real.sqrt x) :=
      mul_le_mul_of_nonneg_left hcore (sq_nonneg Q)
    have step2 : Q ^ 2 * (2 * Real.sqrt x) ≤ 2 * Real.sqrt 2 * (Q ^ 2 * Real.sqrt x) := by
      have h := mul_nonneg (mul_nonneg (sq_nonneg Q) (Real.sqrt_nonneg x))
        (by linarith [h1sqrt2] : (0:ℝ) ≤ Real.sqrt 2 - 1)
      nlinarith [h]
    linarith [step1, step2]
  calc 2 * M * N + 2 * M * Q * Real.sqrt N + N * Q * Real.sqrt (2 * M)
          + Q ^ 2 * (Real.sqrt (2 * M) * Real.sqrt N)
      ≤ 2 * Real.sqrt 2 * (Real.sqrt 2 * x) + 2 * Real.sqrt 2 * (Real.sqrt 2 * Q * Real.sqrt (x * M))
          + 2 * Real.sqrt 2 * (Q * x / Real.sqrt M) + 2 * Real.sqrt 2 * (Q ^ 2 * Real.sqrt x) := by
        linarith [t1, t2, t3, t4]
    _ = 2 * Real.sqrt 2 * (Real.sqrt 2 * x + Real.sqrt 2 * Q * Real.sqrt (x * M)
          + Q * x / Real.sqrt M + Q ^ 2 * Real.sqrt x) := by ring

lemma lam4_block_real_bound (c M N x Q T L : ℝ) (hc : 0 ≤ c)
    (hM1 : 1 ≤ M) (hx1 : 1 ≤ x) (hMx : M ≤ x) (hN : N ≤ 2 * (x / M)) (hN1 : 1 ≤ N)
    (hQ1 : 1 ≤ Q) (hT1 : 1 ≤ T) (hL1 : 1 ≤ L)
    (hlogM : Real.log (4 * M + 2) ≤ 2 * L) (hlogT : Real.log (Real.exp 3 * T) ≤ 4 * L)
    (hlogN : Real.log (2 * (2 * M) * N + 2) ≤ 2 * L) :
    c * Real.sqrt ((2 * M + Q ^ 2) * (2 * M * Real.log (4 * M + 2)))
        * Real.sqrt ((N + Q ^ 2) * (N * (Real.log (Real.exp 3 * T)) ^ 2))
        * Real.log (2 * (2 * M) * N + 2)
      ≤ 128 * c * L ^ 4 * (Real.sqrt 2 * x + Real.sqrt 2 * Q * Real.sqrt (x * M)
          + Q * x / Real.sqrt M + Q ^ 2 * Real.sqrt x) := by
  have hM0 : (0:ℝ) < M := by linarith
  have hx0 : (0:ℝ) < x := by linarith
  have hQ0 : (0:ℝ) < Q := by linarith
  have hN0 : (0:ℝ) < N := by linarith
  have hT0 : (0:ℝ) < T := by linarith
  have hL0 : (0:ℝ) < L := by linarith
  have hMnn : (0:ℝ) ≤ M := le_of_lt hM0
  have hxnn : (0:ℝ) ≤ x := le_of_lt hx0
  have hQnn : (0:ℝ) ≤ Q := le_of_lt hQ0
  have hNnn : (0:ℝ) ≤ N := le_of_lt hN0
  have hLnn : (0:ℝ) ≤ L := le_of_lt hL0
  have hlogM_nn : 0 ≤ Real.log (4 * M + 2) := Real.log_nonneg (by linarith)
  have hlogT_eq : Real.log (Real.exp 3 * T) = 3 + Real.log T := by
    rw [Real.log_mul (ne_of_gt (Real.exp_pos 3)) (ne_of_gt hT0), Real.log_exp]
  have hlogT_nn : 0 ≤ Real.log (Real.exp 3 * T) := by
    rw [hlogT_eq]; have := Real.log_nonneg hT1; linarith
  have hlogN_nn : 0 ≤ Real.log (2 * (2 * M) * N + 2) :=
    Real.log_nonneg (by nlinarith [hMnn, hNnn])
  have h2MQnn : 0 ≤ 2 * M + Q ^ 2 := by nlinarith [hMnn, sq_nonneg Q]
  have hNQnn : 0 ≤ N + Q ^ 2 := by nlinarith [hNnn, sq_nonneg Q]
  -- the bound for the first `√` factor
  have hS : Real.sqrt ((2 * M + Q ^ 2) * (2 * M * Real.log (4 * M + 2)))
      ≤ Real.sqrt (2 * M + Q ^ 2) * Real.sqrt (2 * M) * (Real.sqrt 2 * Real.sqrt L) := by
    have e1 : Real.sqrt ((2 * M + Q ^ 2) * (2 * M * Real.log (4 * M + 2)))
        = Real.sqrt (2 * M + Q ^ 2) * Real.sqrt (2 * M * Real.log (4 * M + 2)) :=
      Real.sqrt_mul h2MQnn _
    have e2 : Real.sqrt (2 * M * Real.log (4 * M + 2))
        = Real.sqrt (2 * M) * Real.sqrt (Real.log (4 * M + 2)) :=
      Real.sqrt_mul (by linarith : (0:ℝ) ≤ 2 * M) _
    have h3 : Real.sqrt (Real.log (4 * M + 2)) ≤ Real.sqrt 2 * Real.sqrt L := by
      have h := Real.sqrt_le_sqrt hlogM
      rwa [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2) L] at h
    rw [e1, e2, ← mul_assoc]
    exact mul_le_mul_of_nonneg_left h3 (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  -- the bound for the second `√` factor
  have hSp : Real.sqrt ((N + Q ^ 2) * (N * (Real.log (Real.exp 3 * T)) ^ 2))
      ≤ Real.sqrt (N + Q ^ 2) * Real.sqrt N * (4 * L) := by
    have e3 : Real.sqrt ((N + Q ^ 2) * (N * (Real.log (Real.exp 3 * T)) ^ 2))
        = Real.sqrt (N + Q ^ 2) * Real.sqrt (N * (Real.log (Real.exp 3 * T)) ^ 2) :=
      Real.sqrt_mul hNQnn _
    have e4 : Real.sqrt (N * (Real.log (Real.exp 3 * T)) ^ 2)
        = Real.sqrt N * Real.sqrt ((Real.log (Real.exp 3 * T)) ^ 2) :=
      Real.sqrt_mul (by linarith : (0:ℝ) ≤ N) _
    have e5 : Real.sqrt ((Real.log (Real.exp 3 * T)) ^ 2) = Real.log (Real.exp 3 * T) := by
      rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hlogT_nn]
    rw [e3, e4, e5]
    have : Real.sqrt N * Real.log (Real.exp 3 * T) ≤ Real.sqrt N * (4 * L) :=
      mul_le_mul_of_nonneg_left hlogT (Real.sqrt_nonneg N)
    calc Real.sqrt (N + Q ^ 2) * (Real.sqrt N * Real.log (Real.exp 3 * T))
        ≤ Real.sqrt (N + Q ^ 2) * (Real.sqrt N * (4 * L)) :=
          mul_le_mul_of_nonneg_left this (Real.sqrt_nonneg _)
      _ = Real.sqrt (N + Q ^ 2) * Real.sqrt N * (4 * L) := by ring
  have hD : Real.log (2 * (2 * M) * N + 2) ≤ 2 * L := hlogN
  have hS1nn : 0 ≤ Real.sqrt (2 * M + Q ^ 2) * Real.sqrt (2 * M) * (Real.sqrt 2 * Real.sqrt L) :=
    mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
      (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  have hS2nn : 0 ≤ Real.sqrt (N + Q ^ 2) * Real.sqrt N * (4 * L) :=
    mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) (by linarith)
  have hstep4 : c * Real.sqrt ((2 * M + Q ^ 2) * (2 * M * Real.log (4 * M + 2)))
        * Real.sqrt ((N + Q ^ 2) * (N * (Real.log (Real.exp 3 * T)) ^ 2))
        * Real.log (2 * (2 * M) * N + 2)
      ≤ c * (Real.sqrt (2 * M + Q ^ 2) * Real.sqrt (2 * M) * (Real.sqrt 2 * Real.sqrt L))
        * (Real.sqrt (N + Q ^ 2) * Real.sqrt N * (4 * L)) * (2 * L) := by
    have h1 : c * Real.sqrt ((2 * M + Q ^ 2) * (2 * M * Real.log (4 * M + 2)))
        ≤ c * (Real.sqrt (2 * M + Q ^ 2) * Real.sqrt (2 * M) * (Real.sqrt 2 * Real.sqrt L)) :=
      mul_le_mul_of_nonneg_left hS hc
    have h2 : c * Real.sqrt ((2 * M + Q ^ 2) * (2 * M * Real.log (4 * M + 2)))
          * Real.sqrt ((N + Q ^ 2) * (N * (Real.log (Real.exp 3 * T)) ^ 2))
        ≤ c * (Real.sqrt (2 * M + Q ^ 2) * Real.sqrt (2 * M) * (Real.sqrt 2 * Real.sqrt L))
          * (Real.sqrt (N + Q ^ 2) * Real.sqrt N * (4 * L)) :=
      mul_le_mul h1 hSp (Real.sqrt_nonneg _) (mul_nonneg hc hS1nn)
    exact mul_le_mul h2 hD hlogN_nn (mul_nonneg (mul_nonneg hc hS1nn) hS2nn)
  -- the pair-product bound
  have hP : Real.sqrt (2 * M + Q ^ 2) * Real.sqrt (2 * M) * Real.sqrt (N + Q ^ 2) * Real.sqrt N
      ≤ 2 * Real.sqrt 2 * (Real.sqrt 2 * x + Real.sqrt 2 * Q * Real.sqrt (x * M)
          + Q * x / Real.sqrt M + Q ^ 2 * Real.sqrt x) := by
    have ha : Real.sqrt (2 * M + Q ^ 2) ≤ Real.sqrt (2 * M) + Q := by
      have h := sqrt_add_le' (by linarith : (0:ℝ) ≤ 2 * M) (sq_nonneg Q)
      rwa [Real.sqrt_sq hQnn] at h
    have hb : Real.sqrt (N + Q ^ 2) ≤ Real.sqrt N + Q := by
      have h := sqrt_add_le' (by linarith : (0:ℝ) ≤ N) (sq_nonneg Q)
      rwa [Real.sqrt_sq hQnn] at h
    have h1 : Real.sqrt (2 * M + Q ^ 2) * Real.sqrt (2 * M) ≤ 2 * M + Q * Real.sqrt (2 * M) := by
      have h := mul_le_mul_of_nonneg_right ha (Real.sqrt_nonneg (2 * M))
      nlinarith [h, Real.sq_sqrt (by linarith : (0:ℝ) ≤ 2 * M)]
    have h2 : Real.sqrt (N + Q ^ 2) * Real.sqrt N ≤ N + Q * Real.sqrt N := by
      have h := mul_le_mul_of_nonneg_right hb (Real.sqrt_nonneg N)
      nlinarith [h, Real.sq_sqrt hNnn]
    have hprod : Real.sqrt (2 * M + Q ^ 2) * Real.sqrt (2 * M) * Real.sqrt (N + Q ^ 2) * Real.sqrt N
        ≤ (2 * M + Q * Real.sqrt (2 * M)) * (N + Q * Real.sqrt N) := by
      have h3 : Real.sqrt (2 * M + Q ^ 2) * Real.sqrt (2 * M) * (Real.sqrt (N + Q ^ 2) * Real.sqrt N)
          ≤ (2 * M + Q * Real.sqrt (2 * M)) * (N + Q * Real.sqrt N) :=
        mul_le_mul h1 h2 (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
          (by positivity : (0:ℝ) ≤ 2 * M + Q * Real.sqrt (2 * M))
      calc Real.sqrt (2 * M + Q ^ 2) * Real.sqrt (2 * M) * Real.sqrt (N + Q ^ 2) * Real.sqrt N
          = Real.sqrt (2 * M + Q ^ 2) * Real.sqrt (2 * M) * (Real.sqrt (N + Q ^ 2) * Real.sqrt N) := by ring
        _ ≤ _ := h3
    exact le_trans hprod (sqrt_pair_product_le M N x Q hM1 hx1 hMx hN hN1 hQ1)
  -- rearrangement and coefficient comparison
  have hcancel : c * (Real.sqrt (2 * M + Q ^ 2) * Real.sqrt (2 * M) * (Real.sqrt 2 * Real.sqrt L))
        * (Real.sqrt (N + Q ^ 2) * Real.sqrt N * (4 * L)) * (2 * L)
      = c * (Real.sqrt (2 * M + Q ^ 2) * Real.sqrt (2 * M) * Real.sqrt (N + Q ^ 2) * Real.sqrt N)
        * (8 * Real.sqrt 2 * L ^ 2 * Real.sqrt L) := by ring
  have hRnn : 0 ≤ Real.sqrt 2 * x + Real.sqrt 2 * Q * Real.sqrt (x * M)
      + Q * x / Real.sqrt M + Q ^ 2 * Real.sqrt x := by
    have h1 : 0 ≤ Real.sqrt 2 * x := mul_nonneg (Real.sqrt_nonneg 2) hxnn
    have h2 : 0 ≤ Real.sqrt 2 * Q * Real.sqrt (x * M) :=
      mul_nonneg (mul_nonneg (Real.sqrt_nonneg 2) hQnn) (Real.sqrt_nonneg _)
    have h3 : 0 ≤ Q * x / Real.sqrt M :=
      div_nonneg (mul_nonneg hQnn hxnn) (le_of_lt (Real.sqrt_pos.mpr hM0))
    have h4 : 0 ≤ Q ^ 2 * Real.sqrt x := mul_nonneg (sq_nonneg Q) (Real.sqrt_nonneg _)
    exact add_nonneg (add_nonneg (add_nonneg h1 h2) h3) h4
  have hcoef : 32 * L ^ 2 * Real.sqrt L ≤ 128 * L ^ 4 := by
    have hsL : Real.sqrt L ≤ L := by
      have h : Real.sqrt L ≤ Real.sqrt (L ^ 2) := Real.sqrt_le_sqrt (by nlinarith [hL1])
      rwa [Real.sqrt_sq hLnn] at h
    have h2 : L ^ 2 * Real.sqrt L ≤ L ^ 3 := by
      have h := mul_le_mul_of_nonneg_left hsL (sq_nonneg L)
      calc L ^ 2 * Real.sqrt L ≤ L ^ 2 * L := h
        _ = L ^ 3 := by ring
    have h3 : L ^ 3 ≤ L ^ 4 := pow_le_pow_right₀ hL1 (by norm_num : (3:ℕ) ≤ 4)
    have h34 : L ^ 2 * Real.sqrt L ≤ L ^ 4 := le_trans h2 h3
    calc 32 * L ^ 2 * Real.sqrt L = 32 * (L ^ 2 * Real.sqrt L) := by ring
      _ ≤ 32 * L ^ 4 := by
          exact mul_le_mul_of_nonneg_left h34 (by norm_num)
      _ ≤ 128 * L ^ 4 := by
          have hL4 : 0 ≤ L ^ 4 := by positivity
          linarith
  have hER : c * (Real.sqrt (2 * M + Q ^ 2) * Real.sqrt (2 * M) * Real.sqrt (N + Q ^ 2) * Real.sqrt N)
        * (8 * Real.sqrt 2 * L ^ 2 * Real.sqrt L)
      ≤ 128 * c * L ^ 4 * (Real.sqrt 2 * x + Real.sqrt 2 * Q * Real.sqrt (x * M)
          + Q * x / Real.sqrt M + Q ^ 2 * Real.sqrt x) := by
    have hCnn : 0 ≤ c * (8 * Real.sqrt 2 * L ^ 2 * Real.sqrt L) :=
      mul_nonneg hc (by positivity)
    have h1 : c * (8 * Real.sqrt 2 * L ^ 2 * Real.sqrt L)
          * (Real.sqrt (2 * M + Q ^ 2) * Real.sqrt (2 * M) * Real.sqrt (N + Q ^ 2) * Real.sqrt N)
        ≤ c * (8 * Real.sqrt 2 * L ^ 2 * Real.sqrt L)
          * (2 * Real.sqrt 2 * (Real.sqrt 2 * x + Real.sqrt 2 * Q * Real.sqrt (x * M)
              + Q * x / Real.sqrt M + Q ^ 2 * Real.sqrt x)) :=
      mul_le_mul_of_nonneg_left hP hCnn
    have eL : c * (8 * Real.sqrt 2 * L ^ 2 * Real.sqrt L)
          * (Real.sqrt (2 * M + Q ^ 2) * Real.sqrt (2 * M) * Real.sqrt (N + Q ^ 2) * Real.sqrt N)
        = c * (Real.sqrt (2 * M + Q ^ 2) * Real.sqrt (2 * M) * Real.sqrt (N + Q ^ 2) * Real.sqrt N)
          * (8 * Real.sqrt 2 * L ^ 2 * Real.sqrt L) := by ring
    have eR : c * (8 * Real.sqrt 2 * L ^ 2 * Real.sqrt L)
          * (2 * Real.sqrt 2 * (Real.sqrt 2 * x + Real.sqrt 2 * Q * Real.sqrt (x * M)
              + Q * x / Real.sqrt M + Q ^ 2 * Real.sqrt x))
        = (c * (Real.sqrt 2 * x + Real.sqrt 2 * Q * Real.sqrt (x * M)
              + Q * x / Real.sqrt M + Q ^ 2 * Real.sqrt x)) * (32 * L ^ 2 * Real.sqrt L) := by
      have h : c * (8 * Real.sqrt 2 * L ^ 2 * Real.sqrt L)
            * (2 * Real.sqrt 2 * (Real.sqrt 2 * x + Real.sqrt 2 * Q * Real.sqrt (x * M)
                + Q * x / Real.sqrt M + Q ^ 2 * Real.sqrt x))
          = c * ((Real.sqrt 2 * Real.sqrt 2) * (16 * L ^ 2 * Real.sqrt L))
            * (Real.sqrt 2 * x + Real.sqrt 2 * Q * Real.sqrt (x * M)
                + Q * x / Real.sqrt M + Q ^ 2 * Real.sqrt x) := by ring
      rw [h, sqrt2_mul_sqrt2]; ring
    have h2 : (c * (Real.sqrt 2 * x + Real.sqrt 2 * Q * Real.sqrt (x * M)
              + Q * x / Real.sqrt M + Q ^ 2 * Real.sqrt x)) * (32 * L ^ 2 * Real.sqrt L)
        ≤ 128 * c * L ^ 4 * (Real.sqrt 2 * x + Real.sqrt 2 * Q * Real.sqrt (x * M)
              + Q * x / Real.sqrt M + Q ^ 2 * Real.sqrt x) := by
      have hmul := mul_le_mul_of_nonneg_left hcoef (mul_nonneg hc hRnn)
      have e : (c * (Real.sqrt 2 * x + Real.sqrt 2 * Q * Real.sqrt (x * M)
              + Q * x / Real.sqrt M + Q ^ 2 * Real.sqrt x)) * (128 * L ^ 4)
          = 128 * c * L ^ 4 * (Real.sqrt 2 * x + Real.sqrt 2 * Q * Real.sqrt (x * M)
              + Q * x / Real.sqrt M + Q ^ 2 * Real.sqrt x) := by ring
      rw [e] at hmul
      exact hmul
    rw [eL, eR] at h1
    exact le_trans h1 h2
  calc c * Real.sqrt ((2 * M + Q ^ 2) * (2 * M * Real.log (4 * M + 2)))
        * Real.sqrt ((N + Q ^ 2) * (N * (Real.log (Real.exp 3 * T)) ^ 2))
        * Real.log (2 * (2 * M) * N + 2)
      ≤ c * (Real.sqrt (2 * M + Q ^ 2) * Real.sqrt (2 * M) * (Real.sqrt 2 * Real.sqrt L))
        * (Real.sqrt (N + Q ^ 2) * Real.sqrt N * (4 * L)) * (2 * L) := hstep4
    _ = c * (Real.sqrt (2 * M + Q ^ 2) * Real.sqrt (2 * M) * Real.sqrt (N + Q ^ 2) * Real.sqrt N)
        * (8 * Real.sqrt 2 * L ^ 2 * Real.sqrt L) := hcancel
    _ ≤ 128 * c * L ^ 4 * (Real.sqrt 2 * x + Real.sqrt 2 * Q * Real.sqrt (x * M)
          + Q * x / Real.sqrt M + Q ^ 2 * Real.sqrt x) := hER

end Commons.NumberTheory.BombieriVinogradov