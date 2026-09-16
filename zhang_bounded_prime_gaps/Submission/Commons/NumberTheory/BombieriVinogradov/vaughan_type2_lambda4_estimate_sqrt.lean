import Mathlib
import Submission.Commons.NumberTheory.BombieriVinogradov.vaughan_type2_lambda4_estimate

/-
Vaughan's type II (`λ₄`) estimate for the Bombieri--Vinogradov mean value theorem,
with the sharper logarithmic factor `(log)^{3}·(log)^{1/2}` (Akbary--Hambrook,
``The Bombieri--Vinogradov theorem``, §6; cf. Vaughan's mean value theorem).

The `λ₄`-piece is decomposed into dyadic blocks `T·2^j < m ≤ 2·T·2^j`; each block
is a bilinear form to which the maximal bilinear character large sieve applies,
and the block estimate keeps the `√(log)` factor rather than replacing it by `log`.
-/

namespace Commons.NumberTheory.BombieriVinogradov

open scoped BigOperators

set_option maxHeartbeats 1600000

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

private lemma lam4_block_real_bound_sqrt_aux (c M N x Q T L : ℝ) (hc : 0 ≤ c)
    (hM1 : 1 ≤ M) (hx1 : 1 ≤ x) (hMx : M ≤ x) (hN : N ≤ 2 * (x / M)) (hN1 : 1 ≤ N)
    (hQ1 : 1 ≤ Q) (hT1 : 1 ≤ T) (hL1 : 1 ≤ L)
    (hlogM : Real.log (4 * M + 2) ≤ 2 * L) (hlogT : Real.log (Real.exp 3 * T) ≤ 4 * L)
    (hlogN : Real.log (2 * (2 * M) * N + 2) ≤ 2 * L) :
    c * Real.sqrt ((2 * M + Q ^ 2) * (2 * M * Real.log (4 * M + 2)))
        * Real.sqrt ((N + Q ^ 2) * (N * (Real.log (Real.exp 3 * T)) ^ 2))
        * Real.log (2 * (2 * M) * N + 2)
      ≤ 64 * c * L ^ 2 * Real.sqrt L * (Real.sqrt 2 * x + Real.sqrt 2 * Q * Real.sqrt (x * M)
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
  have hcoef : 32 * L ^ 2 * Real.sqrt L ≤ 64 * L ^ 2 * Real.sqrt L := by
    have hnn : 0 ≤ L ^ 2 * Real.sqrt L := mul_nonneg (sq_nonneg L) (Real.sqrt_nonneg L)
    linarith
  have hER : c * (Real.sqrt (2 * M + Q ^ 2) * Real.sqrt (2 * M) * Real.sqrt (N + Q ^ 2) * Real.sqrt N)
        * (8 * Real.sqrt 2 * L ^ 2 * Real.sqrt L)
      ≤ 64 * c * L ^ 2 * Real.sqrt L * (Real.sqrt 2 * x + Real.sqrt 2 * Q * Real.sqrt (x * M)
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
        ≤ 64 * c * L ^ 2 * Real.sqrt L * (Real.sqrt 2 * x + Real.sqrt 2 * Q * Real.sqrt (x * M)
              + Q * x / Real.sqrt M + Q ^ 2 * Real.sqrt x) := by
      have hmul := mul_le_mul_of_nonneg_left hcoef (mul_nonneg hc hRnn)
      have e : (c * (Real.sqrt 2 * x + Real.sqrt 2 * Q * Real.sqrt (x * M)
              + Q * x / Real.sqrt M + Q ^ 2 * Real.sqrt x)) * (64 * L ^ 2 * Real.sqrt L)
          = 64 * c * L ^ 2 * Real.sqrt L * (Real.sqrt 2 * x + Real.sqrt 2 * Q * Real.sqrt (x * M)
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
    _ ≤ 64 * c * L ^ 2 * Real.sqrt L * (Real.sqrt 2 * x + Real.sqrt 2 * Q * Real.sqrt (x * M)
          + Q * x / Real.sqrt M + Q ^ 2 * Real.sqrt x) := hER

theorem vaughan_type2_lambda4_estimate_sqrt :
    ∃ C : ℝ, 0 < C ∧ ∀ x Q T : ℕ, 2 ≤ x → 2 ≤ Q → 1 ≤ T → T ≤ x →
      (∑ q ∈ Finset.Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) *
        ∑ χ ∈ (@Finset.filter (DirichletCharacter ℂ q) (fun χ => χ.IsPrimitive)
                (Classical.decPred _) Finset.univ),
          sSup ((fun y : ℕ => ‖∑ n ∈ Finset.Icc 1 y,
              (∑ m ∈ n.divisors.filter (fun m => T < m ∧ T < n / m),
                ((ArithmeticFunction.vonMangoldt m : ℝ) : ℂ) *
                  (∑ d ∈ (n / m).divisors.filter (fun d => d ≤ T),
                    ((ArithmeticFunction.moebius d : ℤ) : ℂ)))
              * χ (n : ZMod q)‖) '' Set.Icc 1 x))
      ≤ C * ((x : ℝ) + (Q : ℝ) * (x : ℝ) ^ (1 / 2 : ℝ) * (T : ℝ)
              + (Q : ℝ) * (x : ℝ) * ((T : ℝ) ^ (1 / 2 : ℝ))⁻¹
              + (Q : ℝ) ^ 2 * (x : ℝ) ^ (1 / 2 : ℝ))
          * (Real.log ((x : ℝ) * (Q : ℝ) + 2)) ^ 3
          * Real.sqrt (Real.log ((x : ℝ) * (Q : ℝ) + 2)) := by
  obtain ⟨cls, hclspos, hcls⟩ := maximal_bilinear_char_large_sieve_sSup
  obtain ⟨cVM, hVMpos, hVM⟩ := Commons.NumberTheory.ArithmeticFunction.sum_vonMangoldt_sq_le
  obtain ⟨cMoeb, hMoebpos, hMoeb⟩ := Commons.NumberTheory.Moebius.sum_moebius_small_divisors_sq_le
  refine ⟨2048 * (cls * Real.sqrt cVM * Real.sqrt cMoeb) + 1, by positivity, ?_⟩
  intro x Q T hx hQ hT hTx
  have hx1 : 1 ≤ x := by omega
  have hQ1 : 1 ≤ Q := by omega
  have hxR1 : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx1
  have hxR2 : (2 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
  have hQR2 : (2 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQ
  have hQR1 : (1 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast (by omega : 1 ≤ Q)
  have hxR0 : (0 : ℝ) ≤ (x : ℝ) := by positivity
  have hQR0 : (0 : ℝ) ≤ (Q : ℝ) := by positivity
  have hTR1 : (1 : ℝ) ≤ (T : ℝ) := by exact_mod_cast hT
  have hTR0 : (0 : ℝ) < (T : ℝ) := by exact_mod_cast (by omega : 0 < T)
  have hxTR : (T : ℝ) ≤ (x : ℝ) := by exact_mod_cast hTx
  set L : ℝ := Real.log ((x : ℝ) * (Q : ℝ) + 2) with hLdef
  have hL1 : 1 ≤ L := by
    rw [hLdef, Real.le_log_iff_exp_le (by positivity)]
    nlinarith [Real.exp_one_lt_d9, hxR2, hQR2]
  have hL0 : 0 ≤ L := le_trans (by norm_num) hL1
  have hlogxL : Real.log (x : ℝ) ≤ L := by
    rw [hLdef]
    apply Real.log_le_log (by positivity)
    nlinarith [hxR0, hQR1]
  have hlogTL : Real.log (T : ℝ) ≤ L := le_trans (Real.log_le_log hTR0 hxTR) hlogxL
  have hlog2L : Real.log 2 ≤ L := le_trans (by linarith only [Real.log_two_lt_d9]) hL1
  change (∑ q ∈ Finset.Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) *
        ∑ χ ∈ lam4Prim q, sSup ((fun y : ℕ =>
            ‖∑ n ∈ Finset.Icc 1 y, lam4C T n * χ (n : ZMod q)‖) '' Set.Icc 1 x))
      ≤ (2048 * (cls * Real.sqrt cVM * Real.sqrt cMoeb) + 1)
          * ((x : ℝ) + (Q : ℝ) * (x : ℝ) ^ (1 / 2 : ℝ) * (T : ℝ)
              + (Q : ℝ) * (x : ℝ) * ((T : ℝ) ^ (1 / 2 : ℝ))⁻¹
              + (Q : ℝ) ^ 2 * (x : ℝ) ^ (1 / 2 : ℝ)) * L ^ 3 * Real.sqrt L
  by_cases hcase : T * T ≤ x
  · -- main case
    have hq1 : 1 ≤ x / (T * T) :=
      (Nat.le_div_iff_mul_le (by positivity : 0 < T * T)).mpr (by simpa using hcase)
    have hqne : x / (T * T) ≠ 0 := by omega
    set J : ℕ := Nat.log 2 (x / (T * T)) + 1 with hJdef
    have hJv : J = Nat.log 2 (x / (T * T)) + 1 := hJdef
    have hJ_le : (J : ℝ) ≤ 3 * L := by
      have hmono : Nat.log 2 (x / (T * T)) ≤ Nat.log 2 x :=
        Nat.log_mono_right (Nat.div_le_self x (T * T))
      have h1 : (Nat.log 2 (x / (T * T)) : ℝ) ≤ Real.log (x : ℝ) / Real.log 2 :=
        le_trans (by exact_mod_cast hmono) (lam4_nat_log_two_cast_le x hx1)
      have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
      have h2 : Real.log (x : ℝ) / Real.log 2 ≤ L / Real.log 2 :=
        div_le_div_of_nonneg_right hlogxL (le_of_lt hlog2pos)
      have h3 : L / Real.log 2 ≤ 2 * L := by
        rw [div_le_iff₀ hlog2pos]
        nlinarith [hL0, Real.log_two_gt_d9]
      have hbig : (Nat.log 2 (x / (T * T)) : ℝ) ≤ 2 * L := le_trans h1 (le_trans h2 h3)
      rw [hJv]
      push_cast
      linarith
    have hTq : T * (x / (T * T)) ≤ x / T := by
      rw [Nat.le_div_iff_mul_le (by omega : 0 < T)]
      calc T * (x / (T * T)) * T = (T * T) * (x / (T * T)) := by ring
        _ ≤ x := Nat.mul_div_le x (T * T)
    have hTJ : (T : ℝ) * (2 : ℝ) ^ J ≤ 2 * (x : ℝ) / (T : ℝ) := by
      have hnat : T * 2 ^ J ≤ 2 * (x / T) := by
        rw [hJv, Nat.pow_succ]
        have h1 : 2 ^ Nat.log 2 (x / (T * T)) ≤ x / (T * T) :=
          Nat.pow_log_le_self 2 hqne
        calc T * (2 ^ Nat.log 2 (x / (T * T)) * 2)
              = T * 2 ^ Nat.log 2 (x / (T * T)) * 2 := by ring
          _ ≤ T * (x / (T * T)) * 2 := Nat.mul_le_mul_right 2 (Nat.mul_le_mul_left T h1)
          _ = 2 * (T * (x / (T * T))) := by ring
          _ ≤ 2 * (x / T) := Nat.mul_le_mul_left 2 hTq
      have hcast : ((T * 2 ^ J : ℕ) : ℝ) = (T : ℝ) * (2 : ℝ) ^ J := by push_cast; ring
      rw [← hcast]
      have h2 : ((T * 2 ^ J : ℕ) : ℝ) ≤ ((2 * (x / T) : ℕ) : ℝ) := by exact_mod_cast hnat
      refine le_trans h2 ?_
      have h3 : ((x / T : ℕ) : ℝ) ≤ (x : ℝ) / (T : ℝ) := Nat.cast_div_le
      rw [show ((2 * (x / T) : ℕ) : ℝ) = 2 * ((x / T : ℕ) : ℝ) by push_cast; ring, mul_div_assoc]
      exact mul_le_mul_of_nonneg_left h3 (by norm_num)
    have hcastM : ∀ j : ℕ, ((2 * (T * 2 ^ j) : ℕ) : ℝ) = 2 * ((T * 2 ^ j : ℕ) : ℝ) := by
      intro j; push_cast; ring
    have hMcase : ∀ j ∈ Finset.range J, T * 2 ^ j ≤ x := by
      intro j hj
      have hjQ : j ≤ Nat.log 2 (x / (T * T)) := by
        have : j < J := Finset.mem_range.mp hj
        rw [hJv] at this; omega
      have hpow : 2 ^ j ≤ x / (T * T) := by
        calc 2 ^ j ≤ 2 ^ Nat.log 2 (x / (T * T)) := pow_le_pow_right' (by norm_num) hjQ
          _ ≤ x / (T * T) := Nat.pow_log_le_self 2 hqne
      calc T * 2 ^ j ≤ T * (x / (T * T)) := Nat.mul_le_mul_left T hpow
        _ ≤ x / T := hTq
        _ ≤ x := Nat.div_le_self x T
    let saf : ℕ → ℝ := fun j => ∑ m ∈ Finset.Icc 1 (2 * (T * 2 ^ j)),
        ‖lam4A T (T * 2 ^ j) m‖ ^ 2
    let sbf : ℕ → ℝ := fun j => ∑ n ∈ Finset.Icc 1 (x / (T * 2 ^ j)),
        ‖lam4B T n‖ ^ 2
    let GS : ℕ → ℝ := fun j => Real.sqrt 2 * (x : ℝ)
        + Real.sqrt 2 * (Q : ℝ) * Real.sqrt ((x : ℝ) * ((T * 2 ^ j : ℕ) : ℝ))
        + (Q : ℝ) * (x : ℝ) / Real.sqrt ((T * 2 ^ j : ℕ) : ℝ)
        + (Q : ℝ) ^ 2 * Real.sqrt (x : ℝ)
    let bnd : ℕ → ℝ := fun j => cls
        * Real.sqrt ((((2 * (T * 2 ^ j) : ℕ) : ℝ) + (Q : ℝ) ^ 2) * saf j)
        * Real.sqrt ((((x / (T * 2 ^ j) : ℕ) : ℝ) + (Q : ℝ) ^ 2) * sbf j)
        * Real.log (2 * ((2 * (T * 2 ^ j) : ℕ) : ℝ) * ((x / (T * 2 ^ j) : ℕ) : ℝ) + 2)
    have hsaf_bd : ∀ j : ℕ, saf j ≤ cVM * (((2 * (T * 2 ^ j) : ℕ) : ℝ))
        * Real.log (2 * (((2 * (T * 2 ^ j)) : ℕ) : ℝ) + 2) := by
      intro j
      dsimp only [saf]
      refine le_trans (Finset.sum_le_sum (fun m _ => ?_)) (hVM (2 * (T * 2 ^ j)))
      show ‖lam4A T (T * 2 ^ j) m‖ ^ 2 ≤ (ArithmeticFunction.vonMangoldt m) ^ 2
      dsimp only [lam4A]
      split_ifs with hc
      · exact le_of_eq (by rw [← Complex.normSq_eq_norm_sq, Complex.normSq_ofReal]; ring)
      · rw [norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]; exact sq_nonneg _
    have hsbf_bd : ∀ j : ℕ, sbf j ≤ cMoeb * (((x / (T * 2 ^ j) : ℕ) : ℝ))
        * (Real.log (Real.exp 3 * (T : ℝ))) ^ 2 := by
      intro j
      dsimp only [sbf]
      refine le_trans (Finset.sum_le_sum (fun n _ => ?_)) (hMoeb (x / (T * 2 ^ j)) T hT)
      show ‖lam4B T n‖ ^ 2
        ≤ (∑ d ∈ n.divisors.filter (fun d => d ≤ T), (ArithmeticFunction.moebius d : ℝ)) ^ 2
      dsimp only [lam4B]
      split_ifs with hc
      · have hcast : (∑ d ∈ n.divisors.filter (fun d => d ≤ T),
              ((ArithmeticFunction.moebius d : ℤ) : ℂ))
            = (((∑ d ∈ n.divisors.filter (fun d => d ≤ T),
                (ArithmeticFunction.moebius d : ℝ)) : ℝ) : ℂ) := by
          rw [Complex.ofReal_sum]
          refine Finset.sum_congr rfl (fun d _ => ?_)
          push_cast; ring
        rw [hcast]
        exact le_of_eq (by rw [← Complex.normSq_eq_norm_sq, Complex.normSq_ofReal]; ring)
      · rw [norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]; exact sq_nonneg _
    have hsup : ∀ (q : ℕ) (χ : DirichletCharacter ℂ q),
        sSup ((fun y : ℕ => ‖∑ n ∈ Finset.Icc 1 y, lam4C T n * χ (n : ZMod q)‖)
            '' Set.Icc 1 x)
          ≤ ∑ j ∈ Finset.range J, sSup ((fun y : ℕ =>
              ‖∑ n ∈ Finset.Icc 1 y, lam4BlkT T (T * 2 ^ j) n * χ (n : ZMod q)‖)
                '' Set.Icc 1 x) := by
      intro q χ
      have hpt : ∀ y ∈ Set.Icc 1 x,
          ‖∑ n ∈ Finset.Icc 1 y, lam4C T n * χ (n : ZMod q)‖
            ≤ ∑ j ∈ Finset.range J,
                ‖∑ n ∈ Finset.Icc 1 y, lam4BlkT T (T * 2 ^ j) n * χ (n : ZMod q)‖ := by
        intro y hy
        have hcov : (∑ n ∈ Finset.Icc 1 y, lam4C T n * χ (n : ZMod q))
            = ∑ j ∈ Finset.range J, ∑ n ∈ Finset.Icc 1 y,
                lam4BlkT T (T * 2 ^ j) n * χ (n : ZMod q) := by
          have hC : ∀ n ∈ Finset.Icc 1 y, lam4C T n
              = ∑ j ∈ Finset.range J, lam4BlkT T (T * 2 ^ j) n := by
            intro n hn
            have hnx : n ≤ x := le_trans (Finset.mem_Icc.mp hn).2 hy.2
            rw [hJv]
            exact lam4C_cover T x n hT hnx
          calc (∑ n ∈ Finset.Icc 1 y, lam4C T n * χ (n : ZMod q))
              = ∑ n ∈ Finset.Icc 1 y,
                  (∑ j ∈ Finset.range J, lam4BlkT T (T * 2 ^ j) n) * χ (n : ZMod q) := by
                refine Finset.sum_congr rfl (fun n hn => ?_)
                rw [hC n hn]
            _ = ∑ n ∈ Finset.Icc 1 y, ∑ j ∈ Finset.range J,
                  lam4BlkT T (T * 2 ^ j) n * χ (n : ZMod q) := by
                refine Finset.sum_congr rfl (fun n _ => ?_)
                rw [Finset.sum_mul]
            _ = ∑ j ∈ Finset.range J, ∑ n ∈ Finset.Icc 1 y,
                  lam4BlkT T (T * 2 ^ j) n * χ (n : ZMod q) := Finset.sum_comm
        rw [hcov]
        exact norm_sum_le _ _
      calc sSup ((fun y : ℕ => ‖∑ n ∈ Finset.Icc 1 y, lam4C T n * χ (n : ZMod q)‖)
              '' Set.Icc 1 x)
          ≤ sSup ((fun y : ℕ => ∑ j ∈ Finset.range J,
                ‖∑ n ∈ Finset.Icc 1 y, lam4BlkT T (T * 2 ^ j) n * χ (n : ZMod q)‖)
                  '' Set.Icc 1 x) := lam4_sSup_image_Icc_le hx1 le_rfl hpt
        _ ≤ ∑ j ∈ Finset.range J, sSup ((fun y : ℕ =>
                ‖∑ n ∈ Finset.Icc 1 y, lam4BlkT T (T * 2 ^ j) n * χ (n : ZMod q)‖)
                  '' Set.Icc 1 x) := lam4_sSup_finset_sum_le hx1 _ _
    have hLS : ∀ j ∈ Finset.range J,
        (∑ q ∈ Finset.Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) *
          ∑ χ ∈ lam4Prim q, sSup ((fun y : ℕ =>
              ‖∑ n ∈ Finset.Icc 1 y, lam4BlkT T (T * 2 ^ j) n * χ (n : ZMod q)‖)
                '' Set.Icc 1 x))
          ≤ bnd j := by
      intro j hj
      have hM1 : 1 ≤ T * 2 ^ j := by
        have := Nat.mul_pos (by omega : 0 < T) (pow_pos (by norm_num : (0:ℕ) < 2) j)
        omega
      have hMT : T ≤ T * 2 ^ j := by
        have h2 : 1 ≤ 2 ^ j := Nat.one_le_two_pow
        calc T = T * 1 := by ring
          _ ≤ T * 2 ^ j := Nat.mul_le_mul_left T h2
      have hMx : T * 2 ^ j ≤ x := hMcase j hj
      have hN1 : 1 ≤ x / (T * 2 ^ j) := Nat.div_pos hMx (by positivity)
      have hMls : 1 ≤ 2 * (T * 2 ^ j) := by omega
      have h2Mx : x ≤ 2 * (T * 2 ^ j) * (x / (T * 2 ^ j)) :=
        lam4_two_mul_div_ge (T * 2 ^ j) x hM1 hMx
      have hstep : (∑ q ∈ Finset.Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) *
            ∑ χ ∈ lam4Prim q, sSup ((fun y : ℕ =>
                ‖∑ n ∈ Finset.Icc 1 y, lam4BlkT T (T * 2 ^ j) n * χ (n : ZMod q)‖)
                  '' Set.Icc 1 x))
          ≤ ∑ q ∈ Finset.Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) *
            ∑ χ ∈ lam4Prim q, sSup ((fun y : ℕ =>
                ‖∑ m ∈ Finset.Icc 1 (2 * (T * 2 ^ j)),
                    ∑ k ∈ Finset.Icc 1 (x / (T * 2 ^ j)),
                    (if m * k ≤ y then (1 : ℂ) else 0) * lam4A T (T * 2 ^ j) m
                      * lam4B T k * χ ((m * k : ℕ) : ZMod q)‖)
                  '' Set.Icc 1 (2 * (T * 2 ^ j) * (x / (T * 2 ^ j)))) := by
        refine Finset.sum_le_sum (fun q _ => mul_le_mul_of_nonneg_left ?_ (by positivity))
        refine Finset.sum_le_sum (fun χ _ => ?_)
        refine lam4_sSup_image_Icc_le hx1 h2Mx ?_
        intro y hy
        rw [lam4BlkT_bilinear T (T * 2 ^ j) x y q hM1 hMT hMx hy.2 χ]
      calc (∑ q ∈ Finset.Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) *
            ∑ χ ∈ lam4Prim q, sSup ((fun y : ℕ =>
                ‖∑ n ∈ Finset.Icc 1 y, lam4BlkT T (T * 2 ^ j) n * χ (n : ZMod q)‖)
                  '' Set.Icc 1 x))
          ≤ _ := hstep
        _ ≤ bnd j := hcls Q (2 * (T * 2 ^ j)) (x / (T * 2 ^ j)) hQ1 hMls hN1
              (lam4A T (T * 2 ^ j)) (lam4B T)
    have hB : ∀ j ∈ Finset.range J,
        bnd j ≤ 64 * (cls * Real.sqrt cVM * Real.sqrt cMoeb) * L ^ 2 * Real.sqrt L * GS j := by
      intro j hj
      have hM1 : 1 ≤ T * 2 ^ j := by
        have := Nat.mul_pos (by omega : 0 < T) (pow_pos (by norm_num : (0:ℕ) < 2) j)
        omega
      have hMx : T * 2 ^ j ≤ x := hMcase j hj
      have hN1 : 1 ≤ x / (T * 2 ^ j) := Nat.div_pos hMx (by positivity)
      have hM1r : (1 : ℝ) ≤ ((T * 2 ^ j : ℕ) : ℝ) := by exact_mod_cast hM1
      have hMxr : ((T * 2 ^ j : ℕ) : ℝ) ≤ (x : ℝ) := by exact_mod_cast hMx
      have hN1r : (1 : ℝ) ≤ ((x / (T * 2 ^ j) : ℕ) : ℝ) := by exact_mod_cast hN1
      have hNle : ((x / (T * 2 ^ j) : ℕ) : ℝ) ≤ 2 * ((x : ℝ) / ((T * 2 ^ j : ℕ) : ℝ)) := by
        have h1 : ((x / (T * 2 ^ j) : ℕ) : ℝ) ≤ (x : ℝ) / ((T * 2 ^ j : ℕ) : ℝ) := Nat.cast_div_le
        have h2 : (0 : ℝ) ≤ (x : ℝ) / ((T * 2 ^ j : ℕ) : ℝ) := by positivity
        linarith
      have hlogM : Real.log (4 * ((T * 2 ^ j : ℕ) : ℝ) + 2) ≤ 2 * L := by
        have h4 : 4 * ((T * 2 ^ j : ℕ) : ℝ) + 2 ≤ 2 * ((x : ℝ) * (Q : ℝ) + 2) := by
          nlinarith [hMxr, hxR0, hQR2, hQR0]
        calc Real.log (4 * ((T * 2 ^ j : ℕ) : ℝ) + 2)
            ≤ Real.log (2 * ((x : ℝ) * (Q : ℝ) + 2)) := Real.log_le_log (by positivity) h4
          _ = Real.log 2 + L := by rw [Real.log_mul (by norm_num) (by positivity), hLdef]
          _ ≤ 2 * L := by linarith [hlog2L, hL1]
      have hlogT : Real.log (Real.exp 3 * (T : ℝ)) ≤ 4 * L := by
        rw [Real.log_mul (Real.exp_ne_zero 3) (ne_of_gt hTR0), Real.log_exp]
        linarith [hlogTL, hL1]
      have hlogN : Real.log (2 * (2 * ((T * 2 ^ j : ℕ) : ℝ)) * ((x / (T * 2 ^ j) : ℕ) : ℝ) + 2)
          ≤ 2 * L := by
        have hMN : ((T * 2 ^ j : ℕ) : ℝ) * ((x / (T * 2 ^ j) : ℕ) : ℝ) ≤ (x : ℝ) := by
          have h3 : ((T * 2 ^ j) * (x / (T * 2 ^ j)) : ℕ) ≤ x := Nat.mul_div_le x _
          calc ((T * 2 ^ j : ℕ) : ℝ) * ((x / (T * 2 ^ j) : ℕ) : ℝ)
              = (((T * 2 ^ j) * (x / (T * 2 ^ j)) : ℕ) : ℝ) := by push_cast; ring
            _ ≤ (x : ℝ) := by exact_mod_cast h3
        have h4 : 2 * (2 * ((T * 2 ^ j : ℕ) : ℝ)) * ((x / (T * 2 ^ j) : ℕ) : ℝ) + 2
            ≤ 2 * ((x : ℝ) * (Q : ℝ) + 2) := by
          nlinarith [hMN, hxR0, hQR2, hQR0]
        calc Real.log (2 * (2 * ((T * 2 ^ j : ℕ) : ℝ)) * ((x / (T * 2 ^ j) : ℕ) : ℝ) + 2)
            ≤ Real.log (2 * ((x : ℝ) * (Q : ℝ) + 2)) := Real.log_le_log (by positivity) h4
          _ = Real.log 2 + L := by rw [Real.log_mul (by norm_num) (by positivity), hLdef]
          _ ≤ 2 * L := by linarith [hlog2L, hL1]
      have hsaj : saf j ≤ cVM * (2 * ((T * 2 ^ j : ℕ) : ℝ)
          * Real.log (4 * ((T * 2 ^ j : ℕ) : ℝ) + 2)) := by
        have h := hsaf_bd j
        rw [hcastM j] at h
        have heq : cVM * (2 * ((T * 2 ^ j : ℕ) : ℝ)) * Real.log (2 * (2 * ((T * 2 ^ j : ℕ) : ℝ)) + 2)
            = cVM * (2 * ((T * 2 ^ j : ℕ) : ℝ) * Real.log (4 * ((T * 2 ^ j : ℕ) : ℝ) + 2)) := by
          have h2 : (2 * (2 * ((T * 2 ^ j : ℕ) : ℝ)) + 2) = (4 * ((T * 2 ^ j : ℕ) : ℝ) + 2) := by ring
          rw [h2]; ring
        rwa [heq] at h
      have hsbj : sbf j ≤ cMoeb * (((x / (T * 2 ^ j) : ℕ) : ℝ)
          * (Real.log (Real.exp 3 * (T : ℝ))) ^ 2) := by
        have h := hsbf_bd j
        rwa [mul_assoc] at h
      have hsq1 : Real.sqrt ((2 * ((T * 2 ^ j : ℕ) : ℝ) + (Q : ℝ) ^ 2) * saf j)
          ≤ Real.sqrt cVM * Real.sqrt ((2 * ((T * 2 ^ j : ℕ) : ℝ) + (Q : ℝ) ^ 2)
              * (2 * ((T * 2 ^ j : ℕ) : ℝ) * Real.log (4 * ((T * 2 ^ j : ℕ) : ℝ) + 2))) := by
        calc Real.sqrt ((2 * ((T * 2 ^ j : ℕ) : ℝ) + (Q : ℝ) ^ 2) * saf j)
            ≤ Real.sqrt (cVM * ((2 * ((T * 2 ^ j : ℕ) : ℝ) + (Q : ℝ) ^ 2)
                * (2 * ((T * 2 ^ j : ℕ) : ℝ) * Real.log (4 * ((T * 2 ^ j : ℕ) : ℝ) + 2)))) :=
              Real.sqrt_le_sqrt (by
                calc (2 * ((T * 2 ^ j : ℕ) : ℝ) + (Q : ℝ) ^ 2) * saf j
                    ≤ (2 * ((T * 2 ^ j : ℕ) : ℝ) + (Q : ℝ) ^ 2)
                      * (cVM * (2 * ((T * 2 ^ j : ℕ) : ℝ)
                        * Real.log (4 * ((T * 2 ^ j : ℕ) : ℝ) + 2))) :=
                      mul_le_mul_of_nonneg_left hsaj (by positivity)
                  _ = cVM * ((2 * ((T * 2 ^ j : ℕ) : ℝ) + (Q : ℝ) ^ 2)
                      * (2 * ((T * 2 ^ j : ℕ) : ℝ)
                        * Real.log (4 * ((T * 2 ^ j : ℕ) : ℝ) + 2))) := by ring)
          _ = Real.sqrt cVM * Real.sqrt ((2 * ((T * 2 ^ j : ℕ) : ℝ) + (Q : ℝ) ^ 2)
                * (2 * ((T * 2 ^ j : ℕ) : ℝ) * Real.log (4 * ((T * 2 ^ j : ℕ) : ℝ) + 2))) :=
              Real.sqrt_mul (le_of_lt hVMpos) _
      have hsq2 : Real.sqrt ((((x / (T * 2 ^ j) : ℕ) : ℝ) + (Q : ℝ) ^ 2) * sbf j)
          ≤ Real.sqrt cMoeb * Real.sqrt ((((x / (T * 2 ^ j) : ℕ) : ℝ) + (Q : ℝ) ^ 2)
              * (((x / (T * 2 ^ j) : ℕ) : ℝ) * (Real.log (Real.exp 3 * (T : ℝ))) ^ 2)) := by
        calc Real.sqrt ((((x / (T * 2 ^ j) : ℕ) : ℝ) + (Q : ℝ) ^ 2) * sbf j)
            ≤ Real.sqrt (cMoeb * ((((x / (T * 2 ^ j) : ℕ) : ℝ) + (Q : ℝ) ^ 2)
                * (((x / (T * 2 ^ j) : ℕ) : ℝ) * (Real.log (Real.exp 3 * (T : ℝ))) ^ 2))) :=
              Real.sqrt_le_sqrt (by
                calc (((x / (T * 2 ^ j) : ℕ) : ℝ) + (Q : ℝ) ^ 2) * sbf j
                    ≤ (((x / (T * 2 ^ j) : ℕ) : ℝ) + (Q : ℝ) ^ 2)
                      * (cMoeb * (((x / (T * 2 ^ j) : ℕ) : ℝ)
                        * (Real.log (Real.exp 3 * (T : ℝ))) ^ 2)) :=
                      mul_le_mul_of_nonneg_left hsbj (by positivity)
                  _ = cMoeb * ((((x / (T * 2 ^ j) : ℕ) : ℝ) + (Q : ℝ) ^ 2)
                      * (((x / (T * 2 ^ j) : ℕ) : ℝ)
                        * (Real.log (Real.exp 3 * (T : ℝ))) ^ 2)) := by ring)
          _ = Real.sqrt cMoeb * Real.sqrt ((((x / (T * 2 ^ j) : ℕ) : ℝ) + (Q : ℝ) ^ 2)
                * (((x / (T * 2 ^ j) : ℕ) : ℝ) * (Real.log (Real.exp 3 * (T : ℝ))) ^ 2)) :=
              Real.sqrt_mul (le_of_lt hMoebpos) _
      have hBapp := lam4_block_real_bound_sqrt_aux 1 ((T * 2 ^ j : ℕ) : ℝ) ((x / (T * 2 ^ j) : ℕ) : ℝ)
          (x : ℝ) (Q : ℝ) (T : ℝ) L (by norm_num) hM1r hxR1 hMxr hNle hN1r hQR1 hTR1 hL1
          hlogM hlogT hlogN
      dsimp only [bnd]
      rw [hcastM j]
      calc cls * Real.sqrt ((2 * ((T * 2 ^ j : ℕ) : ℝ) + (Q : ℝ) ^ 2) * saf j)
            * Real.sqrt ((((x / (T * 2 ^ j) : ℕ) : ℝ) + (Q : ℝ) ^ 2) * sbf j)
            * Real.log (2 * (2 * ((T * 2 ^ j : ℕ) : ℝ)) * ((x / (T * 2 ^ j) : ℕ) : ℝ) + 2)
          ≤ cls * (Real.sqrt cVM * Real.sqrt ((2 * ((T * 2 ^ j : ℕ) : ℝ) + (Q : ℝ) ^ 2)
                * (2 * ((T * 2 ^ j : ℕ) : ℝ) * Real.log (4 * ((T * 2 ^ j : ℕ) : ℝ) + 2))))
              * (Real.sqrt cMoeb * Real.sqrt ((((x / (T * 2 ^ j) : ℕ) : ℝ) + (Q : ℝ) ^ 2)
                * (((x / (T * 2 ^ j) : ℕ) : ℝ) * (Real.log (Real.exp 3 * (T : ℝ))) ^ 2)))
              * Real.log (2 * (2 * ((T * 2 ^ j : ℕ) : ℝ)) * ((x / (T * 2 ^ j) : ℕ) : ℝ) + 2) := by
            have hC1nn : 0 ≤ Real.log (2 * (2 * ((T * 2 ^ j : ℕ) : ℝ)) * ((x / (T * 2 ^ j) : ℕ) : ℝ) + 2) :=
              Real.log_nonneg (by nlinarith [hM1r, hN1r])
            refine mul_le_mul_of_nonneg_right ?_ hC1nn
            refine mul_le_mul ?_ hsq2 (Real.sqrt_nonneg _) (by positivity)
            exact mul_le_mul_of_nonneg_left hsq1 (le_of_lt hclspos)
        _ = cls * Real.sqrt cVM * Real.sqrt cMoeb
              * (Real.sqrt ((2 * ((T * 2 ^ j : ℕ) : ℝ) + (Q : ℝ) ^ 2)
                  * (2 * ((T * 2 ^ j : ℕ) : ℝ) * Real.log (4 * ((T * 2 ^ j : ℕ) : ℝ) + 2)))
                * Real.sqrt ((((x / (T * 2 ^ j) : ℕ) : ℝ) + (Q : ℝ) ^ 2)
                  * (((x / (T * 2 ^ j) : ℕ) : ℝ) * (Real.log (Real.exp 3 * (T : ℝ))) ^ 2))
                * Real.log (2 * (2 * ((T * 2 ^ j : ℕ) : ℝ)) * ((x / (T * 2 ^ j) : ℕ) : ℝ) + 2)) := by ring
        _ ≤ cls * Real.sqrt cVM * Real.sqrt cMoeb * (64 * L ^ 2 * Real.sqrt L * GS j) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            dsimp only [GS]
            simpa only [one_mul, mul_one] using hBapp
        _ = 64 * (cls * Real.sqrt cVM * Real.sqrt cMoeb) * L ^ 2 * Real.sqrt L * GS j := by ring
    have hfin : (∑ j ∈ Finset.range J, bnd j)
        ≤ 64 * (cls * Real.sqrt cVM * Real.sqrt cMoeb) * L ^ 2 * Real.sqrt L
            * (32 * L * ((x : ℝ) + (Q : ℝ) * Real.sqrt (x : ℝ) * (T : ℝ)
                + (Q : ℝ) * (x : ℝ) / Real.sqrt (T : ℝ) + (Q : ℝ) ^ 2 * Real.sqrt (x : ℝ))) := by
      calc (∑ j ∈ Finset.range J, bnd j)
          ≤ ∑ j ∈ Finset.range J, 64 * (cls * Real.sqrt cVM * Real.sqrt cMoeb) * L ^ 2 * Real.sqrt L * GS j :=
            Finset.sum_le_sum hB
        _ = 64 * (cls * Real.sqrt cVM * Real.sqrt cMoeb) * L ^ 2 * Real.sqrt L * (∑ j ∈ Finset.range J, GS j) := by
            rw [Finset.mul_sum]
        _ ≤ 64 * (cls * Real.sqrt cVM * Real.sqrt cMoeb) * L ^ 2 * Real.sqrt L
              * (32 * L * ((x : ℝ) + (Q : ℝ) * Real.sqrt (x : ℝ) * (T : ℝ)
                + (Q : ℝ) * (x : ℝ) / Real.sqrt (T : ℝ) + (Q : ℝ) ^ 2 * Real.sqrt (x : ℝ))) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            have hcongr : (∑ j ∈ Finset.range J, GS j)
                = ∑ j ∈ Finset.range J, (Real.sqrt 2 * (x : ℝ)
                    + Real.sqrt 2 * (Q : ℝ) * Real.sqrt ((x : ℝ) * ((T : ℝ) * (2 : ℝ) ^ j))
                    + (Q : ℝ) * (x : ℝ) / Real.sqrt ((T : ℝ) * (2 : ℝ) ^ j)
                    + (Q : ℝ) ^ 2 * Real.sqrt (x : ℝ)) := by
              refine Finset.sum_congr rfl (fun j _ => ?_)
              dsimp only [GS]
              rw [show ((T * 2 ^ j : ℕ) : ℝ) = (T : ℝ) * (2 : ℝ) ^ j by push_cast; ring]
            rw [hcongr]
            exact lam4_dyadic_sum_bound (x : ℝ) (Q : ℝ) (T : ℝ) L J hxR1 hQR0 hTR1 hL1 hJ_le hTJ
    have hcomb : (∑ q ∈ Finset.Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) *
          ∑ χ ∈ lam4Prim q, sSup ((fun y : ℕ =>
              ‖∑ n ∈ Finset.Icc 1 y, lam4C T n * χ (n : ZMod q)‖) '' Set.Icc 1 x))
        ≤ ∑ j ∈ Finset.range J, bnd j := by
      have hswap : (∑ q ∈ Finset.Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) *
            ∑ χ ∈ lam4Prim q, ∑ j ∈ Finset.range J, sSup ((fun y : ℕ =>
                ‖∑ n ∈ Finset.Icc 1 y, lam4BlkT T (T * 2 ^ j) n * χ (n : ZMod q)‖)
                  '' Set.Icc 1 x))
          = ∑ j ∈ Finset.range J, ∑ q ∈ Finset.Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) *
            ∑ χ ∈ lam4Prim q, sSup ((fun y : ℕ =>
                ‖∑ n ∈ Finset.Icc 1 y, lam4BlkT T (T * 2 ^ j) n * χ (n : ZMod q)‖)
                  '' Set.Icc 1 x) := by
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [Finset.sum_comm]
      calc (∑ q ∈ Finset.Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) *
            ∑ χ ∈ lam4Prim q, sSup ((fun y : ℕ =>
                ‖∑ n ∈ Finset.Icc 1 y, lam4C T n * χ (n : ZMod q)‖) '' Set.Icc 1 x))
          ≤ ∑ q ∈ Finset.Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) *
            ∑ χ ∈ lam4Prim q, ∑ j ∈ Finset.range J, sSup ((fun y : ℕ =>
                ‖∑ n ∈ Finset.Icc 1 y, lam4BlkT T (T * 2 ^ j) n * χ (n : ZMod q)‖)
                  '' Set.Icc 1 x) := by
            refine Finset.sum_le_sum (fun q _ => mul_le_mul_of_nonneg_left ?_ (by positivity))
            exact Finset.sum_le_sum (fun χ _ => hsup q χ)
        _ = _ := hswap
        _ ≤ ∑ j ∈ Finset.range J, bnd j := Finset.sum_le_sum hLS
    have hSSe : ((x : ℝ) + (Q : ℝ) * Real.sqrt (x : ℝ) * (T : ℝ)
          + (Q : ℝ) * (x : ℝ) / Real.sqrt (T : ℝ) + (Q : ℝ) ^ 2 * Real.sqrt (x : ℝ))
        = ((x : ℝ) + (Q : ℝ) * (x : ℝ) ^ (1 / 2 : ℝ) * (T : ℝ)
            + (Q : ℝ) * (x : ℝ) * ((T : ℝ) ^ (1 / 2 : ℝ))⁻¹
            + (Q : ℝ) ^ 2 * (x : ℝ) ^ (1 / 2 : ℝ)) := by
      simp only [Real.sqrt_eq_rpow, div_eq_mul_inv]
    rw [← hSSe]
    have hSnn : 0 ≤ ((x : ℝ) + (Q : ℝ) * Real.sqrt (x : ℝ) * (T : ℝ)
        + (Q : ℝ) * (x : ℝ) / Real.sqrt (T : ℝ) + (Q : ℝ) ^ 2 * Real.sqrt (x : ℝ)) := by positivity
    refine le_trans (le_trans hcomb hfin) ?_
    have h1 : 2048 * (cls * Real.sqrt cVM * Real.sqrt cMoeb) * L ^ 3
        ≤ (2048 * (cls * Real.sqrt cVM * Real.sqrt cMoeb) + 1) * L ^ 3 :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    have h2 : 2048 * (cls * Real.sqrt cVM * Real.sqrt cMoeb) * L ^ 3 * Real.sqrt L
        ≤ (2048 * (cls * Real.sqrt cVM * Real.sqrt cMoeb) + 1) * L ^ 3 * Real.sqrt L :=
      mul_le_mul_of_nonneg_right h1 (Real.sqrt_nonneg L)
    calc 64 * (cls * Real.sqrt cVM * Real.sqrt cMoeb) * L ^ 2 * Real.sqrt L
            * (32 * L * ((x : ℝ) + (Q : ℝ) * Real.sqrt (x : ℝ) * (T : ℝ)
              + (Q : ℝ) * (x : ℝ) / Real.sqrt (T : ℝ) + (Q : ℝ) ^ 2 * Real.sqrt (x : ℝ)))
        = 2048 * (cls * Real.sqrt cVM * Real.sqrt cMoeb) * L ^ 3 * Real.sqrt L
            * ((x : ℝ) + (Q : ℝ) * Real.sqrt (x : ℝ) * (T : ℝ)
              + (Q : ℝ) * (x : ℝ) / Real.sqrt (T : ℝ) + (Q : ℝ) ^ 2 * Real.sqrt (x : ℝ)) := by ring
      _ ≤ (2048 * (cls * Real.sqrt cVM * Real.sqrt cMoeb) + 1) * L ^ 3 * Real.sqrt L
            * ((x : ℝ) + (Q : ℝ) * Real.sqrt (x : ℝ) * (T : ℝ)
              + (Q : ℝ) * (x : ℝ) / Real.sqrt (T : ℝ) + (Q : ℝ) ^ 2 * Real.sqrt (x : ℝ)) :=
          mul_le_mul_of_nonneg_right h2 hSnn
      _ = (2048 * (cls * Real.sqrt cVM * Real.sqrt cMoeb) + 1)
            * ((x : ℝ) + (Q : ℝ) * Real.sqrt (x : ℝ) * (T : ℝ)
              + (Q : ℝ) * (x : ℝ) / Real.sqrt (T : ℝ) + (Q : ℝ) ^ 2 * Real.sqrt (x : ℝ)) * L ^ 3 * Real.sqrt L := by ring
  · -- degenerate case: T * T > x
    push_neg at hcase
    have hcoeff : ∀ n, n ≤ x → lam4C T n = 0 := by
      intro n hn
      rw [lam4C]
      apply Finset.sum_eq_zero
      intro m hm
      obtain ⟨hmdiv, hTm, hTnm⟩ := Finset.mem_filter.mp hm
      exfalso
      have hmdvd : m ∣ n := (Nat.mem_divisors.mp hmdiv).1
      have hnm : m * (n / m) = n := Nat.mul_div_cancel' hmdvd
      have h1 : T + 1 ≤ m := hTm
      have h2 : T + 1 ≤ n / m := hTnm
      have h3 : (T + 1) * (T + 1) ≤ m * (n / m) := Nat.mul_le_mul h1 h2
      rw [hnm] at h3
      nlinarith [h3, hn, hcase]
    have hLHS0 : (∑ q ∈ Finset.Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) *
          ∑ χ ∈ lam4Prim q, sSup ((fun y : ℕ =>
              ‖∑ n ∈ Finset.Icc 1 y, lam4C T n * χ (n : ZMod q)‖) '' Set.Icc 1 x)) ≤ 0 := by
      apply Finset.sum_nonpos
      intro q hq
      apply mul_nonpos_of_nonneg_of_nonpos
      · positivity
      · apply Finset.sum_nonpos
        intro χ hχ
        apply csSup_le
        · exact ⟨_, ⟨1, ⟨le_rfl, hx1⟩, rfl⟩⟩
        · rintro v ⟨y, hy, rfl⟩
          have hz : (∑ n ∈ Finset.Icc 1 y, lam4C T n * χ (n : ZMod q)) = 0 := by
            apply Finset.sum_eq_zero
            intro n hn
            rw [hcoeff n (le_trans (Finset.mem_Icc.mp hn).2 hy.2), zero_mul]
          change ‖∑ n ∈ Finset.Icc 1 y, lam4C T n * χ (n : ZMod q)‖ ≤ 0
          rw [hz, norm_zero]
    refine le_trans hLHS0 ?_
    positivity

end Commons.NumberTheory.BombieriVinogradov
