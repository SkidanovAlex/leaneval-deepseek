import Mathlib
import Submission.Subspace.MaxRankParams
import Submission.Commons.Analysis.Real.log_two_mul_le_mul_of_ge

/-!
# Numeric lemmas for the maximal-rank core

Each lemma is a self-contained scalar estimate with the *explicit* threshold `mrA` of
`MaxRankParams`.  Splitting them off keeps every declaration inside its own heartbeat budget
(the assembled `max_rank_core` is a single very long proof).
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false

open scoped BigOperators

namespace Submission.Subspace

/-- (a) The Siegel constant term: `log C ≤ η^{2^{m-1}}·θ·D/8`. -/
lemma mrnum_logC {n : ℕ} {ε S θ MΛ C D : ℝ} {m : ℕ}
    (hε : 0 < ε) (hS : 0 < S) (hθ : 0 < θ) (hC1 : 1 ≤ C)
    (hD : mrA n ε S θ MΛ C m / (1 + mrTheta n ε S) ≤ D) :
    Real.log C ≤ mrEta n ε S ^ (2 ^ (m - 1)) * θ * D / 8 := by
  have hE : (0:ℝ) < mrEta n ε S ^ (2 ^ (m - 1)) * θ :=
    mul_pos (pow_pos (mrEta_pos hε hS) _) hθ
  have hΘ : (0:ℝ) < 1 + mrTheta n ε S := by
    have := mrTheta_pos (n := n) hε hS; linarith
  have hlogC0 : 0 ≤ Real.log C := Real.log_nonneg hC1
  have hA4 := le_mrA_4 (n := n) (ε := ε) (S := S) (θ := θ) (MΛ := MΛ) (C := C) (m := m)
  rw [div_le_iff₀ hE] at hA4
  have hD' : mrA n ε S θ MΛ C m ≤ D * (1 + mrTheta n ε S) := by
    have := (div_le_iff₀ hΘ).mp hD
    linarith [this]
  have h1 : 8 * Real.log C ≤ mrEta n ε S ^ (2 ^ (m - 1)) * θ * D := by
    have h2 : 8 * (1 + mrTheta n ε S) * Real.log C
        ≤ D * (1 + mrTheta n ε S) * (mrEta n ε S ^ (2 ^ (m - 1)) * θ) :=
      le_trans hA4 (mul_le_mul_of_nonneg_right hD' (le_of_lt hE))
    nlinarith [h2, hΘ]
  linarith [h1]

/-- (b) The `log(2D)` term: `N·m·log(2D) ≤ η^{2^{m-1}}·θ·D/8`. -/
lemma mrnum_logD {n : ℕ} {ε S θ MΛ C D : ℝ} {m : ℕ}
    (hε : 0 < ε) (hS : 0 < S) (hθ : 0 < θ) (hn : 1 ≤ n) (hm : 1 ≤ m) (hD0 : 0 < D)
    (hD : mrA n ε S θ MΛ C m / (1 + mrTheta n ε S) ≤ D) :
    (n : ℝ) * (m : ℝ) * Real.log (2 * D) ≤ mrEta n ε S ^ (2 ^ (m - 1)) * θ * D / 8 := by
  have hE : (0:ℝ) < mrEta n ε S ^ (2 ^ (m - 1)) * θ :=
    mul_pos (pow_pos (mrEta_pos hε hS) _) hθ
  have hΘ : (0:ℝ) < 1 + mrTheta n ε S := by
    have := mrTheta_pos (n := n) hε hS; linarith
  have hn0 : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
  have hm0 : (0:ℝ) < (m:ℝ) := by exact_mod_cast hm
  have hnm : (0:ℝ) < (n:ℝ) * (m:ℝ) := mul_pos hn0 hm0
  have hA5 := le_mrA_5 (n := n) (ε := ε) (S := S) (θ := θ) (MΛ := MΛ) (C := C) (m := m)
  rw [div_le_iff₀ (pow_pos hE 2)] at hA5
  have hD' : mrA n ε S θ MΛ C m ≤ D * (1 + mrTheta n ε S) := by
    have := (div_le_iff₀ hΘ).mp hD
    linarith [this]
  have hDthr : 512 * (n:ℝ)^2 * (m:ℝ)^2 / (mrEta n ε S ^ (2 ^ (m-1)) * θ)^2 ≤ D := by
    have h2 : (1 + mrTheta n ε S) * (512 * (n:ℝ)^2 * (m:ℝ)^2)
        ≤ D * (1 + mrTheta n ε S) * (mrEta n ε S ^ (2 ^ (m-1)) * θ)^2 :=
      le_trans (by linarith [hA5] : (1 + mrTheta n ε S) * (512 * (n:ℝ)^2 * (m:ℝ)^2)
        ≤ mrA n ε S θ MΛ C m * (mrEta n ε S ^ (2 ^ (m-1)) * θ)^2)
        (mul_le_mul_of_nonneg_right hD' (le_of_lt (pow_pos hE 2)))
    rw [div_le_iff₀ (pow_pos hE 2)]
    have h5 : (1 + mrTheta n ε S) * (512 * (n:ℝ)^2 * (m:ℝ)^2)
        ≤ (1 + mrTheta n ε S) * (D * (mrEta n ε S ^ (2 ^ (m-1)) * θ)^2) := by
      nlinarith [h2]
    exact le_of_mul_le_mul_left h5 hΘ
  set c : ℝ := mrEta n ε S ^ (2 ^ (m - 1)) * θ / (8 * ((n:ℝ) * (m:ℝ))) with hcdef
  have hcpos : 0 < c := by rw [hcdef]; positivity
  have h8c : 8 / c ^ 2 ≤ D := by
    have heq : 8 / c ^ 2 = 512 * (n:ℝ)^2 * (m:ℝ)^2 / (mrEta n ε S ^ (2^(m-1)) * θ)^2 := by
      rw [hcdef]
      field_simp
      ring
    rw [heq]
    exact hDthr
  have hlog := Commons.Analysis.Real.log_two_mul_le_mul_of_ge hD0 hcpos h8c
  have hfin : (n:ℝ) * (m:ℝ) * (c * D) = mrEta n ε S ^ (2 ^ (m-1)) * θ * D / 8 := by
    rw [hcdef]; field_simp
  have h3 := mul_le_mul_of_nonneg_left hlog (le_of_lt hnm)
  linarith [h3, hfin]

/-- (c) The `T`-term: `T·(log (C·MΛ) + 100 m) ≤ η^{2^{m-1}}·θ·D/2`. -/
lemma mrnum_T {n : ℕ} {ε S θ MΛ C D T : ℝ} {m : ℕ}
    (hε : 0 < ε) (hS : 0 < S) (hθ : 0 < θ) (hC1 : 1 ≤ C) (hM1 : 1 ≤ MΛ)
    (hD0 : 0 < D)
    (hD : mrA n ε S θ MΛ C m / (1 + mrTheta n ε S) ≤ D)
    (hA0 : 0 < mrA n ε S θ MΛ C m)
    (hT : T ≤ 2 * (1 + mrTheta n ε S) * D / mrA n ε S θ MΛ C m) :
    T * (Real.log (C * MΛ) + 100 * (m:ℝ)) ≤ mrEta n ε S ^ (2 ^ (m - 1)) * θ * D / 2 := by
  have hE : (0:ℝ) < mrEta n ε S ^ (2 ^ (m - 1)) * θ :=
    mul_pos (pow_pos (mrEta_pos hε hS) _) hθ
  have hΘ : (0:ℝ) < 1 + mrTheta n ε S := by
    have := mrTheta_pos (n := n) hε hS; linarith
  have hA2 := le_mrA_2 (n := n) (ε := ε) (S := S) (θ := θ) (MΛ := MΛ) (C := C) (m := m)
  have hA3 := le_mrA_3 (n := n) (ε := ε) (S := S) (θ := θ) (MΛ := MΛ) (C := C) (m := m)
  rw [div_le_iff₀ hE] at hA2 hA3
  have hlogCM : 0 ≤ Real.log (C * MΛ) :=
    Real.log_nonneg (one_le_mul_of_one_le_of_one_le hC1 hM1)
  have hm0 : (0:ℝ) ≤ (m:ℝ) := by positivity
  have hkey : (Real.log (C * MΛ) + 100 * (m:ℝ)) * (8 * (1 + mrTheta n ε S))
      ≤ 2 * ((mrEta n ε S ^ (2^(m-1)) * θ) * mrA n ε S θ MΛ C m) := by
    nlinarith [hA2, hA3, hlogCM, hm0]
  have hsum : 0 ≤ Real.log (C * MΛ) + 100 * (m:ℝ) := by linarith
  have hT' : T * (Real.log (C*MΛ) + 100*(m:ℝ))
      ≤ (2 * (1 + mrTheta n ε S) * D / mrA n ε S θ MΛ C m)
        * (Real.log (C*MΛ) + 100*(m:ℝ)) :=
    mul_le_mul_of_nonneg_right hT hsum
  have h2 : (2*(1+mrTheta n ε S)*D / mrA n ε S θ MΛ C m) * (Real.log (C*MΛ) + 100*(m:ℝ))
      ≤ mrEta n ε S ^ (2 ^ (m - 1)) * θ * D / 2 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hA0]
    nlinarith [hkey, hD0, hE]
  linarith [hT', h2]

/-- (d1) The `log(2D)` piece of the `hbig` condition (from `mrA` entry 7). -/
lemma mrnum_hbig1 {n : ℕ} {ε S θ MΛ C D : ℝ} {m : ℕ}
    (hn : 1 ≤ n) (hm : 1 ≤ m) (hε : 0 < ε) (hS : 0 < S) (hεS : ε ≤ S) (hθ : 0 < θ)
    (hD0 : 0 < D) (hD : mrA n ε S θ MΛ C m / (1 + mrTheta n ε S) ≤ D) :
    2 * ((n:ℝ)+1) * (2 * ((n:ℝ)+1) + (n:ℝ)) * (m:ℝ) * Real.log (2*D)
      ≤ D * ε * (m:ℝ) / 8 := by
  have hΘ : (0:ℝ) < 1 + mrTheta n ε S := by
    have := mrTheta_pos (n := n) hε hS; linarith
  have hn0 : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
  have hm0 : (0:ℝ) < (m:ℝ) := by exact_mod_cast hm
  have hN0 : (0:ℝ) < (n:ℝ) + 1 := by linarith
  have hQ0 : (0:ℝ) < 2 * ((n:ℝ)+1) + (n:ℝ) := by linarith
  have hD' : mrA n ε S θ MΛ C m ≤ D * (1 + mrTheta n ε S) := by
    have := (div_le_iff₀ hΘ).mp hD
    linarith [this]
  have hA7 := le_mrA_7 (n := n) (ε := ε) (S := S) (θ := θ) (MΛ := MΛ) (C := C) (m := m)
  have hA7' : (1 + mrTheta n ε S) * 2048 * ((n:ℝ)+1)^2 * (2*((n:ℝ)+1) + (n:ℝ))^2
      ≤ mrA n ε S θ MΛ C m * ε^2 := by
    rw [div_le_iff₀ (by positivity : (0:ℝ) < ε^2)] at hA7
    linarith [hA7]
  have hDthr : 2048 * ((n:ℝ)+1)^2 * (2*((n:ℝ)+1) + (n:ℝ))^2 / ε^2 ≤ D := by
    rw [div_le_iff₀ (by positivity : (0:ℝ) < ε^2)]
    have h5 : (1 + mrTheta n ε S) * (2048 * ((n:ℝ)+1)^2 * (2*((n:ℝ)+1) + (n:ℝ))^2)
        ≤ (1 + mrTheta n ε S) * (D * ε^2) := by nlinarith [hA7', hD']
    exact le_of_mul_le_mul_left h5 hΘ
  set c : ℝ := ε / (16 * ((n:ℝ)+1) * (2*((n:ℝ)+1) + (n:ℝ))) with hcdef
  have hcpos : 0 < c := by rw [hcdef]; positivity
  have h8c : 8 / c ^ 2 ≤ D := by
    have heq : 8 / c ^ 2
        = 2048 * ((n:ℝ)+1)^2 * (2*((n:ℝ)+1) + (n:ℝ))^2 / ε^2 := by
      rw [hcdef]
      field_simp
      ring
    rw [heq]; exact hDthr
  have hlog := Commons.Analysis.Real.log_two_mul_le_mul_of_ge hD0 hcpos h8c
  have hfin : 2 * ((n:ℝ)+1) * (2*((n:ℝ)+1) + (n:ℝ)) * (m:ℝ) * (c * D)
      = D * ε * (m:ℝ) / 8 := by
    rw [hcdef]; field_simp; ring
  have h3 := mul_le_mul_of_nonneg_left hlog (by positivity : (0:ℝ) ≤ 2 * ((n:ℝ)+1) * (2*((n:ℝ)+1) + (n:ℝ)) * (m:ℝ))
  linarith [h3, hfin]

/-- (d2) The `log C` piece of the `hbig` condition (from `mrA` entry 6). -/
lemma mrnum_hbig2 {n : ℕ} {ε S θ MΛ C D : ℝ} {m : ℕ}
    (hn : 1 ≤ n) (hm : 1 ≤ m) (hε : 0 < ε) (hS : 0 < S) (hεS : ε ≤ S) (hθ : 0 < θ)
    (hC1 : 1 ≤ C) (hD : 0 < D) (hD' : mrA n ε S θ MΛ C m / (1 + mrTheta n ε S) ≤ D) :
    2 * ((n:ℝ)+1) * Real.log C ≤ D * ε * (m:ℝ) / 8 := by
  have hΘ : (0:ℝ) < 1 + mrTheta n ε S := by
    have := mrTheta_pos (n := n) hε hS; linarith
  have hm0 : (0:ℝ) < (m:ℝ) := by exact_mod_cast hm
  have hlogC0 : 0 ≤ Real.log C := Real.log_nonneg hC1
  have hDa : mrA n ε S θ MΛ C m ≤ D * (1 + mrTheta n ε S) := by
    have := (div_le_iff₀ hΘ).mp hD'
    linarith [this]
  have hA6 := le_mrA_6 (n := n) (ε := ε) (S := S) (θ := θ) (MΛ := MΛ) (C := C) (m := m)
  rw [div_le_iff₀ (by positivity : (0:ℝ) < ε * (m:ℝ))] at hA6
  have hkey : (1 + mrTheta n ε S) * (16 * ((n:ℝ)+1) * Real.log C)
      ≤ D * (1 + mrTheta n ε S) * (ε * (m:ℝ)) :=
    le_trans (by linarith [hA6] : (1 + mrTheta n ε S) * (16 * ((n:ℝ)+1) * Real.log C)
      ≤ mrA n ε S θ MΛ C m * (ε * (m:ℝ)))
      (mul_le_mul_of_nonneg_right hDa (by positivity))
  have h16 : 16 * ((n:ℝ)+1) * Real.log C ≤ D * (ε * (m:ℝ)) :=
    le_of_mul_le_mul_left (by nlinarith [hkey] :
      (1 + mrTheta n ε S) * (16 * ((n:ℝ)+1) * Real.log C)
        ≤ (1 + mrTheta n ε S) * (D * (ε * (m:ℝ)))) hΘ
  linarith [h16]

/-- (d3) The Siegel-term piece of the `hbig` condition (from `mrA` entry 8). -/
lemma mrnum_hbig3 {n : ℕ} {ε S θ MΛ C D T : ℝ} {m : ℕ}
    (hn : 1 ≤ n) (hm : 1 ≤ m) (hε : 0 < ε) (hS : 0 < S) (hεS : ε ≤ S) (hθ : 0 < θ)
    (hC1 : 1 ≤ C) (hM1 : 1 ≤ MΛ) (hD0 : 0 < D)
    (hA1 : 1 ≤ mrA n ε S θ MΛ C m)
    (hD : mrA n ε S θ MΛ C m / (1 + mrTheta n ε S) ≤ D)
    (hT : T ≤ 2 * (1 + mrTheta n ε S) * D / mrA n ε S θ MΛ C m)
    (hT0 : 0 ≤ T) :
    2 * ((n:ℝ)+1) * (T * (Real.log (C * MΛ) + ((n:ℝ)+1) * Real.log 2
        + Real.log (((n:ℝ)+1) * MΛ + 1) + Real.log ((n:ℝ) * (mrB n ε S : ℝ) + 1)))
      ≤ D * ε * (m:ℝ) / 8 := by
  have hΘ : (0:ℝ) < 1 + mrTheta n ε S := by
    have := mrTheta_pos (n := n) hε hS; linarith
  have hm0 : (0:ℝ) < (m:ℝ) := by exact_mod_cast hm
  have hA0 : 0 < mrA n ε S θ MΛ C m := lt_of_lt_of_le zero_lt_one hA1
  have hN0 : (0:ℝ) < (n:ℝ) + 1 := by
    have hn0 : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
    linarith
  have hlogCM : 0 ≤ Real.log (C * MΛ) :=
    Real.log_nonneg (one_le_mul_of_one_le_of_one_le hC1 hM1)
  have hP0 : 0 ≤ Real.log (C * MΛ) + ((n:ℝ)+1) * Real.log 2
      + Real.log (((n:ℝ)+1) * MΛ + 1) + Real.log ((n:ℝ) * (mrB n ε S : ℝ) + 1) := by
    have h1 : 0 ≤ ((n:ℝ)+1) * Real.log 2 := by
      apply mul_nonneg (by linarith) (Real.log_nonneg (by norm_num))
    have h2 : 0 ≤ Real.log (((n:ℝ)+1) * MΛ + 1) := Real.log_nonneg (by nlinarith [hM1])
    have h3 : 0 ≤ Real.log ((n:ℝ) * (mrB n ε S : ℝ) + 1) := by
      apply Real.log_nonneg
      have hh : (0:ℝ) ≤ (n:ℝ) * (mrB n ε S : ℝ) := by positivity
      linarith
    linarith
  have hA8 := le_mrA_8 (n := n) (ε := ε) (S := S) (θ := θ) (MΛ := MΛ) (C := C) (m := m)
  rw [div_le_iff₀ (by positivity : (0:ℝ) < ε * (m:ℝ))] at hA8
  have hP32 : 32 * ((n:ℝ)+1) * (1 + mrTheta n ε S)
      * (Real.log (C * MΛ) + ((n:ℝ)+1) * Real.log 2 + Real.log (((n:ℝ)+1) * MΛ + 1)
        + Real.log ((n:ℝ) * (mrB n ε S : ℝ) + 1))
      ≤ mrA n ε S θ MΛ C m * (ε * (m:ℝ)) := by
    linarith [hA8]
  have hstep : T * (Real.log (C * MΛ) + ((n:ℝ)+1) * Real.log 2
      + Real.log (((n:ℝ)+1) * MΛ + 1) + Real.log ((n:ℝ) * (mrB n ε S : ℝ) + 1))
      ≤ D * ε * (m:ℝ) / (16 * ((n:ℝ)+1)) := by
    have h1 : T * (Real.log (C * MΛ) + ((n:ℝ)+1) * Real.log 2
        + Real.log (((n:ℝ)+1) * MΛ + 1) + Real.log ((n:ℝ) * (mrB n ε S : ℝ) + 1))
        ≤ (2 * (1 + mrTheta n ε S) * D / mrA n ε S θ MΛ C m)
          * (Real.log (C * MΛ) + ((n:ℝ)+1) * Real.log 2
            + Real.log (((n:ℝ)+1) * MΛ + 1) + Real.log ((n:ℝ) * (mrB n ε S : ℝ) + 1)) :=
      mul_le_mul_of_nonneg_right hT hP0
    have h2 : (2 * (1 + mrTheta n ε S) * D / mrA n ε S θ MΛ C m)
        * (Real.log (C * MΛ) + ((n:ℝ)+1) * Real.log 2
          + Real.log (((n:ℝ)+1) * MΛ + 1) + Real.log ((n:ℝ) * (mrB n ε S : ℝ) + 1))
        ≤ D * ε * (m:ℝ) / (16 * ((n:ℝ)+1)) := by
      have hN16 : (0:ℝ) < 16 * ((n:ℝ)+1) := by positivity
      rw [div_mul_eq_mul_div, div_le_iff₀ hA0]
      rw [show D * ε * (m:ℝ) / (16 * ((n:ℝ)+1)) * mrA n ε S θ MΛ C m
          = D * ε * (m:ℝ) * mrA n ε S θ MΛ C m / (16 * ((n:ℝ)+1)) by ring]
      rw [le_div_iff₀ hN16]
      have hmul := mul_le_mul_of_nonneg_left hP32 (le_of_lt hD0)
      nlinarith [hmul]
    linarith [h1, h2]
  have hfin : 2 * ((n:ℝ)+1) * (D * ε * (m:ℝ) / (16 * ((n:ℝ)+1))) = D * ε * (m:ℝ) / 8 := by
    field_simp; ring
  have := mul_le_mul_of_nonneg_left hstep (by positivity : (0:ℝ) ≤ 2 * ((n:ℝ)+1))
  linarith [this, hfin]

/-- (d) The `hbig` hypothesis of the `A`-bounds, assembled from `mrnum_hbig1/2/3`. -/
lemma mrnum_hbig {n : ℕ} {ε S θ MΛ C D Lc Lb Lp T : ℝ} {m : ℕ}
    (hn : 1 ≤ n) (hm : 1 ≤ m) (hε : 0 < ε) (hS : 0 < S) (hεS : ε ≤ S) (hθ : 0 < θ)
    (hC1 : 1 ≤ C) (hM1 : 1 ≤ MΛ) (hD0 : 0 < D) (hA1 : 1 ≤ mrA n ε S θ MΛ C m)
    (hD : mrA n ε S θ MΛ C m / (1 + mrTheta n ε S) ≤ D)
    (hLc : Lc ≤ ((n:ℝ)+1) * (m:ℝ) * Real.log (2*D))
    (hLb : Lb ≤ Real.log C + (n:ℝ) * (m:ℝ) * Real.log (2*D) + T * Real.log (C*MΛ))
    (hLp : Lp ≤ ((n:ℝ)+1) * (m:ℝ) * Real.log (2*D))
    (hT : T ≤ 2 * (1 + mrTheta n ε S) * D / mrA n ε S θ MΛ C m)
    (hT0 : 0 ≤ T) :
    2 * ((n:ℝ)+1) * (Lc + Lb + T * (((n:ℝ)+1) * Real.log 2) + Lp
        + T * Real.log (((n:ℝ)+1) * MΛ + 1) + T * Real.log ((n:ℝ) * (mrB n ε S : ℝ) + 1))
      < D * ε * (m:ℝ) := by
  have hN0 : (0:ℝ) < (n:ℝ) + 1 := by
    have hn0 : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
    linarith
  have h2N : (0:ℝ) ≤ 2 * ((n:ℝ)+1) := by positivity
  have hm0 : (0:ℝ) < (m:ℝ) := by exact_mod_cast hm
  have hsum1 : Lc + Lb + Lp ≤ (2 * ((n:ℝ)+1) + (n:ℝ)) * (m:ℝ) * Real.log (2*D)
      + Real.log C + T * Real.log (C*MΛ) := by linarith [hLc, hLb, hLp]
  have htot : 2 * ((n:ℝ)+1) * (Lc + Lb + T * (((n:ℝ)+1) * Real.log 2) + Lp
      + T * Real.log (((n:ℝ)+1) * MΛ + 1) + T * Real.log ((n:ℝ) * (mrB n ε S : ℝ) + 1))
      ≤ 2 * ((n:ℝ)+1) * ((2 * ((n:ℝ)+1) + (n:ℝ)) * (m:ℝ) * Real.log (2*D)
          + Real.log C + T * (Real.log (C*MΛ) + ((n:ℝ)+1) * Real.log 2
            + Real.log (((n:ℝ)+1) * MΛ + 1) + Real.log ((n:ℝ) * (mrB n ε S : ℝ) + 1))) := by
    have := mul_le_mul_of_nonneg_left hsum1 h2N
    nlinarith [this]
  have h3 : 2 * ((n:ℝ)+1) * ((2 * ((n:ℝ)+1) + (n:ℝ)) * (m:ℝ) * Real.log (2*D))
      ≤ D * ε * (m:ℝ) / 8 := by
    have h := mrnum_hbig1 (n := n) (ε := ε) (S := S) (θ := θ) (MΛ := MΛ) (C := C) (D := D)
      (m := m) hn hm hε hS hεS hθ hD0 hD
    nlinarith [h]
  have h4 : 2 * ((n:ℝ)+1) * Real.log C ≤ D * ε * (m:ℝ) / 8 :=
    mrnum_hbig2 (n := n) (ε := ε) (S := S) (θ := θ) (MΛ := MΛ) (C := C) (D := D) (m := m)
      hn hm hε hS hεS hθ hC1 hD0 hD
  have h5 : 2 * ((n:ℝ)+1) * (T * (Real.log (C*MΛ) + ((n:ℝ)+1) * Real.log 2
      + Real.log (((n:ℝ)+1) * MΛ + 1) + Real.log ((n:ℝ) * (mrB n ε S : ℝ) + 1)))
      ≤ D * ε * (m:ℝ) / 8 :=
    mrnum_hbig3 (n := n) (ε := ε) (S := S) (θ := θ) (MΛ := MΛ) (C := C) (D := D) (T := T)
      (m := m) hn hm hε hS hεS hθ hC1 hM1 hD0 hA1 hD hT hT0
  have htot2 : 2 * ((n:ℝ)+1) * ((2 * ((n:ℝ)+1) + (n:ℝ)) * (m:ℝ) * Real.log (2*D)
      + Real.log C + T * (Real.log (C*MΛ) + ((n:ℝ)+1) * Real.log 2
        + Real.log (((n:ℝ)+1) * MΛ + 1) + Real.log ((n:ℝ) * (mrB n ε S : ℝ) + 1)))
      ≤ D * ε * (m:ℝ) * 3 / 8 := by
    have hdist : 2 * ((n:ℝ)+1) * ((2 * ((n:ℝ)+1) + (n:ℝ)) * (m:ℝ) * Real.log (2*D)
        + Real.log C + T * (Real.log (C*MΛ) + ((n:ℝ)+1) * Real.log 2
          + Real.log (((n:ℝ)+1) * MΛ + 1) + Real.log ((n:ℝ) * (mrB n ε S : ℝ) + 1)))
        = 2 * ((n:ℝ)+1) * ((2 * ((n:ℝ)+1) + (n:ℝ)) * (m:ℝ) * Real.log (2*D))
          + 2 * ((n:ℝ)+1) * Real.log C
          + 2 * ((n:ℝ)+1) * (T * (Real.log (C*MΛ) + ((n:ℝ)+1) * Real.log 2
            + Real.log (((n:ℝ)+1) * MΛ + 1) + Real.log ((n:ℝ) * (mrB n ε S : ℝ) + 1))) := by
      ring
    rw [hdist]; linarith [h3, h4, h5]
  have hpos : (0:ℝ) < D * ε * (m:ℝ) := by positivity
  linarith [htot, htot2, hpos]

end Submission.Subspace
