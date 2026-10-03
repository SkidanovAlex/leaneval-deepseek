import Mathlib
import Submission.Work.FIArea2.R6.Aggregate6

namespace Work.FIArea2.R6

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## 2. The geometric/arithmetic step of `NOTES.md` §24.4 -/

lemma Params_vartheta_le_one' (Pa : Work.FITop.Params) : Pa.ϑ ≤ 1 := by
  have hx3 : (3 : ℝ) ≤ (Pa.x : ℝ) := by exact_mod_cast Pa.hx
  have hlog1 : (1 : ℝ) ≤ Real.log (Pa.x : ℝ) := by
    have hexp : Real.exp 1 ≤ (Pa.x : ℝ) := by
      have := Real.exp_one_lt_three; linarith
    have := Real.log_le_log (Real.exp_pos 1) hexp
    rwa [Real.log_exp] at this
  rw [Pa.hϑ]
  exact Real.rpow_le_one_of_one_le_of_nonpos hlog1 (by linarith [Pa.hA])

lemma Hscale_ge_one (Pa : Work.FITop.Params) : 1 ≤ Work.FIPlan.Hscale Pa.M Pa.N := by
  have hb := (Hscale_bounds Pa).1
  have hx3 : (3 : ℝ) ≤ (Pa.x : ℝ) := by exact_mod_cast Pa.hx
  have hx1 : (1 : ℝ) < (Pa.x : ℝ) := by linarith
  have hxη : (1 : ℝ) < (Pa.x : ℝ) ^ Pa.η := Real.one_lt_rpow hx1 Pa.hη
  linarith

/-- The elementary bound `log 6 ≤ 2`, i.e. `6 ≤ exp 2 = (exp 1)²` with `exp 1 > 2.718…`. -/
lemma log_six_le_two : Real.log 6 ≤ (2 : ℝ) := by
  rw [Real.log_le_iff_le_exp (by norm_num)]
  have h : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
    rw [show (2:ℝ) = 1 + 1 by norm_num, Real.exp_add]
  rw [h]
  have h1 : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  have h2 : (2.7182818283 : ℝ) * 2.7182818283 ≤ Real.exp 1 * Real.exp 1 :=
    mul_le_mul h1.le h1.le (by norm_num) (by positivity)
  nlinarith [h2]

/-- The geometric factor of the §9 aggregate: `(H²+1)(2R+1)²(log(H+R+2))^K ≤ 128·3^K·N²(log N+2)^K`
(by `H ≤ √N`, `2R+1 ≤ 8√N` and `H+R+2 ≤ 6(N+2)`), and `ϑ^{-1/2}(log N+2)^8 ≤ ϑ^{-1}(log N+2)^8`. -/
lemma sec9_geom_le (Pa : Work.FITop.Params) (K : ℕ) :
    Pa.ϑ ^ (-(1 : ℝ) / 2) * (Real.log Pa.N + 2) ^ (8 : ℕ)
        * ((Work.FIPlan.Hscale Pa.M Pa.N ^ 2 + 1)
            * (2 * (((Work.FITop.radN Pa).toNat : ℕ) : ℝ) + 1) ^ 2
            * (Real.log (Work.FIPlan.Hscale Pa.M Pa.N
                + (((Work.FITop.radN Pa).toNat : ℕ) : ℝ) + 2)) ^ K)
      ≤ 128 * 3 ^ K * Pa.ϑ⁻¹ * Pa.N ^ 2 * (Real.log Pa.N + 2) ^ (8 + K) := by
  have hN1 : (1 : ℝ) ≤ Pa.N := Pa.hN1
  have hN0 : (0 : ℝ) < Pa.N := by linarith
  have hϑ0 : 0 < Pa.ϑ := Pa.hϑ0
  have hϑ1 : Pa.ϑ ≤ 1 := Params_vartheta_le_one' Pa
  have hlogN0 : (0 : ℝ) ≤ Real.log Pa.N := Real.log_nonneg hN1
  have hL0 : (0 : ℝ) ≤ Real.log Pa.N + 2 := by linarith
  have hHle : Work.FIPlan.Hscale Pa.M Pa.N ≤ Real.sqrt Pa.N := (Hscale_bounds Pa).2
  have hH1 : 1 ≤ Work.FIPlan.Hscale Pa.M Pa.N := Hscale_ge_one Pa
  have hHpos : 0 < Work.FIPlan.Hscale Pa.M Pa.N := by linarith
  -- the `(u₁,u₂)`-bound `(2R+1)² ≤ 64N`
  have hRnat : ((((Work.FITop.radN Pa).toNat : ℕ)) : ℤ) = Work.FITop.radN Pa :=
    Int.toNat_of_nonneg (Work.FIArea2.Count.radN_nonneg Pa)
  have hR : 2 * (((Work.FITop.radN Pa).toNat : ℕ) : ℝ) + 1 ≤ 8 * Real.sqrt Pa.N := by
    have h := Work.FIArea2.Count.radN_bound Pa
    rw [← hRnat] at h
    push_cast at h
    linarith [h]
  have hRnn : (0 : ℝ) ≤ 2 * (((Work.FITop.radN Pa).toNat : ℕ) : ℝ) + 1 := by positivity
  have hR2 : (2 * (((Work.FITop.radN Pa).toNat : ℕ) : ℝ) + 1) ^ 2 ≤ 64 * Pa.N := by
    have h8 : (0 : ℝ) ≤ 8 * Real.sqrt Pa.N := by positivity
    have hsq : (8 * Real.sqrt Pa.N) ^ 2 = 64 * Pa.N := by
      rw [mul_pow, Real.sq_sqrt hN0.le]; ring
    calc (2 * (((Work.FITop.radN Pa).toNat : ℕ) : ℝ) + 1) ^ 2
        ≤ (8 * Real.sqrt Pa.N) ^ 2 := pow_le_pow_left₀ hRnn hR 2
      _ = 64 * Pa.N := hsq
  -- `H² ≤ N`, hence `(H²+1) ≤ 2N`
  have hH2 : Work.FIPlan.Hscale Pa.M Pa.N ^ 2 ≤ Pa.N := by
    have h2 : Real.sqrt Pa.N ^ 2 = Pa.N := Real.sq_sqrt hN0.le
    calc Work.FIPlan.Hscale Pa.M Pa.N ^ 2 ≤ Real.sqrt Pa.N ^ 2 :=
          pow_le_pow_left₀ hHpos.le hHle 2
      _ = Pa.N := h2
  have hH21 : Work.FIPlan.Hscale Pa.M Pa.N ^ 2 + 1 ≤ 2 * Pa.N := by linarith
  have hprod : (Work.FIPlan.Hscale Pa.M Pa.N ^ 2 + 1)
        * (2 * (((Work.FITop.radN Pa).toNat : ℕ) : ℝ) + 1) ^ 2 ≤ 128 * Pa.N ^ 2 := by
    have h2 : (0 : ℝ) ≤ (2 * (((Work.FITop.radN Pa).toNat : ℕ) : ℝ) + 1) ^ 2 := by positivity
    calc (Work.FIPlan.Hscale Pa.M Pa.N ^ 2 + 1)
          * (2 * (((Work.FITop.radN Pa).toNat : ℕ) : ℝ) + 1) ^ 2
        ≤ (2 * Pa.N) * (64 * Pa.N) := mul_le_mul hH21 hR2 h2 (by positivity)
      _ = 128 * Pa.N ^ 2 := by ring
  -- the logarithm: `H + R + 2 ≤ 6(N+2)` and `log 6 ≤ 2`, `log(N+2) ≤ log N + 2`
  have hRle : (((Work.FITop.radN Pa).toNat : ℕ) : ℝ) ≤ 4 * Real.sqrt Pa.N := by linarith
  have hHR : Work.FIPlan.Hscale Pa.M Pa.N + (((Work.FITop.radN Pa).toNat : ℕ) : ℝ) + 2
      ≤ 6 * (Pa.N + 2) := by
    have h1 : Real.sqrt Pa.N ≤ Pa.N := by
      calc Real.sqrt Pa.N ≤ Real.sqrt (Pa.N ^ 2) := Real.sqrt_le_sqrt (by nlinarith [hN1])
        _ = Pa.N := Real.sqrt_sq (by linarith)
    have h2 : 4 * Real.sqrt Pa.N ≤ 4 * (Pa.N + 2) := by linarith
    linarith
  have hHRpos : 0 < Work.FIPlan.Hscale Pa.M Pa.N
      + (((Work.FITop.radN Pa).toNat : ℕ) : ℝ) + 2 := by positivity
  have hlogN2 : Real.log (Pa.N + 2) ≤ Real.log Pa.N + 2 := by
    have h4 : Pa.N + 2 ≤ 3 * Pa.N := by linarith
    have h5 : Real.log (Pa.N + 2) ≤ Real.log (3 * Pa.N) :=
      Real.log_le_log (by linarith) h4
    rw [Real.log_mul (by norm_num) hN0.ne'] at h5
    have h6 : Real.log 3 ≤ (2 : ℝ) :=
      le_trans (Real.log_le_log (by norm_num) (by norm_num : (3:ℝ) ≤ 6)) log_six_le_two
    linarith [h5, h6]
  have hlog : Real.log (Work.FIPlan.Hscale Pa.M Pa.N
        + (((Work.FITop.radN Pa).toNat : ℕ) : ℝ) + 2) ≤ 3 * (Real.log Pa.N + 2) := by
    calc Real.log (Work.FIPlan.Hscale Pa.M Pa.N
            + (((Work.FITop.radN Pa).toNat : ℕ) : ℝ) + 2)
        ≤ Real.log (6 * (Pa.N + 2)) := Real.log_le_log hHRpos hHR
      _ = Real.log 6 + Real.log (Pa.N + 2) := by
          rw [Real.log_mul (by norm_num) (by linarith)]
      _ ≤ 2 + (Real.log Pa.N + 2) := add_le_add log_six_le_two hlogN2
      _ ≤ 3 * (Real.log Pa.N + 2) := by linarith [hlogN0]
  have hlogK : (Real.log (Work.FIPlan.Hscale Pa.M Pa.N
        + (((Work.FITop.radN Pa).toNat : ℕ) : ℝ) + 2)) ^ K
      ≤ (3 * (Real.log Pa.N + 2)) ^ K :=
    pow_le_pow_left₀ (Real.log_nonneg (by linarith)) hlog K
  have hmain : (Work.FIPlan.Hscale Pa.M Pa.N ^ 2 + 1)
        * (2 * (((Work.FITop.radN Pa).toNat : ℕ) : ℝ) + 1) ^ 2
        * (Real.log (Work.FIPlan.Hscale Pa.M Pa.N
            + (((Work.FITop.radN Pa).toNat : ℕ) : ℝ) + 2)) ^ K
      ≤ 128 * Pa.N ^ 2 * (3 * (Real.log Pa.N + 2)) ^ K := by
    have hnn : 0 ≤ (Real.log (Work.FIPlan.Hscale Pa.M Pa.N
        + (((Work.FITop.radN Pa).toNat : ℕ) : ℝ) + 2)) ^ K :=
      pow_nonneg (Real.log_nonneg (by linarith)) K
    have h128 : 0 ≤ 128 * Pa.N ^ 2 := by nlinarith [sq_nonneg Pa.N]
    exact mul_le_mul hprod hlogK hnn h128
  -- `ϑ^{-1/2} ≤ ϑ^{-1}`
  have hϑpow : Pa.ϑ ^ (-(1 : ℝ) / 2) ≤ Pa.ϑ⁻¹ := by
    have hb : Pa.ϑ ≤ Pa.ϑ ^ ((1 : ℝ) / 2) := by
      have h2 : Pa.ϑ = Pa.ϑ ^ ((1 : ℝ) / 2) * Pa.ϑ ^ ((1 : ℝ) / 2) := by
        rw [← Real.rpow_add hϑ0]; norm_num
      have h3 : Pa.ϑ ^ ((1 : ℝ) / 2) ≤ 1 := Real.rpow_le_one hϑ0.le hϑ1 (by norm_num)
      nlinarith [Real.rpow_nonneg hϑ0.le ((1:ℝ)/2), h2, h3]
    have h3 : Pa.ϑ ^ (-(1 : ℝ) / 2) = (Pa.ϑ ^ ((1 : ℝ) / 2))⁻¹ := by
      rw [← Real.rpow_neg hϑ0.le]; norm_num
    rw [h3, inv_le_inv₀ (Real.rpow_pos_of_pos hϑ0 _) hϑ0]
    exact hb
  have hA : Pa.ϑ ^ (-(1 : ℝ) / 2) * (Real.log Pa.N + 2) ^ (8 : ℕ)
      ≤ Pa.ϑ⁻¹ * (Real.log Pa.N + 2) ^ (8 : ℕ) :=
    mul_le_mul_of_nonneg_right hϑpow (by positivity)
  have hC : 0 ≤ (Work.FIPlan.Hscale Pa.M Pa.N ^ 2 + 1)
      * (2 * (((Work.FITop.radN Pa).toNat : ℕ) : ℝ) + 1) ^ 2
      * (Real.log (Work.FIPlan.Hscale Pa.M Pa.N
          + (((Work.FITop.radN Pa).toNat : ℕ) : ℝ) + 2)) ^ K := by
    refine mul_nonneg (mul_nonneg ?_ ?_) ?_
    · positivity
    · positivity
    · exact pow_nonneg (Real.log_nonneg (by linarith)) K
  have hB : 0 ≤ Pa.ϑ⁻¹ * (Real.log Pa.N + 2) ^ (8 : ℕ) :=
    mul_nonneg (inv_nonneg.mpr hϑ0.le) (pow_nonneg hL0 8)
  calc Pa.ϑ ^ (-(1 : ℝ) / 2) * (Real.log Pa.N + 2) ^ (8 : ℕ)
        * ((Work.FIPlan.Hscale Pa.M Pa.N ^ 2 + 1)
            * (2 * (((Work.FITop.radN Pa).toNat : ℕ) : ℝ) + 1) ^ 2
            * (Real.log (Work.FIPlan.Hscale Pa.M Pa.N
                + (((Work.FITop.radN Pa).toNat : ℕ) : ℝ) + 2)) ^ K)
      ≤ (Pa.ϑ⁻¹ * (Real.log Pa.N + 2) ^ (8 : ℕ))
          * ((Work.FIPlan.Hscale Pa.M Pa.N ^ 2 + 1)
            * (2 * (((Work.FITop.radN Pa).toNat : ℕ) : ℝ) + 1) ^ 2
            * (Real.log (Work.FIPlan.Hscale Pa.M Pa.N
                + (((Work.FITop.radN Pa).toNat : ℕ) : ℝ) + 2)) ^ K) :=
        mul_le_mul_of_nonneg_right hA hC
    _ ≤ (Pa.ϑ⁻¹ * (Real.log Pa.N + 2) ^ (8 : ℕ))
          * (128 * Pa.N ^ 2 * (3 * (Real.log Pa.N + 2)) ^ K) :=
        mul_le_mul_of_nonneg_left hmain hB
    _ = 128 * 3 ^ K * Pa.ϑ⁻¹ * Pa.N ^ 2 * (Real.log Pa.N + 2) ^ (8 + K) := by
        rw [mul_pow, pow_add]; ring

lemma Params_tau_nonneg' (Pa : Work.FITop.Params) : 0 ≤ Pa.τ := by
  have hx3 : (3 : ℝ) ≤ (Pa.x : ℝ) := by exact_mod_cast Pa.hx
  have hlog : (0 : ℝ) ≤ Real.log (Pa.x : ℝ) := Real.log_nonneg (by linarith)
  have h2 : (0 : ℝ) ≤ (Real.log (Pa.x : ℝ)) ^ (Pa.A + 124) := by positivity
  linarith [Pa.hτ1]

end

end Work.FIArea2.R6
