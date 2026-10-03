import Mathlib
import Submission.Work.FIArea2.R6.Area6eDefs
import Submission.Work.FIArea2.R6.Assembly6

namespace Work.FIArea2.R6

open scoped BigOperators

/-- For `N ≥ 8`, `log N ≥ 2`. -/
lemma log_N_ge_two (Pa : Work.FITop.Params) (hN8 : 8 ≤ Pa.N) : (2 : ℝ) ≤ Real.log Pa.N := by
  have h8 : Real.log 8 ≤ Real.log Pa.N := Real.log_le_log (by norm_num) (by exact_mod_cast hN8)
  have h9 : (2 : ℝ) ≤ Real.log 8 := by
    have hlt : ((2 : ℝ) / 3) < Real.log 2 := by
      have hnum : ((2 : ℝ) / 3) < (6931471803 : ℝ) / 10000000000 := by norm_num
      have hd := Real.log_two_gt_d9
      rw [show (0.6931471803 : ℝ) = (6931471803 : ℝ) / 10000000000 by norm_num] at hd
      exact lt_trans hnum hd
    have h8' : Real.log 8 = 3 * Real.log 2 := by
      rw [show (8 : ℝ) = 2 ^ (3 : ℕ) by norm_num, Real.log_pow]; norm_num
    rw [h8']; linarith
  linarith

/-- `√M · N^{-1/2} = √M / √N`. -/
lemma sqrt_mul_rpow_neg_half (M N : ℝ) (hN : 0 < N) :
    Real.sqrt M * N ^ (-(1 : ℝ) / 2) = Real.sqrt M / Real.sqrt N := by
  have h' : N ^ (-(1 : ℝ) / 2) = (Real.sqrt N)⁻¹ := by
    rw [Real.sqrt_eq_rpow]
    rw [show (-(1 : ℝ) / 2) = -((1 : ℝ) / 2) by norm_num, Real.rpow_neg hN.le]
  rw [h', div_eq_mul_inv]

/-- **The geometric conversion** underlying (9.10):
`√M · N^{-1/2} · (H²+1) · (2R+1)² ≤ 128 N²`, `H = Hscale M N`, `R = radN Pa`.
Direct from `geom_le_six`. -/
lemma sec9geom (Pa : Work.FITop.Params) (hN8 : 8 ≤ Pa.N) :
    Real.sqrt Pa.M * Pa.N ^ (-(1 : ℝ) / 2)
      * ((Work.FIPlan.Hscale Pa.M Pa.N ^ 2 + 1)
          * (2 * (((Work.FITop.radN Pa).toNat : ℕ) : ℝ) + 1) ^ 2) ≤ 128 * Pa.N ^ 2 := by
  have hNpos : (0 : ℝ) < Pa.N := by linarith
  have hN4 : 4 ≤ Pa.N := by linarith
  have h := Work.FIArea2.R6.geom_le_six Pa hN4
  have hs := sqrt_mul_rpow_neg_half Pa.M Pa.N hNpos
  rw [hs]
  calc Real.sqrt Pa.M / Real.sqrt Pa.N
        * ((Work.FIPlan.Hscale Pa.M Pa.N ^ 2 + 1)
            * (2 * (((Work.FITop.radN Pa).toNat : ℕ) : ℝ) + 1) ^ 2)
      = Real.sqrt Pa.M / Real.sqrt Pa.N
        * (Work.FIPlan.Hscale Pa.M Pa.N ^ 2 + 1)
        * (2 * (((Work.FITop.radN Pa).toNat : ℕ) : ℝ) + 1) ^ 2 := by ring
    _ ≤ 128 * Pa.N ^ 2 := h

/-- **The logarithmic conversion** underlying (9.10):
`(log N + 2)·(log(H+R+2))^{8+KL+4} ≤ 2·(log N)^{bFun η}`,
using `KL ≤ 2^{10}`, `N ≥ 8`, `0 < η < 3/32` and `bFun η ≥ 5000`. -/
lemma sec9log (Pa : Work.FITop.Params) (KL : ℕ) (hKL : KL ≤ 2 ^ 10) (hN8 : 8 ≤ Pa.N)
    (hη0 : 0 < Pa.η) (hη32 : Pa.η < 3 / 32) :
    (Real.log Pa.N + 2) * (Real.log (Work.FIPlan.Hscale Pa.M Pa.N
        + (((Work.FITop.radN Pa).toNat : ℕ) : ℝ) + 2)) ^ (8 + KL + 4)
      ≤ 2 * (Real.log Pa.N) ^ (Work.FITop4.bFun Pa.η) := by
  have hNpos : (0 : ℝ) < Pa.N := by linarith
  have hL2 : (2 : ℝ) ≤ Real.log Pa.N := log_N_ge_two Pa hN8
  have hL1 : (1 : ℝ) ≤ Real.log Pa.N := by linarith
  have hLpos : (0 : ℝ) < Real.log Pa.N := by linarith
  have harg1 : (1 : ℝ) ≤ Work.FIPlan.Hscale Pa.M Pa.N
      + (((Work.FITop.radN Pa).toNat : ℕ) : ℝ) + 2 := by
    have hHpos : (0 : ℝ) < Work.FIPlan.Hscale Pa.M Pa.N := by
      rw [Work.FIPlan.Hscale]
      exact mul_pos (Real.rpow_pos_of_pos (by linarith [Pa.hM1]) _) (Real.rpow_pos_of_pos hNpos _)
    have hR : (0 : ℝ) ≤ (((Work.FITop.radN Pa).toNat : ℕ) : ℝ) := by positivity
    linarith
  have hXnn : (0 : ℝ) ≤ (Real.log (Work.FIPlan.Hscale Pa.M Pa.N
      + (((Work.FITop.radN Pa).toNat : ℕ) : ℝ) + 2)) ^ (8 + KL + 4) :=
    pow_nonneg (Real.log_nonneg harg1) _
  have hX : (Real.log (Work.FIPlan.Hscale Pa.M Pa.N
      + (((Work.FITop.radN Pa).toNat : ℕ) : ℝ) + 2)) ^ (8 + KL + 4)
      ≤ (Real.log Pa.N) ^ (2 * (8 + KL + 4)) :=
    Work.FIArea2.R6.log_pow_le_six Pa hN8 (8 + KL + 4)
  have hE' : 2 * (8 + KL + 4) ≤ 2072 := by
    have h1024 : (2 : ℕ) ^ 10 = 1024 := by norm_num
    rw [h1024] at hKL
    omega
  have hb : 1 + ((2 * (8 + KL + 4) : ℕ) : ℝ) ≤ Work.FITop4.bFun Pa.η := by
    have h5000 := Work.FIArea2.R6.bFun_ge_5000 Pa.η hη0 hη32
    have hcast : ((2 * (8 + KL + 4) : ℕ) : ℝ) ≤ 2072 := by exact_mod_cast hE'
    linarith
  have key : (2 * Real.log Pa.N) * (Real.log Pa.N) ^ (2 * (8 + KL + 4))
      = 2 * (Real.log Pa.N) ^ (1 + ((2 * (8 + KL + 4) : ℕ) : ℝ)) := by
    rw [← Real.rpow_natCast (Real.log Pa.N) (2 * (8 + KL + 4))]
    have h2 : (2 : ℝ) * Real.log Pa.N = 2 * (Real.log Pa.N) ^ (1 : ℝ) := by
      rw [Real.rpow_one]
    rw [h2, mul_assoc, ← Real.rpow_add hLpos]
  calc (Real.log Pa.N + 2) * (Real.log (Work.FIPlan.Hscale Pa.M Pa.N
        + (((Work.FITop.radN Pa).toNat : ℕ) : ℝ) + 2)) ^ (8 + KL + 4)
      ≤ (2 * Real.log Pa.N) * (Real.log (Work.FIPlan.Hscale Pa.M Pa.N
        + (((Work.FITop.radN Pa).toNat : ℕ) : ℝ) + 2)) ^ (8 + KL + 4) := by
        apply mul_le_mul_of_nonneg_right _ hXnn
        linarith
    _ ≤ (2 * Real.log Pa.N) * (Real.log Pa.N) ^ (2 * (8 + KL + 4)) :=
        mul_le_mul_of_nonneg_left hX (by linarith)
    _ = 2 * (Real.log Pa.N) ^ (1 + ((2 * (8 + KL + 4) : ℕ) : ℝ)) := key
    _ ≤ 2 * (Real.log Pa.N) ^ (Work.FITop4.bFun Pa.η) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact Real.rpow_le_rpow_of_exponent_le hL1 hb

theorem sec9ErrSum6_arith (Pa : Work.FITop.Params) (CZ CL C : ℝ) (KL : ℕ)
    (hCZ : 0 < CZ) (hCL : 0 < CL) (hC : 0 < C) (hKL : KL ≤ 2 ^ 10) (hN8 : 8 ≤ Pa.N)
    (hη0 : 0 < Pa.η) (hη32 : Pa.η < 3 / 32) {β : GaussianInt → ℂ}
    (hErr : Work.FIArea2.R6.sec9ErrSum6 Pa β
      ≤ Real.sqrt Pa.M * (256 * (Real.log Pa.N + 2) * Pa.N ^ (-(1 : ℝ) / 2))
          * Work.FIArea2.R6.sec9Psum6 Pa β)
    (hPsum : Work.FIArea2.R6.sec9Psum6 Pa β
      ≤ C * (CZ * CL) * Pa.ϑ⁻¹ * Pa.τ ^ (2 : ℕ)
          * ((Work.FIPlan.Hscale Pa.M Pa.N ^ 2 + 1)
              * (2 * (((Work.FITop.radN Pa).toNat : ℕ) : ℝ) + 1) ^ 2)
          * (Real.log (Work.FIPlan.Hscale Pa.M Pa.N
              + (((Work.FITop.radN Pa).toNat : ℕ) : ℝ) + 2)) ^ (8 + KL + 4)) :
    Work.FIArea2.R6.sec9ErrSum6 Pa β
      ≤ 256 * 128 * 2 * C * CZ * CL * Pa.ϑ⁻¹ * Pa.τ ^ (2 : ℕ) * Pa.N ^ 2
          * (Real.log Pa.N) ^ (Work.FITop4.bFun Pa.η) := by
  have hNpos : (0 : ℝ) < Pa.N := by linarith
  have hL2 : (2 : ℝ) ≤ Real.log Pa.N := log_N_ge_two Pa hN8
  -- nonnegativity of the carrier
  have hK1nn : 0 ≤ Real.sqrt Pa.M * (256 * (Real.log Pa.N + 2) * Pa.N ^ (-(1 : ℝ) / 2)) := by
    apply mul_nonneg (Real.sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg (by norm_num) (by linarith)) (Real.rpow_nonneg hNpos.le _)
  have hstep1 : Work.FIArea2.R6.sec9ErrSum6 Pa β ≤
      Real.sqrt Pa.M * (256 * (Real.log Pa.N + 2) * Pa.N ^ (-(1 : ℝ) / 2))
        * (C * (CZ * CL) * Pa.ϑ⁻¹ * Pa.τ ^ (2 : ℕ)
            * ((Work.FIPlan.Hscale Pa.M Pa.N ^ 2 + 1)
                * (2 * (((Work.FITop.radN Pa).toNat : ℕ) : ℝ) + 1) ^ 2)
            * (Real.log (Work.FIPlan.Hscale Pa.M Pa.N
                + (((Work.FITop.radN Pa).toNat : ℕ) : ℝ) + 2)) ^ (8 + KL + 4)) :=
    le_trans hErr (mul_le_mul_of_nonneg_left hPsum hK1nn)
  have hstep2 : Real.sqrt Pa.M * (256 * (Real.log Pa.N + 2) * Pa.N ^ (-(1 : ℝ) / 2))
        * (C * (CZ * CL) * Pa.ϑ⁻¹ * Pa.τ ^ (2 : ℕ)
            * ((Work.FIPlan.Hscale Pa.M Pa.N ^ 2 + 1)
                * (2 * (((Work.FITop.radN Pa).toNat : ℕ) : ℝ) + 1) ^ 2)
            * (Real.log (Work.FIPlan.Hscale Pa.M Pa.N
                + (((Work.FITop.radN Pa).toNat : ℕ) : ℝ) + 2)) ^ (8 + KL + 4))
      ≤ 256 * 128 * 2 * C * CZ * CL * Pa.ϑ⁻¹ * Pa.τ ^ (2 : ℕ) * Pa.N ^ 2
          * (Real.log Pa.N) ^ (Work.FITop4.bFun Pa.η) := by
    have hG := sec9geom Pa hN8
    have hLb : 256 * (Real.log Pa.N + 2)
        * (Real.log (Work.FIPlan.Hscale Pa.M Pa.N
            + (((Work.FITop.radN Pa).toNat : ℕ) : ℝ) + 2)) ^ (8 + KL + 4)
        ≤ 256 * 2 * (Real.log Pa.N) ^ (Work.FITop4.bFun Pa.η) := by
      have hinner := sec9log Pa KL hKL hN8 hη0 hη32
      have hmul := mul_le_mul_of_nonneg_left hinner (by norm_num : (0 : ℝ) ≤ 256)
      calc 256 * (Real.log Pa.N + 2)
            * (Real.log (Work.FIPlan.Hscale Pa.M Pa.N
                + (((Work.FITop.radN Pa).toNat : ℕ) : ℝ) + 2)) ^ (8 + KL + 4)
          = 256 * ((Real.log Pa.N + 2)
              * (Real.log (Work.FIPlan.Hscale Pa.M Pa.N
                  + (((Work.FITop.radN Pa).toNat : ℕ) : ℝ) + 2)) ^ (8 + KL + 4)) := by ring
        _ ≤ 256 * (2 * (Real.log Pa.N) ^ (Work.FITop4.bFun Pa.η)) := hmul
        _ = 256 * 2 * (Real.log Pa.N) ^ (Work.FITop4.bFun Pa.η) := by ring
    have hP3nn : 0 ≤ C * (CZ * CL) * Pa.ϑ⁻¹ * Pa.τ ^ (2 : ℕ) := by
      have h1 : 0 < C * (CZ * CL) := mul_pos hC (mul_pos hCZ hCL)
      have h2 : 0 < Pa.ϑ⁻¹ := inv_pos.mpr Pa.hϑ0
      have h3 : 0 ≤ Pa.τ ^ (2 : ℕ) := by rw [pow_two]; exact mul_self_nonneg Pa.τ
      exact mul_nonneg (mul_nonneg h1.le h2.le) h3
    have hGnn : 0 ≤ 128 * Pa.N ^ 2 := by positivity
    have hcnn : 0 ≤ 256 * (Real.log Pa.N + 2)
        * (Real.log (Work.FIPlan.Hscale Pa.M Pa.N
            + (((Work.FITop.radN Pa).toNat : ℕ) : ℝ) + 2)) ^ (8 + KL + 4) := by
      apply mul_nonneg
      · exact mul_nonneg (by norm_num) (by linarith)
      · exact pow_nonneg (Real.log_nonneg (by
          have hHpos : (0 : ℝ) < Work.FIPlan.Hscale Pa.M Pa.N := by
            rw [Work.FIPlan.Hscale]
            exact mul_pos (Real.rpow_pos_of_pos (by linarith [Pa.hM1]) _)
              (Real.rpow_pos_of_pos hNpos _)
          have hR : (0 : ℝ) ≤ (((Work.FITop.radN Pa).toNat : ℕ) : ℝ) := by positivity
          linarith)) _
    have hAB : (Real.sqrt Pa.M * Pa.N ^ (-(1 : ℝ) / 2)
          * ((Work.FIPlan.Hscale Pa.M Pa.N ^ 2 + 1)
              * (2 * (((Work.FITop.radN Pa).toNat : ℕ) : ℝ) + 1) ^ 2))
        * (256 * (Real.log Pa.N + 2)
            * (Real.log (Work.FIPlan.Hscale Pa.M Pa.N
                + (((Work.FITop.radN Pa).toNat : ℕ) : ℝ) + 2)) ^ (8 + KL + 4))
        ≤ (128 * Pa.N ^ 2)
          * (256 * 2 * (Real.log Pa.N) ^ (Work.FITop4.bFun Pa.η)) :=
      mul_le_mul hG hLb hcnn hGnn
    have hab2 := mul_le_mul_of_nonneg_right hAB hP3nn
    calc Real.sqrt Pa.M * (256 * (Real.log Pa.N + 2) * Pa.N ^ (-(1 : ℝ) / 2))
          * (C * (CZ * CL) * Pa.ϑ⁻¹ * Pa.τ ^ (2 : ℕ)
              * ((Work.FIPlan.Hscale Pa.M Pa.N ^ 2 + 1)
                  * (2 * (((Work.FITop.radN Pa).toNat : ℕ) : ℝ) + 1) ^ 2)
              * (Real.log (Work.FIPlan.Hscale Pa.M Pa.N
                  + (((Work.FITop.radN Pa).toNat : ℕ) : ℝ) + 2)) ^ (8 + KL + 4))
        = (Real.sqrt Pa.M * Pa.N ^ (-(1 : ℝ) / 2)
              * ((Work.FIPlan.Hscale Pa.M Pa.N ^ 2 + 1)
                  * (2 * (((Work.FITop.radN Pa).toNat : ℕ) : ℝ) + 1) ^ 2))
            * (256 * (Real.log Pa.N + 2)
                * (Real.log (Work.FIPlan.Hscale Pa.M Pa.N
                    + (((Work.FITop.radN Pa).toNat : ℕ) : ℝ) + 2)) ^ (8 + KL + 4))
            * (C * (CZ * CL) * Pa.ϑ⁻¹ * Pa.τ ^ (2 : ℕ)) := by ring
      _ ≤ (128 * Pa.N ^ 2)
            * (256 * 2 * (Real.log Pa.N) ^ (Work.FITop4.bFun Pa.η))
            * (C * (CZ * CL) * Pa.ϑ⁻¹ * Pa.τ ^ (2 : ℕ)) := hab2
      _ = 256 * 128 * 2 * C * CZ * CL * Pa.ϑ⁻¹ * Pa.τ ^ (2 : ℕ) * Pa.N ^ 2
            * (Real.log Pa.N) ^ (Work.FITop4.bFun Pa.η) := by ring
  exact le_trans hstep1 hstep2

end Work.FIArea2.R6
