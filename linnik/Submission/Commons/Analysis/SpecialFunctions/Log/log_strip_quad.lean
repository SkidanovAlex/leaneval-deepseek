import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.NormNum.RealSqrt
import Submission.Commons.Analysis.SpecialFunctions.Log.log_one_add_le7
import Submission.Commons.Analysis.SpecialFunctions.Log.log_one_add_ge7
import Submission.Commons.Analysis.SpecialFunctions.Log.log_one_sub_le6
import Submission.Commons.Analysis.SpecialFunctions.Log.log_one_sub_ge6
import Submission.Commons.Analysis.SpecialFunctions.Trigonometric.arctan_ge3
import Submission.Commons.Analysis.SpecialFunctions.Trigonometric.arctan_le4

open scoped Topology
open Set Real
open Commons.Analysis.SpecialFunctions.Log
open Commons.Analysis.SpecialFunctions.Trigonometric

noncomputable section

namespace Commons.Analysis.SpecialFunctions.Log

private lemma sq_le_of_nonneg {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) : a ^ 2 ≤ b ^ 2 := by
  rw [sq_le_sq]
  rw [abs_of_nonneg ha, abs_of_nonneg (le_trans ha hab)]
  exact hab

private lemma inv_two_sqrt_le (a : ℝ) (ha : 0 < a) (c : ℝ) (hc : 0 < c)
    (h : (1 / (4 * c ^ 2)) ≤ a) : 1 / (2 * Real.sqrt a) ≤ c := by
  have hsq : 1 / (2 * c) ≤ Real.sqrt a := by
    rw [Real.le_sqrt (by positivity : 0 ≤ 1 / (2 * c)) (le_of_lt ha)]
    have hsq' : (1 / (2 * c)) ^ 2 ≤ a := by
      have : (1 / (2 * c)) ^ 2 = 1 / (4 * c ^ 2) := by field_simp [hc.ne']; ring
      rw [this]
      exact h
    exact hsq'
  have hcpos : 0 < 2 * c := by positivity
  have hc2 : (2 * c) ≠ 0 := by positivity
  have hone : (1 : ℝ) ≤ (2 * c) * Real.sqrt a := by
    calc
      (1 : ℝ) = (2 * c) * (1 / (2 * c)) := by field_simp [hc2, hc.ne']
      _ ≤ (2 * c) * Real.sqrt a := mul_le_mul_of_nonneg_left hsq (le_of_lt hcpos)
  have hpos : 0 < 2 * Real.sqrt a := by
    have hsp : 0 < Real.sqrt a := Real.sqrt_pos.2 ha
    positivity
  exact (div_le_iff₀ hpos).2 (by
    calc
      (1 : ℝ) ≤ (2 * c) * Real.sqrt a := hone
      _ = c * (2 * Real.sqrt a) := by ring)

/-- assembly for a rectangle box -/
private lemma combine (x t : ℝ) (hxpos : 0 < x) (htpos : 0 < t)
    (LU LD LD3 AT PM : ℝ) (hld3pos : 0 < LD3)
    (hS : Real.log (x ^ 2 + t ^ 2) / 2 - Real.log (2 + t) ≤ (1 / 2) * LU - LD)
    (hQ : (Real.arctan (t / x)) ^ 2 / Real.log (x ^ 2 + t ^ 2) ≤ AT ^ 2 / LD3)
    (hP : (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) ≤ PM)
    (hfin : (1 / 2) * LU - LD + AT ^ 2 / LD3 + PM ≤ (3 : ℝ) / 2) :
    Real.log (Real.sqrt (x ^ 2 + t ^ 2)) +
        (Real.arctan (t / x)) ^ 2 / (2 * Real.log (Real.sqrt (x ^ 2 + t ^ 2))) +
        (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) ≤
      Real.log (2 + t) + (3 : ℝ) / 2 := by
  have hapos : 0 ≤ x ^ 2 + t ^ 2 := by positivity
  have hs1 : Real.log (Real.sqrt (x ^ 2 + t ^ 2)) = Real.log (x ^ 2 + t ^ 2) / 2 :=
    Real.log_sqrt hapos
  have hrew : Real.log (Real.sqrt (x ^ 2 + t ^ 2)) +
        (Real.arctan (t / x)) ^ 2 / (2 * Real.log (Real.sqrt (x ^ 2 + t ^ 2))) +
        (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) =
      Real.log (x ^ 2 + t ^ 2) / 2 + (Real.arctan (t / x)) ^ 2 / Real.log (x ^ 2 + t ^ 2) +
        (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) := by
    rw [hs1]
    rw [show (2 : ℝ) * (Real.log (x ^ 2 + t ^ 2) / 2) = Real.log (x ^ 2 + t ^ 2) by ring]
  have hq1 : Real.log (x ^ 2 + t ^ 2) / 2 + (Real.arctan (t / x)) ^ 2 / Real.log (x ^ 2 + t ^ 2) +
      (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) ≤
    ((1 / 2) * LU - LD) + AT ^ 2 / LD3 + PM + Real.log (2 + t) := by
    calc
      Real.log (x ^ 2 + t ^ 2) / 2 + (Real.arctan (t / x)) ^ 2 / Real.log (x ^ 2 + t ^ 2) +
          (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2))
          = (Real.log (x ^ 2 + t ^ 2) / 2 - Real.log (2 + t)) +
              (Real.arctan (t / x)) ^ 2 / Real.log (x ^ 2 + t ^ 2) +
              (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) + Real.log (2 + t) := by ring
      _ ≤ ((1 / 2) * LU - LD) + AT ^ 2 / LD3 + PM + Real.log (2 + t) := by
          nlinarith [hS, hQ, hP]
  calc
    Real.log (Real.sqrt (x ^ 2 + t ^ 2)) + (Real.arctan (t / x)) ^ 2 / (2 * Real.log (Real.sqrt (x ^ 2 + t ^ 2))) +
        (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2))
        = Real.log (x ^ 2 + t ^ 2) / 2 + (Real.arctan (t / x)) ^ 2 / Real.log (x ^ 2 + t ^ 2) +
            (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) := hrew
    _ ≤ ((1 / 2) * LU - LD) + AT ^ 2 / LD3 + PM + Real.log (2 + t) := hq1
    _ ≤ Real.log (2 + t) + (3 : ℝ) / 2 := by nlinarith [hfin]

private lemma vatan_ub_m1_4 : Real.arctan (((1:ℝ)/4)) ≤ ((20229203:ℝ)/82575360) := by
  have hle := arctan_le4 (((1:ℝ)/4)) (by norm_num)
  calc
    Real.arctan (((1:ℝ)/4)) ≤ ((1:ℝ)/4) - ((1:ℝ)/4) ^ 3 / 3 + ((1:ℝ)/4) ^ 5 / 5 - ((1:ℝ)/4) ^ 7 / 7 + ((1:ℝ)/4) ^ 9 / 9 := hle
    _ = ((20229203:ℝ)/82575360) := by norm_num

private lemma vatan_ub_m1_3 : Real.arctan (((1:ℝ)/3)) ≤ ((1994903:ℝ)/6200145) := by
  have hle := arctan_le4 (((1:ℝ)/3)) (by norm_num)
  calc
    Real.arctan (((1:ℝ)/3)) ≤ ((1:ℝ)/3) - ((1:ℝ)/3) ^ 3 / 3 + ((1:ℝ)/3) ^ 5 / 5 - ((1:ℝ)/3) ^ 7 / 7 + ((1:ℝ)/3) ^ 9 / 9 := hle
    _ = ((1994903:ℝ)/6200145) := by norm_num

private lemma vatan_ub_m3_8 : Real.arctan (((3:ℝ)/8)) ≤ ((1685376321:ℝ)/4697620480) := by
  have hle := arctan_le4 (((3:ℝ)/8)) (by norm_num)
  calc
    Real.arctan (((3:ℝ)/8)) ≤ ((3:ℝ)/8) - ((3:ℝ)/8) ^ 3 / 3 + ((3:ℝ)/8) ^ 5 / 5 - ((3:ℝ)/8) ^ 7 / 7 + ((3:ℝ)/8) ^ 9 / 9 := hle
    _ = ((1685376321:ℝ)/4697620480) := by norm_num

private lemma vatan_ub_m1_2 : Real.arctan (((1:ℝ)/2)) ≤ ((74783:ℝ)/161280) := by
  have hle := arctan_le4 (((1:ℝ)/2)) (by norm_num)
  calc
    Real.arctan (((1:ℝ)/2)) ≤ ((1:ℝ)/2) - ((1:ℝ)/2) ^ 3 / 3 + ((1:ℝ)/2) ^ 5 / 5 - ((1:ℝ)/2) ^ 7 / 7 + ((1:ℝ)/2) ^ 9 / 9 := hle
    _ = ((74783:ℝ)/161280) := by norm_num

private lemma vatan_ub_m3_5 : Real.arctan (((3:ℝ)/5)) ≤ ((7392009:ℝ)/13671875) := by
  have hle := arctan_le4 (((3:ℝ)/5)) (by norm_num)
  calc
    Real.arctan (((3:ℝ)/5)) ≤ ((3:ℝ)/5) - ((3:ℝ)/5) ^ 3 / 3 + ((3:ℝ)/5) ^ 5 / 5 - ((3:ℝ)/5) ^ 7 / 7 + ((3:ℝ)/5) ^ 9 / 9 := hle
    _ = ((7392009:ℝ)/13671875) := by norm_num

private lemma vatan_ub_m2_3 : Real.arctan (((2:ℝ)/3)) ≤ ((3650446:ℝ)/6200145) := by
  have hle := arctan_le4 (((2:ℝ)/3)) (by norm_num)
  calc
    Real.arctan (((2:ℝ)/3)) ≤ ((2:ℝ)/3) - ((2:ℝ)/3) ^ 3 / 3 + ((2:ℝ)/3) ^ 5 / 5 - ((2:ℝ)/3) ^ 7 / 7 + ((2:ℝ)/3) ^ 9 / 9 := hle
    _ = ((3650446:ℝ)/6200145) := by norm_num

private lemma vatan_ub_m3_4 : Real.arctan (((3:ℝ)/4)) ≤ ((5928081:ℝ)/9175040) := by
  have hle := arctan_le4 (((3:ℝ)/4)) (by norm_num)
  calc
    Real.arctan (((3:ℝ)/4)) ≤ ((3:ℝ)/4) - ((3:ℝ)/4) ^ 3 / 3 + ((3:ℝ)/4) ^ 5 / 5 - ((3:ℝ)/4) ^ 7 / 7 + ((3:ℝ)/4) ^ 9 / 9 := hle
    _ = ((5928081:ℝ)/9175040) := by norm_num

private lemma vatan_ub_m4_5 : Real.arctan (((4:ℝ)/5)) ≤ ((83650108:ℝ)/123046875) := by
  have hle := arctan_le4 (((4:ℝ)/5)) (by norm_num)
  calc
    Real.arctan (((4:ℝ)/5)) ≤ ((4:ℝ)/5) - ((4:ℝ)/5) ^ 3 / 3 + ((4:ℝ)/5) ^ 5 / 5 - ((4:ℝ)/5) ^ 7 / 7 + ((4:ℝ)/5) ^ 9 / 9 := hle
    _ = ((83650108:ℝ)/123046875) := by norm_num

private lemma vatan_ub_m1 : Real.arctan ((1:ℝ)) ≤ ((263:ℝ)/315) := by
  have hle := arctan_le4 ((1:ℝ)) (by norm_num)
  calc
    Real.arctan ((1:ℝ)) ≤ (1:ℝ) - (1:ℝ) ^ 3 / 3 + (1:ℝ) ^ 5 / 5 - (1:ℝ) ^ 7 / 7 + (1:ℝ) ^ 9 / 9 := hle
    _ = ((263:ℝ)/315) := by norm_num

private lemma vatan_ub_m6_5 : Real.arctan (((6:ℝ)/5)) ≤ ((1089830801:ℝ)/1224720000) := by
  have hpos : 0 < (((6:ℝ)/5)) := by norm_num
  have hrec := Real.arctan_inv_of_pos hpos
  have hrec' : Real.arctan (((6:ℝ)/5)) = Real.pi / 2 - Real.arctan (((((6:ℝ)/5)))⁻¹) := by
    linarith
  have hconv : ((((6:ℝ)/5)))⁻¹ = (((5:ℝ)/6)) := by norm_num
  have hle2 : ((5:ℝ)/6) - ((5:ℝ)/6) ^ 3 / 3 + ((5:ℝ)/6) ^ 5 / 5 - ((5:ℝ)/6) ^ 7 / 7 ≤ Real.arctan (((5:ℝ)/6)) := arctan_ge3 (((5:ℝ)/6)) (by positivity)
  have hpi : Real.pi / 2 ≤ ((3927:ℝ)/2500) := by
    have h := Real.pi_lt_d4
    norm_num at h
    linarith
  calc
    Real.arctan (((6:ℝ)/5)) = Real.pi / 2 - Real.arctan (((((6:ℝ)/5)))⁻¹) := hrec'
    _ ≤ ((3927:ℝ)/2500) - Real.arctan (((((6:ℝ)/5)))⁻¹) := sub_le_sub_right hpi _
    _ ≤ ((3927:ℝ)/2500) - (((5:ℝ)/6) - ((5:ℝ)/6) ^ 3 / 3 + ((5:ℝ)/6) ^ 5 / 5 - ((5:ℝ)/6) ^ 7 / 7) := by
      have hconv2 : Real.arctan (((((6:ℝ)/5)))⁻¹) = Real.arctan (((5:ℝ)/6)) := by rw [hconv]
      rw [hconv2]
      exact sub_le_sub_left hle2 (((3927:ℝ)/2500) : ℝ)
    _ = ((1089830801:ℝ)/1224720000) := by norm_num

private lemma vatan_ub_m5_4 : Real.arctan (((5:ℝ)/4)) ≤ ((5944903:ℝ)/6562500) := by
  have hpos : 0 < (((5:ℝ)/4)) := by norm_num
  have hrec := Real.arctan_inv_of_pos hpos
  have hrec' : Real.arctan (((5:ℝ)/4)) = Real.pi / 2 - Real.arctan (((((5:ℝ)/4)))⁻¹) := by
    linarith
  have hconv : ((((5:ℝ)/4)))⁻¹ = (((4:ℝ)/5)) := by norm_num
  have hle2 : ((4:ℝ)/5) - ((4:ℝ)/5) ^ 3 / 3 + ((4:ℝ)/5) ^ 5 / 5 - ((4:ℝ)/5) ^ 7 / 7 ≤ Real.arctan (((4:ℝ)/5)) := arctan_ge3 (((4:ℝ)/5)) (by positivity)
  have hpi : Real.pi / 2 ≤ ((3927:ℝ)/2500) := by
    have h := Real.pi_lt_d4
    norm_num at h
    linarith
  calc
    Real.arctan (((5:ℝ)/4)) = Real.pi / 2 - Real.arctan (((((5:ℝ)/4)))⁻¹) := hrec'
    _ ≤ ((3927:ℝ)/2500) - Real.arctan (((((5:ℝ)/4)))⁻¹) := sub_le_sub_right hpi _
    _ ≤ ((3927:ℝ)/2500) - (((4:ℝ)/5) - ((4:ℝ)/5) ^ 3 / 3 + ((4:ℝ)/5) ^ 5 / 5 - ((4:ℝ)/5) ^ 7 / 7) := by
      have hconv2 : Real.arctan (((((5:ℝ)/4)))⁻¹) = Real.arctan (((4:ℝ)/5)) := by rw [hconv]
      rw [hconv2]
      exact sub_le_sub_left hle2 (((3927:ℝ)/2500) : ℝ)
    _ = ((5944903:ℝ)/6562500) := by norm_num

private lemma vatan_ub_m4_3 : Real.arctan (((4:ℝ)/3)) ≤ ((66879819:ℝ)/71680000) := by
  have hpos : 0 < (((4:ℝ)/3)) := by norm_num
  have hrec := Real.arctan_inv_of_pos hpos
  have hrec' : Real.arctan (((4:ℝ)/3)) = Real.pi / 2 - Real.arctan (((((4:ℝ)/3)))⁻¹) := by
    linarith
  have hconv : ((((4:ℝ)/3)))⁻¹ = (((3:ℝ)/4)) := by norm_num
  have hle2 : ((3:ℝ)/4) - ((3:ℝ)/4) ^ 3 / 3 + ((3:ℝ)/4) ^ 5 / 5 - ((3:ℝ)/4) ^ 7 / 7 ≤ Real.arctan (((3:ℝ)/4)) := arctan_ge3 (((3:ℝ)/4)) (by positivity)
  have hpi : Real.pi / 2 ≤ ((3927:ℝ)/2500) := by
    have h := Real.pi_lt_d4
    norm_num at h
    linarith
  calc
    Real.arctan (((4:ℝ)/3)) = Real.pi / 2 - Real.arctan (((((4:ℝ)/3)))⁻¹) := hrec'
    _ ≤ ((3927:ℝ)/2500) - Real.arctan (((((4:ℝ)/3)))⁻¹) := sub_le_sub_right hpi _
    _ ≤ ((3927:ℝ)/2500) - (((3:ℝ)/4) - ((3:ℝ)/4) ^ 3 / 3 + ((3:ℝ)/4) ^ 5 / 5 - ((3:ℝ)/4) ^ 7 / 7) := by
      have hconv2 : Real.arctan (((((4:ℝ)/3)))⁻¹) = Real.arctan (((3:ℝ)/4)) := by rw [hconv]
      rw [hconv2]
      exact sub_le_sub_left hle2 (((3927:ℝ)/2500) : ℝ)
    _ = ((66879819:ℝ)/71680000) := by norm_num

private lemma vatan_ub_m3_2 : Real.arctan (((3:ℝ)/2)) ≤ ((37695443:ℝ)/38272500) := by
  have hpos : 0 < (((3:ℝ)/2)) := by norm_num
  have hrec := Real.arctan_inv_of_pos hpos
  have hrec' : Real.arctan (((3:ℝ)/2)) = Real.pi / 2 - Real.arctan (((((3:ℝ)/2)))⁻¹) := by
    linarith
  have hconv : ((((3:ℝ)/2)))⁻¹ = (((2:ℝ)/3)) := by norm_num
  have hle2 : ((2:ℝ)/3) - ((2:ℝ)/3) ^ 3 / 3 + ((2:ℝ)/3) ^ 5 / 5 - ((2:ℝ)/3) ^ 7 / 7 ≤ Real.arctan (((2:ℝ)/3)) := arctan_ge3 (((2:ℝ)/3)) (by positivity)
  have hpi : Real.pi / 2 ≤ ((3927:ℝ)/2500) := by
    have h := Real.pi_lt_d4
    norm_num at h
    linarith
  calc
    Real.arctan (((3:ℝ)/2)) = Real.pi / 2 - Real.arctan (((((3:ℝ)/2)))⁻¹) := hrec'
    _ ≤ ((3927:ℝ)/2500) - Real.arctan (((((3:ℝ)/2)))⁻¹) := sub_le_sub_right hpi _
    _ ≤ ((3927:ℝ)/2500) - (((2:ℝ)/3) - ((2:ℝ)/3) ^ 3 / 3 + ((2:ℝ)/3) ^ 5 / 5 - ((2:ℝ)/3) ^ 7 / 7) := by
      have hconv2 : Real.arctan (((((3:ℝ)/2)))⁻¹) = Real.arctan (((2:ℝ)/3)) := by rw [hconv]
      rw [hconv2]
      exact sub_le_sub_left hle2 (((3927:ℝ)/2500) : ℝ)
    _ = ((37695443:ℝ)/38272500) := by norm_num

private lemma vatan_ub_m8_5 : Real.arctan (((8:ℝ)/5)) ≤ ((27894742871:ℝ)/27525120000) := by
  have hpos : 0 < (((8:ℝ)/5)) := by norm_num
  have hrec := Real.arctan_inv_of_pos hpos
  have hrec' : Real.arctan (((8:ℝ)/5)) = Real.pi / 2 - Real.arctan (((((8:ℝ)/5)))⁻¹) := by
    linarith
  have hconv : ((((8:ℝ)/5)))⁻¹ = (((5:ℝ)/8)) := by norm_num
  have hle2 : ((5:ℝ)/8) - ((5:ℝ)/8) ^ 3 / 3 + ((5:ℝ)/8) ^ 5 / 5 - ((5:ℝ)/8) ^ 7 / 7 ≤ Real.arctan (((5:ℝ)/8)) := arctan_ge3 (((5:ℝ)/8)) (by positivity)
  have hpi : Real.pi / 2 ≤ ((3927:ℝ)/2500) := by
    have h := Real.pi_lt_d4
    norm_num at h
    linarith
  calc
    Real.arctan (((8:ℝ)/5)) = Real.pi / 2 - Real.arctan (((((8:ℝ)/5)))⁻¹) := hrec'
    _ ≤ ((3927:ℝ)/2500) - Real.arctan (((((8:ℝ)/5)))⁻¹) := sub_le_sub_right hpi _
    _ ≤ ((3927:ℝ)/2500) - (((5:ℝ)/8) - ((5:ℝ)/8) ^ 3 / 3 + ((5:ℝ)/8) ^ 5 / 5 - ((5:ℝ)/8) ^ 7 / 7) := by
      have hconv2 : Real.arctan (((((8:ℝ)/5)))⁻¹) = Real.arctan (((5:ℝ)/8)) := by rw [hconv]
      rw [hconv2]
      exact sub_le_sub_left hle2 (((3927:ℝ)/2500) : ℝ)
    _ = ((27894742871:ℝ)/27525120000) := by norm_num

private lemma vatan_ub_m5_3 : Real.arctan (((5:ℝ)/3)) ≤ ((2255853:ℝ)/2187500) := by
  have hpos : 0 < (((5:ℝ)/3)) := by norm_num
  have hrec := Real.arctan_inv_of_pos hpos
  have hrec' : Real.arctan (((5:ℝ)/3)) = Real.pi / 2 - Real.arctan (((((5:ℝ)/3)))⁻¹) := by
    linarith
  have hconv : ((((5:ℝ)/3)))⁻¹ = (((3:ℝ)/5)) := by norm_num
  have hle2 : ((3:ℝ)/5) - ((3:ℝ)/5) ^ 3 / 3 + ((3:ℝ)/5) ^ 5 / 5 - ((3:ℝ)/5) ^ 7 / 7 ≤ Real.arctan (((3:ℝ)/5)) := arctan_ge3 (((3:ℝ)/5)) (by positivity)
  have hpi : Real.pi / 2 ≤ ((3927:ℝ)/2500) := by
    have h := Real.pi_lt_d4
    norm_num at h
    linarith
  calc
    Real.arctan (((5:ℝ)/3)) = Real.pi / 2 - Real.arctan (((((5:ℝ)/3)))⁻¹) := hrec'
    _ ≤ ((3927:ℝ)/2500) - Real.arctan (((((5:ℝ)/3)))⁻¹) := sub_le_sub_right hpi _
    _ ≤ ((3927:ℝ)/2500) - (((3:ℝ)/5) - ((3:ℝ)/5) ^ 3 / 3 + ((3:ℝ)/5) ^ 5 / 5 - ((3:ℝ)/5) ^ 7 / 7) := by
      have hconv2 : Real.arctan (((((5:ℝ)/3)))⁻¹) = Real.arctan (((3:ℝ)/5)) := by rw [hconv]
      rw [hconv2]
      exact sub_le_sub_left hle2 (((3927:ℝ)/2500) : ℝ)
    _ = ((2255853:ℝ)/2187500) := by norm_num

private lemma vatan_ub_m2 : Real.arctan ((2:ℝ)) ≤ ((1860319:ℝ)/1680000) := by
  have hpos : 0 < ((2:ℝ)) := by norm_num
  have hrec := Real.arctan_inv_of_pos hpos
  have hrec' : Real.arctan ((2:ℝ)) = Real.pi / 2 - Real.arctan ((((2:ℝ)))⁻¹) := by
    linarith
  have hconv : (((2:ℝ)))⁻¹ = (((1:ℝ)/2)) := by norm_num
  have hle2 : ((1:ℝ)/2) - ((1:ℝ)/2) ^ 3 / 3 + ((1:ℝ)/2) ^ 5 / 5 - ((1:ℝ)/2) ^ 7 / 7 ≤ Real.arctan (((1:ℝ)/2)) := arctan_ge3 (((1:ℝ)/2)) (by positivity)
  have hpi : Real.pi / 2 ≤ ((3927:ℝ)/2500) := by
    have h := Real.pi_lt_d4
    norm_num at h
    linarith
  calc
    Real.arctan ((2:ℝ)) = Real.pi / 2 - Real.arctan ((((2:ℝ)))⁻¹) := hrec'
    _ ≤ ((3927:ℝ)/2500) - Real.arctan ((((2:ℝ)))⁻¹) := sub_le_sub_right hpi _
    _ ≤ ((3927:ℝ)/2500) - (((1:ℝ)/2) - ((1:ℝ)/2) ^ 3 / 3 + ((1:ℝ)/2) ^ 5 / 5 - ((1:ℝ)/2) ^ 7 / 7) := by
      have hconv2 : Real.arctan ((((2:ℝ)))⁻¹) = Real.arctan (((1:ℝ)/2)) := by rw [hconv]
      rw [hconv2]
      exact sub_le_sub_left hle2 (((3927:ℝ)/2500) : ℝ)
    _ = ((1860319:ℝ)/1680000) := by norm_num

private lemma vatan_ub_m13_6 : Real.arctan (((13:ℝ)/6)) ≤ ((1250166234813:ℝ)/1098099047500) := by
  have hpos : 0 < (((13:ℝ)/6)) := by norm_num
  have hrec := Real.arctan_inv_of_pos hpos
  have hrec' : Real.arctan (((13:ℝ)/6)) = Real.pi / 2 - Real.arctan (((((13:ℝ)/6)))⁻¹) := by
    linarith
  have hconv : ((((13:ℝ)/6)))⁻¹ = (((6:ℝ)/13)) := by norm_num
  have hle2 : ((6:ℝ)/13) - ((6:ℝ)/13) ^ 3 / 3 + ((6:ℝ)/13) ^ 5 / 5 - ((6:ℝ)/13) ^ 7 / 7 ≤ Real.arctan (((6:ℝ)/13)) := arctan_ge3 (((6:ℝ)/13)) (by positivity)
  have hpi : Real.pi / 2 ≤ ((3927:ℝ)/2500) := by
    have h := Real.pi_lt_d4
    norm_num at h
    linarith
  calc
    Real.arctan (((13:ℝ)/6)) = Real.pi / 2 - Real.arctan (((((13:ℝ)/6)))⁻¹) := hrec'
    _ ≤ ((3927:ℝ)/2500) - Real.arctan (((((13:ℝ)/6)))⁻¹) := sub_le_sub_right hpi _
    _ ≤ ((3927:ℝ)/2500) - (((6:ℝ)/13) - ((6:ℝ)/13) ^ 3 / 3 + ((6:ℝ)/13) ^ 5 / 5 - ((6:ℝ)/13) ^ 7 / 7) := by
      have hconv2 : Real.arctan (((((13:ℝ)/6)))⁻¹) = Real.arctan (((6:ℝ)/13)) := by rw [hconv]
      rw [hconv2]
      exact sub_le_sub_left hle2 (((3927:ℝ)/2500) : ℝ)
    _ = ((1250166234813:ℝ)/1098099047500) := by norm_num

private lemma vatan_ub_m9_4 : Real.arctan (((9:ℝ)/4)) ≤ ((96478260841:ℝ)/83701957500) := by
  have hpos : 0 < (((9:ℝ)/4)) := by norm_num
  have hrec := Real.arctan_inv_of_pos hpos
  have hrec' : Real.arctan (((9:ℝ)/4)) = Real.pi / 2 - Real.arctan (((((9:ℝ)/4)))⁻¹) := by
    linarith
  have hconv : ((((9:ℝ)/4)))⁻¹ = (((4:ℝ)/9)) := by norm_num
  have hle2 : ((4:ℝ)/9) - ((4:ℝ)/9) ^ 3 / 3 + ((4:ℝ)/9) ^ 5 / 5 - ((4:ℝ)/9) ^ 7 / 7 ≤ Real.arctan (((4:ℝ)/9)) := arctan_ge3 (((4:ℝ)/9)) (by positivity)
  have hpi : Real.pi / 2 ≤ ((3927:ℝ)/2500) := by
    have h := Real.pi_lt_d4
    norm_num at h
    linarith
  calc
    Real.arctan (((9:ℝ)/4)) = Real.pi / 2 - Real.arctan (((((9:ℝ)/4)))⁻¹) := hrec'
    _ ≤ ((3927:ℝ)/2500) - Real.arctan (((((9:ℝ)/4)))⁻¹) := sub_le_sub_right hpi _
    _ ≤ ((3927:ℝ)/2500) - (((4:ℝ)/9) - ((4:ℝ)/9) ^ 3 / 3 + ((4:ℝ)/9) ^ 5 / 5 - ((4:ℝ)/9) ^ 7 / 7) := by
      have hconv2 : Real.arctan (((((9:ℝ)/4)))⁻¹) = Real.arctan (((4:ℝ)/9)) := by rw [hconv]
      rw [hconv2]
      exact sub_le_sub_left hle2 (((3927:ℝ)/2500) : ℝ)
    _ = ((96478260841:ℝ)/83701957500) := by norm_num

private lemma vatan_ub_m12_5 : Real.arctan (((12:ℝ)/5)) ≤ ((184361820653:ℝ)/156764160000) := by
  have hpos : 0 < (((12:ℝ)/5)) := by norm_num
  have hrec := Real.arctan_inv_of_pos hpos
  have hrec' : Real.arctan (((12:ℝ)/5)) = Real.pi / 2 - Real.arctan (((((12:ℝ)/5)))⁻¹) := by
    linarith
  have hconv : ((((12:ℝ)/5)))⁻¹ = (((5:ℝ)/12)) := by norm_num
  have hle2 : ((5:ℝ)/12) - ((5:ℝ)/12) ^ 3 / 3 + ((5:ℝ)/12) ^ 5 / 5 - ((5:ℝ)/12) ^ 7 / 7 ≤ Real.arctan (((5:ℝ)/12)) := arctan_ge3 (((5:ℝ)/12)) (by positivity)
  have hpi : Real.pi / 2 ≤ ((3927:ℝ)/2500) := by
    have h := Real.pi_lt_d4
    norm_num at h
    linarith
  calc
    Real.arctan (((12:ℝ)/5)) = Real.pi / 2 - Real.arctan (((((12:ℝ)/5)))⁻¹) := hrec'
    _ ≤ ((3927:ℝ)/2500) - Real.arctan (((((12:ℝ)/5)))⁻¹) := sub_le_sub_right hpi _
    _ ≤ ((3927:ℝ)/2500) - (((5:ℝ)/12) - ((5:ℝ)/12) ^ 3 / 3 + ((5:ℝ)/12) ^ 5 / 5 - ((5:ℝ)/12) ^ 7 / 7) := by
      have hconv2 : Real.arctan (((((12:ℝ)/5)))⁻¹) = Real.arctan (((5:ℝ)/12)) := by rw [hconv]
      rw [hconv2]
      exact sub_le_sub_left hle2 (((3927:ℝ)/2500) : ℝ)
    _ = ((184361820653:ℝ)/156764160000) := by norm_num

private lemma vatan_ub_m5_2 : Real.arctan (((5:ℝ)/2)) ≤ ((7811471:ℝ)/6562500) := by
  have hpos : 0 < (((5:ℝ)/2)) := by norm_num
  have hrec := Real.arctan_inv_of_pos hpos
  have hrec' : Real.arctan (((5:ℝ)/2)) = Real.pi / 2 - Real.arctan (((((5:ℝ)/2)))⁻¹) := by
    linarith
  have hconv : ((((5:ℝ)/2)))⁻¹ = (((2:ℝ)/5)) := by norm_num
  have hle2 : ((2:ℝ)/5) - ((2:ℝ)/5) ^ 3 / 3 + ((2:ℝ)/5) ^ 5 / 5 - ((2:ℝ)/5) ^ 7 / 7 ≤ Real.arctan (((2:ℝ)/5)) := arctan_ge3 (((2:ℝ)/5)) (by positivity)
  have hpi : Real.pi / 2 ≤ ((3927:ℝ)/2500) := by
    have h := Real.pi_lt_d4
    norm_num at h
    linarith
  calc
    Real.arctan (((5:ℝ)/2)) = Real.pi / 2 - Real.arctan (((((5:ℝ)/2)))⁻¹) := hrec'
    _ ≤ ((3927:ℝ)/2500) - Real.arctan (((((5:ℝ)/2)))⁻¹) := sub_le_sub_right hpi _
    _ ≤ ((3927:ℝ)/2500) - (((2:ℝ)/5) - ((2:ℝ)/5) ^ 3 / 3 + ((2:ℝ)/5) ^ 5 / 5 - ((2:ℝ)/5) ^ 7 / 7) := by
      have hconv2 : Real.arctan (((((5:ℝ)/2)))⁻¹) = Real.arctan (((2:ℝ)/5)) := by rw [hconv]
      rw [hconv2]
      exact sub_le_sub_left hle2 (((3927:ℝ)/2500) : ℝ)
    _ = ((7811471:ℝ)/6562500) := by norm_num

private lemma vatan_ub_m8_3 : Real.arctan (((8:ℝ)/3)) ≤ ((11120551707:ℝ)/9175040000) := by
  have hpos : 0 < (((8:ℝ)/3)) := by norm_num
  have hrec := Real.arctan_inv_of_pos hpos
  have hrec' : Real.arctan (((8:ℝ)/3)) = Real.pi / 2 - Real.arctan (((((8:ℝ)/3)))⁻¹) := by
    linarith
  have hconv : ((((8:ℝ)/3)))⁻¹ = (((3:ℝ)/8)) := by norm_num
  have hle2 : ((3:ℝ)/8) - ((3:ℝ)/8) ^ 3 / 3 + ((3:ℝ)/8) ^ 5 / 5 - ((3:ℝ)/8) ^ 7 / 7 ≤ Real.arctan (((3:ℝ)/8)) := arctan_ge3 (((3:ℝ)/8)) (by positivity)
  have hpi : Real.pi / 2 ≤ ((3927:ℝ)/2500) := by
    have h := Real.pi_lt_d4
    norm_num at h
    linarith
  calc
    Real.arctan (((8:ℝ)/3)) = Real.pi / 2 - Real.arctan (((((8:ℝ)/3)))⁻¹) := hrec'
    _ ≤ ((3927:ℝ)/2500) - Real.arctan (((((8:ℝ)/3)))⁻¹) := sub_le_sub_right hpi _
    _ ≤ ((3927:ℝ)/2500) - (((3:ℝ)/8) - ((3:ℝ)/8) ^ 3 / 3 + ((3:ℝ)/8) ^ 5 / 5 - ((3:ℝ)/8) ^ 7 / 7) := by
      have hconv2 : Real.arctan (((((8:ℝ)/3)))⁻¹) = Real.arctan (((3:ℝ)/8)) := by rw [hconv]
      rw [hconv2]
      exact sub_le_sub_left hle2 (((3927:ℝ)/2500) : ℝ)
    _ = ((11120551707:ℝ)/9175040000) := by norm_num

private lemma vatan_ub_m3 : Real.arctan ((3:ℝ)) ≤ ((47804443:ℝ)/38272500) := by
  have hpos : 0 < ((3:ℝ)) := by norm_num
  have hrec := Real.arctan_inv_of_pos hpos
  have hrec' : Real.arctan ((3:ℝ)) = Real.pi / 2 - Real.arctan ((((3:ℝ)))⁻¹) := by
    linarith
  have hconv : (((3:ℝ)))⁻¹ = (((1:ℝ)/3)) := by norm_num
  have hle2 : ((1:ℝ)/3) - ((1:ℝ)/3) ^ 3 / 3 + ((1:ℝ)/3) ^ 5 / 5 - ((1:ℝ)/3) ^ 7 / 7 ≤ Real.arctan (((1:ℝ)/3)) := arctan_ge3 (((1:ℝ)/3)) (by positivity)
  have hpi : Real.pi / 2 ≤ ((3927:ℝ)/2500) := by
    have h := Real.pi_lt_d4
    norm_num at h
    linarith
  calc
    Real.arctan ((3:ℝ)) = Real.pi / 2 - Real.arctan ((((3:ℝ)))⁻¹) := hrec'
    _ ≤ ((3927:ℝ)/2500) - Real.arctan ((((3:ℝ)))⁻¹) := sub_le_sub_right hpi _
    _ ≤ ((3927:ℝ)/2500) - (((1:ℝ)/3) - ((1:ℝ)/3) ^ 3 / 3 + ((1:ℝ)/3) ^ 5 / 5 - ((1:ℝ)/3) ^ 7 / 7) := by
      have hconv2 : Real.arctan ((((3:ℝ)))⁻¹) = Real.arctan (((1:ℝ)/3)) := by rw [hconv]
      rw [hconv2]
      exact sub_le_sub_left hle2 (((3927:ℝ)/2500) : ℝ)
    _ = ((47804443:ℝ)/38272500) := by norm_num

private lemma vatan_ub_m13_4 : Real.arctan (((13:ℝ)/4)) ≤ ((4191346173439:ℝ)/3294297142500) := by
  have hpos : 0 < (((13:ℝ)/4)) := by norm_num
  have hrec := Real.arctan_inv_of_pos hpos
  have hrec' : Real.arctan (((13:ℝ)/4)) = Real.pi / 2 - Real.arctan (((((13:ℝ)/4)))⁻¹) := by
    linarith
  have hconv : ((((13:ℝ)/4)))⁻¹ = (((4:ℝ)/13)) := by norm_num
  have hle2 : ((4:ℝ)/13) - ((4:ℝ)/13) ^ 3 / 3 + ((4:ℝ)/13) ^ 5 / 5 - ((4:ℝ)/13) ^ 7 / 7 ≤ Real.arctan (((4:ℝ)/13)) := arctan_ge3 (((4:ℝ)/13)) (by positivity)
  have hpi : Real.pi / 2 ≤ ((3927:ℝ)/2500) := by
    have h := Real.pi_lt_d4
    norm_num at h
    linarith
  calc
    Real.arctan (((13:ℝ)/4)) = Real.pi / 2 - Real.arctan (((((13:ℝ)/4)))⁻¹) := hrec'
    _ ≤ ((3927:ℝ)/2500) - Real.arctan (((((13:ℝ)/4)))⁻¹) := sub_le_sub_right hpi _
    _ ≤ ((3927:ℝ)/2500) - (((4:ℝ)/13) - ((4:ℝ)/13) ^ 3 / 3 + ((4:ℝ)/13) ^ 5 / 5 - ((4:ℝ)/13) ^ 7 / 7) := by
      have hconv2 : Real.arctan (((((13:ℝ)/4)))⁻¹) = Real.arctan (((4:ℝ)/13)) := by rw [hconv]
      rw [hconv2]
      exact sub_le_sub_left hle2 (((3927:ℝ)/2500) : ℝ)
    _ = ((4191346173439:ℝ)/3294297142500) := by norm_num

private lemma vatan_ub_m10_3 : Real.arctan (((10:ℝ)/3)) ≤ ((89554167:ℝ)/70000000) := by
  have hpos : 0 < (((10:ℝ)/3)) := by norm_num
  have hrec := Real.arctan_inv_of_pos hpos
  have hrec' : Real.arctan (((10:ℝ)/3)) = Real.pi / 2 - Real.arctan (((((10:ℝ)/3)))⁻¹) := by
    linarith
  have hconv : ((((10:ℝ)/3)))⁻¹ = (((3:ℝ)/10)) := by norm_num
  have hle2 : ((3:ℝ)/10) - ((3:ℝ)/10) ^ 3 / 3 + ((3:ℝ)/10) ^ 5 / 5 - ((3:ℝ)/10) ^ 7 / 7 ≤ Real.arctan (((3:ℝ)/10)) := arctan_ge3 (((3:ℝ)/10)) (by positivity)
  have hpi : Real.pi / 2 ≤ ((3927:ℝ)/2500) := by
    have h := Real.pi_lt_d4
    norm_num at h
    linarith
  calc
    Real.arctan (((10:ℝ)/3)) = Real.pi / 2 - Real.arctan (((((10:ℝ)/3)))⁻¹) := hrec'
    _ ≤ ((3927:ℝ)/2500) - Real.arctan (((((10:ℝ)/3)))⁻¹) := sub_le_sub_right hpi _
    _ ≤ ((3927:ℝ)/2500) - (((3:ℝ)/10) - ((3:ℝ)/10) ^ 3 / 3 + ((3:ℝ)/10) ^ 5 / 5 - ((3:ℝ)/10) ^ 7 / 7) := by
      have hconv2 : Real.arctan (((((10:ℝ)/3)))⁻¹) = Real.arctan (((3:ℝ)/10)) := by rw [hconv]
      rw [hconv2]
      exact sub_le_sub_left hle2 (((3927:ℝ)/2500) : ℝ)
    _ = ((89554167:ℝ)/70000000) := by norm_num

private lemma vatan_ub_m18_5 : Real.arctan (((18:ℝ)/5)) ≤ ((3481610855537:ℝ)/2678462640000) := by
  have hpos : 0 < (((18:ℝ)/5)) := by norm_num
  have hrec := Real.arctan_inv_of_pos hpos
  have hrec' : Real.arctan (((18:ℝ)/5)) = Real.pi / 2 - Real.arctan (((((18:ℝ)/5)))⁻¹) := by
    linarith
  have hconv : ((((18:ℝ)/5)))⁻¹ = (((5:ℝ)/18)) := by norm_num
  have hle2 : ((5:ℝ)/18) - ((5:ℝ)/18) ^ 3 / 3 + ((5:ℝ)/18) ^ 5 / 5 - ((5:ℝ)/18) ^ 7 / 7 ≤ Real.arctan (((5:ℝ)/18)) := arctan_ge3 (((5:ℝ)/18)) (by positivity)
  have hpi : Real.pi / 2 ≤ ((3927:ℝ)/2500) := by
    have h := Real.pi_lt_d4
    norm_num at h
    linarith
  calc
    Real.arctan (((18:ℝ)/5)) = Real.pi / 2 - Real.arctan (((((18:ℝ)/5)))⁻¹) := hrec'
    _ ≤ ((3927:ℝ)/2500) - Real.arctan (((((18:ℝ)/5)))⁻¹) := sub_le_sub_right hpi _
    _ ≤ ((3927:ℝ)/2500) - (((5:ℝ)/18) - ((5:ℝ)/18) ^ 3 / 3 + ((5:ℝ)/18) ^ 5 / 5 - ((5:ℝ)/18) ^ 7 / 7) := by
      have hconv2 : Real.arctan (((((18:ℝ)/5)))⁻¹) = Real.arctan (((5:ℝ)/18)) := by rw [hconv]
      rw [hconv2]
      exact sub_le_sub_left hle2 (((3927:ℝ)/2500) : ℝ)
    _ = ((3481610855537:ℝ)/2678462640000) := by norm_num

private lemma vatan_ub_m15_4 : Real.arctan (((15:ℝ)/4)) ≤ ((6268070671:ℝ)/4784062500) := by
  have hpos : 0 < (((15:ℝ)/4)) := by norm_num
  have hrec := Real.arctan_inv_of_pos hpos
  have hrec' : Real.arctan (((15:ℝ)/4)) = Real.pi / 2 - Real.arctan (((((15:ℝ)/4)))⁻¹) := by
    linarith
  have hconv : ((((15:ℝ)/4)))⁻¹ = (((4:ℝ)/15)) := by norm_num
  have hle2 : ((4:ℝ)/15) - ((4:ℝ)/15) ^ 3 / 3 + ((4:ℝ)/15) ^ 5 / 5 - ((4:ℝ)/15) ^ 7 / 7 ≤ Real.arctan (((4:ℝ)/15)) := arctan_ge3 (((4:ℝ)/15)) (by positivity)
  have hpi : Real.pi / 2 ≤ ((3927:ℝ)/2500) := by
    have h := Real.pi_lt_d4
    norm_num at h
    linarith
  calc
    Real.arctan (((15:ℝ)/4)) = Real.pi / 2 - Real.arctan (((((15:ℝ)/4)))⁻¹) := hrec'
    _ ≤ ((3927:ℝ)/2500) - Real.arctan (((((15:ℝ)/4)))⁻¹) := sub_le_sub_right hpi _
    _ ≤ ((3927:ℝ)/2500) - (((4:ℝ)/15) - ((4:ℝ)/15) ^ 3 / 3 + ((4:ℝ)/15) ^ 5 / 5 - ((4:ℝ)/15) ^ 7 / 7) := by
      have hconv2 : Real.arctan (((((15:ℝ)/4)))⁻¹) = Real.arctan (((4:ℝ)/15)) := by rw [hconv]
      rw [hconv2]
      exact sub_le_sub_left hle2 (((3927:ℝ)/2500) : ℝ)
    _ = ((6268070671:ℝ)/4784062500) := by norm_num

private lemma vatan_ub_m4 : Real.arctan ((4:ℝ)) ≤ ((285104707:ℝ)/215040000) := by
  have hpos : 0 < ((4:ℝ)) := by norm_num
  have hrec := Real.arctan_inv_of_pos hpos
  have hrec' : Real.arctan ((4:ℝ)) = Real.pi / 2 - Real.arctan ((((4:ℝ)))⁻¹) := by
    linarith
  have hconv : (((4:ℝ)))⁻¹ = (((1:ℝ)/4)) := by norm_num
  have hle2 : ((1:ℝ)/4) - ((1:ℝ)/4) ^ 3 / 3 + ((1:ℝ)/4) ^ 5 / 5 - ((1:ℝ)/4) ^ 7 / 7 ≤ Real.arctan (((1:ℝ)/4)) := arctan_ge3 (((1:ℝ)/4)) (by positivity)
  have hpi : Real.pi / 2 ≤ ((3927:ℝ)/2500) := by
    have h := Real.pi_lt_d4
    norm_num at h
    linarith
  calc
    Real.arctan ((4:ℝ)) = Real.pi / 2 - Real.arctan ((((4:ℝ)))⁻¹) := hrec'
    _ ≤ ((3927:ℝ)/2500) - Real.arctan ((((4:ℝ)))⁻¹) := sub_le_sub_right hpi _
    _ ≤ ((3927:ℝ)/2500) - (((1:ℝ)/4) - ((1:ℝ)/4) ^ 3 / 3 + ((1:ℝ)/4) ^ 5 / 5 - ((1:ℝ)/4) ^ 7 / 7) := by
      have hconv2 : Real.arctan ((((4:ℝ)))⁻¹) = Real.arctan (((1:ℝ)/4)) := by rw [hconv]
      rw [hconv2]
      exact sub_le_sub_left hle2 (((3927:ℝ)/2500) : ℝ)
    _ = ((285104707:ℝ)/215040000) := by norm_num

private lemma vatan_ub_m13_3 : Real.arctan (((13:ℝ)/3)) ≤ ((1475846601813:ℝ)/1098099047500) := by
  have hpos : 0 < (((13:ℝ)/3)) := by norm_num
  have hrec := Real.arctan_inv_of_pos hpos
  have hrec' : Real.arctan (((13:ℝ)/3)) = Real.pi / 2 - Real.arctan (((((13:ℝ)/3)))⁻¹) := by
    linarith
  have hconv : ((((13:ℝ)/3)))⁻¹ = (((3:ℝ)/13)) := by norm_num
  have hle2 : ((3:ℝ)/13) - ((3:ℝ)/13) ^ 3 / 3 + ((3:ℝ)/13) ^ 5 / 5 - ((3:ℝ)/13) ^ 7 / 7 ≤ Real.arctan (((3:ℝ)/13)) := arctan_ge3 (((3:ℝ)/13)) (by positivity)
  have hpi : Real.pi / 2 ≤ ((3927:ℝ)/2500) := by
    have h := Real.pi_lt_d4
    norm_num at h
    linarith
  calc
    Real.arctan (((13:ℝ)/3)) = Real.pi / 2 - Real.arctan (((((13:ℝ)/3)))⁻¹) := hrec'
    _ ≤ ((3927:ℝ)/2500) - Real.arctan (((((13:ℝ)/3)))⁻¹) := sub_le_sub_right hpi _
    _ ≤ ((3927:ℝ)/2500) - (((3:ℝ)/13) - ((3:ℝ)/13) ^ 3 / 3 + ((3:ℝ)/13) ^ 5 / 5 - ((3:ℝ)/13) ^ 7 / 7) := by
      have hconv2 : Real.arctan (((((13:ℝ)/3)))⁻¹) = Real.arctan (((3:ℝ)/13)) := by rw [hconv]
      rw [hconv2]
      exact sub_le_sub_left hle2 (((3927:ℝ)/2500) : ℝ)
    _ = ((1475846601813:ℝ)/1098099047500) := by norm_num

private lemma vatan_ub_m9_2 : Real.arctan (((9:ℝ)/2)) ≤ ((113176027841:ℝ)/83701957500) := by
  have hpos : 0 < (((9:ℝ)/2)) := by norm_num
  have hrec := Real.arctan_inv_of_pos hpos
  have hrec' : Real.arctan (((9:ℝ)/2)) = Real.pi / 2 - Real.arctan (((((9:ℝ)/2)))⁻¹) := by
    linarith
  have hconv : ((((9:ℝ)/2)))⁻¹ = (((2:ℝ)/9)) := by norm_num
  have hle2 : ((2:ℝ)/9) - ((2:ℝ)/9) ^ 3 / 3 + ((2:ℝ)/9) ^ 5 / 5 - ((2:ℝ)/9) ^ 7 / 7 ≤ Real.arctan (((2:ℝ)/9)) := arctan_ge3 (((2:ℝ)/9)) (by positivity)
  have hpi : Real.pi / 2 ≤ ((3927:ℝ)/2500) := by
    have h := Real.pi_lt_d4
    norm_num at h
    linarith
  calc
    Real.arctan (((9:ℝ)/2)) = Real.pi / 2 - Real.arctan (((((9:ℝ)/2)))⁻¹) := hrec'
    _ ≤ ((3927:ℝ)/2500) - Real.arctan (((((9:ℝ)/2)))⁻¹) := sub_le_sub_right hpi _
    _ ≤ ((3927:ℝ)/2500) - (((2:ℝ)/9) - ((2:ℝ)/9) ^ 3 / 3 + ((2:ℝ)/9) ^ 5 / 5 - ((2:ℝ)/9) ^ 7 / 7) := by
      have hconv2 : Real.arctan (((((9:ℝ)/2)))⁻¹) = Real.arctan (((2:ℝ)/9)) := by rw [hconv]
      rw [hconv2]
      exact sub_le_sub_left hle2 (((3927:ℝ)/2500) : ℝ)
    _ = ((113176027841:ℝ)/83701957500) := by norm_num

private lemma vatan_ub_m5 : Real.arctan ((5:ℝ)) ≤ ((9012967:ℝ)/6562500) := by
  have hpos : 0 < ((5:ℝ)) := by norm_num
  have hrec := Real.arctan_inv_of_pos hpos
  have hrec' : Real.arctan ((5:ℝ)) = Real.pi / 2 - Real.arctan ((((5:ℝ)))⁻¹) := by
    linarith
  have hconv : (((5:ℝ)))⁻¹ = (((1:ℝ)/5)) := by norm_num
  have hle2 : ((1:ℝ)/5) - ((1:ℝ)/5) ^ 3 / 3 + ((1:ℝ)/5) ^ 5 / 5 - ((1:ℝ)/5) ^ 7 / 7 ≤ Real.arctan (((1:ℝ)/5)) := arctan_ge3 (((1:ℝ)/5)) (by positivity)
  have hpi : Real.pi / 2 ≤ ((3927:ℝ)/2500) := by
    have h := Real.pi_lt_d4
    norm_num at h
    linarith
  calc
    Real.arctan ((5:ℝ)) = Real.pi / 2 - Real.arctan ((((5:ℝ)))⁻¹) := hrec'
    _ ≤ ((3927:ℝ)/2500) - Real.arctan ((((5:ℝ)))⁻¹) := sub_le_sub_right hpi _
    _ ≤ ((3927:ℝ)/2500) - (((1:ℝ)/5) - ((1:ℝ)/5) ^ 3 / 3 + ((1:ℝ)/5) ^ 5 / 5 - ((1:ℝ)/5) ^ 7 / 7) := by
      have hconv2 : Real.arctan ((((5:ℝ)))⁻¹) = Real.arctan (((1:ℝ)/5)) := by rw [hconv]
      rw [hconv2]
      exact sub_le_sub_left hle2 (((3927:ℝ)/2500) : ℝ)
    _ = ((9012967:ℝ)/6562500) := by norm_num

private lemma vatan_ub_m26_5 : Real.arctan (((26:ℝ)/5)) ≤ ((145561734567923:ℝ)/105417508560000) := by
  have hpos : 0 < (((26:ℝ)/5)) := by norm_num
  have hrec := Real.arctan_inv_of_pos hpos
  have hrec' : Real.arctan (((26:ℝ)/5)) = Real.pi / 2 - Real.arctan (((((26:ℝ)/5)))⁻¹) := by
    linarith
  have hconv : ((((26:ℝ)/5)))⁻¹ = (((5:ℝ)/26)) := by norm_num
  have hle2 : ((5:ℝ)/26) - ((5:ℝ)/26) ^ 3 / 3 + ((5:ℝ)/26) ^ 5 / 5 - ((5:ℝ)/26) ^ 7 / 7 ≤ Real.arctan (((5:ℝ)/26)) := arctan_ge3 (((5:ℝ)/26)) (by positivity)
  have hpi : Real.pi / 2 ≤ ((3927:ℝ)/2500) := by
    have h := Real.pi_lt_d4
    norm_num at h
    linarith
  calc
    Real.arctan (((26:ℝ)/5)) = Real.pi / 2 - Real.arctan (((((26:ℝ)/5)))⁻¹) := hrec'
    _ ≤ ((3927:ℝ)/2500) - Real.arctan (((((26:ℝ)/5)))⁻¹) := sub_le_sub_right hpi _
    _ ≤ ((3927:ℝ)/2500) - (((5:ℝ)/26) - ((5:ℝ)/26) ^ 3 / 3 + ((5:ℝ)/26) ^ 5 / 5 - ((5:ℝ)/26) ^ 7 / 7) := by
      have hconv2 : Real.arctan (((((26:ℝ)/5)))⁻¹) = Real.arctan (((5:ℝ)/26)) := by rw [hconv]
      rw [hconv2]
      exact sub_le_sub_left hle2 (((3927:ℝ)/2500) : ℝ)
    _ = ((145561734567923:ℝ)/105417508560000) := by norm_num

private lemma vatan_ub_m6 : Real.arctan ((6:ℝ)) ≤ ((1721529301:ℝ)/1224720000) := by
  have hpos : 0 < ((6:ℝ)) := by norm_num
  have hrec := Real.arctan_inv_of_pos hpos
  have hrec' : Real.arctan ((6:ℝ)) = Real.pi / 2 - Real.arctan ((((6:ℝ)))⁻¹) := by
    linarith
  have hconv : (((6:ℝ)))⁻¹ = (((1:ℝ)/6)) := by norm_num
  have hle2 : ((1:ℝ)/6) - ((1:ℝ)/6) ^ 3 / 3 + ((1:ℝ)/6) ^ 5 / 5 - ((1:ℝ)/6) ^ 7 / 7 ≤ Real.arctan (((1:ℝ)/6)) := arctan_ge3 (((1:ℝ)/6)) (by positivity)
  have hpi : Real.pi / 2 ≤ ((3927:ℝ)/2500) := by
    have h := Real.pi_lt_d4
    norm_num at h
    linarith
  calc
    Real.arctan ((6:ℝ)) = Real.pi / 2 - Real.arctan ((((6:ℝ)))⁻¹) := hrec'
    _ ≤ ((3927:ℝ)/2500) - Real.arctan ((((6:ℝ)))⁻¹) := sub_le_sub_right hpi _
    _ ≤ ((3927:ℝ)/2500) - (((1:ℝ)/6) - ((1:ℝ)/6) ^ 3 / 3 + ((1:ℝ)/6) ^ 5 / 5 - ((1:ℝ)/6) ^ 7 / 7) := by
      have hconv2 : Real.arctan ((((6:ℝ)))⁻¹) = Real.arctan (((1:ℝ)/6)) := by rw [hconv]
      rw [hconv2]
      exact sub_le_sub_left hle2 (((3927:ℝ)/2500) : ℝ)
    _ = ((1721529301:ℝ)/1224720000) := by norm_num

private lemma vatan_ub_m13_2 : Real.arctan (((13:ℝ)/2)) ≤ ((4671809722439:ℝ)/3294297142500) := by
  have hpos : 0 < (((13:ℝ)/2)) := by norm_num
  have hrec := Real.arctan_inv_of_pos hpos
  have hrec' : Real.arctan (((13:ℝ)/2)) = Real.pi / 2 - Real.arctan (((((13:ℝ)/2)))⁻¹) := by
    linarith
  have hconv : ((((13:ℝ)/2)))⁻¹ = (((2:ℝ)/13)) := by norm_num
  have hle2 : ((2:ℝ)/13) - ((2:ℝ)/13) ^ 3 / 3 + ((2:ℝ)/13) ^ 5 / 5 - ((2:ℝ)/13) ^ 7 / 7 ≤ Real.arctan (((2:ℝ)/13)) := arctan_ge3 (((2:ℝ)/13)) (by positivity)
  have hpi : Real.pi / 2 ≤ ((3927:ℝ)/2500) := by
    have h := Real.pi_lt_d4
    norm_num at h
    linarith
  calc
    Real.arctan (((13:ℝ)/2)) = Real.pi / 2 - Real.arctan (((((13:ℝ)/2)))⁻¹) := hrec'
    _ ≤ ((3927:ℝ)/2500) - Real.arctan (((((13:ℝ)/2)))⁻¹) := sub_le_sub_right hpi _
    _ ≤ ((3927:ℝ)/2500) - (((2:ℝ)/13) - ((2:ℝ)/13) ^ 3 / 3 + ((2:ℝ)/13) ^ 5 / 5 - ((2:ℝ)/13) ^ 7 / 7) := by
      have hconv2 : Real.arctan (((((13:ℝ)/2)))⁻¹) = Real.arctan (((2:ℝ)/13)) := by rw [hconv]
      rw [hconv2]
      exact sub_le_sub_left hle2 (((3927:ℝ)/2500) : ℝ)
    _ = ((4671809722439:ℝ)/3294297142500) := by norm_num

private lemma vatan_ub_m15_2 : Real.arctan (((15:ℝ)/2)) ≤ ((6880670567:ℝ)/4784062500) := by
  have hpos : 0 < (((15:ℝ)/2)) := by norm_num
  have hrec := Real.arctan_inv_of_pos hpos
  have hrec' : Real.arctan (((15:ℝ)/2)) = Real.pi / 2 - Real.arctan (((((15:ℝ)/2)))⁻¹) := by
    linarith
  have hconv : ((((15:ℝ)/2)))⁻¹ = (((2:ℝ)/15)) := by norm_num
  have hle2 : ((2:ℝ)/15) - ((2:ℝ)/15) ^ 3 / 3 + ((2:ℝ)/15) ^ 5 / 5 - ((2:ℝ)/15) ^ 7 / 7 ≤ Real.arctan (((2:ℝ)/15)) := arctan_ge3 (((2:ℝ)/15)) (by positivity)
  have hpi : Real.pi / 2 ≤ ((3927:ℝ)/2500) := by
    have h := Real.pi_lt_d4
    norm_num at h
    linarith
  calc
    Real.arctan (((15:ℝ)/2)) = Real.pi / 2 - Real.arctan (((((15:ℝ)/2)))⁻¹) := hrec'
    _ ≤ ((3927:ℝ)/2500) - Real.arctan (((((15:ℝ)/2)))⁻¹) := sub_le_sub_right hpi _
    _ ≤ ((3927:ℝ)/2500) - (((2:ℝ)/15) - ((2:ℝ)/15) ^ 3 / 3 + ((2:ℝ)/15) ^ 5 / 5 - ((2:ℝ)/15) ^ 7 / 7) := by
      have hconv2 : Real.arctan (((((15:ℝ)/2)))⁻¹) = Real.arctan (((2:ℝ)/15)) := by rw [hconv]
      rw [hconv2]
      exact sub_le_sub_left hle2 (((3927:ℝ)/2500) : ℝ)
    _ = ((6880670567:ℝ)/4784062500) := by norm_num

private lemma vatan_ub_m26_3 : Real.arctan (((26:ℝ)/3)) ≤ ((51159938984391:ℝ)/35139169520000) := by
  have hpos : 0 < (((26:ℝ)/3)) := by norm_num
  have hrec := Real.arctan_inv_of_pos hpos
  have hrec' : Real.arctan (((26:ℝ)/3)) = Real.pi / 2 - Real.arctan (((((26:ℝ)/3)))⁻¹) := by
    linarith
  have hconv : ((((26:ℝ)/3)))⁻¹ = (((3:ℝ)/26)) := by norm_num
  have hle2 : ((3:ℝ)/26) - ((3:ℝ)/26) ^ 3 / 3 + ((3:ℝ)/26) ^ 5 / 5 - ((3:ℝ)/26) ^ 7 / 7 ≤ Real.arctan (((3:ℝ)/26)) := arctan_ge3 (((3:ℝ)/26)) (by positivity)
  have hpi : Real.pi / 2 ≤ ((3927:ℝ)/2500) := by
    have h := Real.pi_lt_d4
    norm_num at h
    linarith
  calc
    Real.arctan (((26:ℝ)/3)) = Real.pi / 2 - Real.arctan (((((26:ℝ)/3)))⁻¹) := hrec'
    _ ≤ ((3927:ℝ)/2500) - Real.arctan (((((26:ℝ)/3)))⁻¹) := sub_le_sub_right hpi _
    _ ≤ ((3927:ℝ)/2500) - (((3:ℝ)/26) - ((3:ℝ)/26) ^ 3 / 3 + ((3:ℝ)/26) ^ 5 / 5 - ((3:ℝ)/26) ^ 7 / 7) := by
      have hconv2 : Real.arctan (((((26:ℝ)/3)))⁻¹) = Real.arctan (((3:ℝ)/26)) := by rw [hconv]
      rw [hconv2]
      exact sub_le_sub_left hle2 (((3927:ℝ)/2500) : ℝ)
    _ = ((51159938984391:ℝ)/35139169520000) := by norm_num

private lemma vatan_ub_m9 : Real.arctan ((9:ℝ)) ≤ ((122216808841:ℝ)/83701957500) := by
  have hpos : 0 < ((9:ℝ)) := by norm_num
  have hrec := Real.arctan_inv_of_pos hpos
  have hrec' : Real.arctan ((9:ℝ)) = Real.pi / 2 - Real.arctan ((((9:ℝ)))⁻¹) := by
    linarith
  have hconv : (((9:ℝ)))⁻¹ = (((1:ℝ)/9)) := by norm_num
  have hle2 : ((1:ℝ)/9) - ((1:ℝ)/9) ^ 3 / 3 + ((1:ℝ)/9) ^ 5 / 5 - ((1:ℝ)/9) ^ 7 / 7 ≤ Real.arctan (((1:ℝ)/9)) := arctan_ge3 (((1:ℝ)/9)) (by positivity)
  have hpi : Real.pi / 2 ≤ ((3927:ℝ)/2500) := by
    have h := Real.pi_lt_d4
    norm_num at h
    linarith
  calc
    Real.arctan ((9:ℝ)) = Real.pi / 2 - Real.arctan ((((9:ℝ)))⁻¹) := hrec'
    _ ≤ ((3927:ℝ)/2500) - Real.arctan ((((9:ℝ)))⁻¹) := sub_le_sub_right hpi _
    _ ≤ ((3927:ℝ)/2500) - (((1:ℝ)/9) - ((1:ℝ)/9) ^ 3 / 3 + ((1:ℝ)/9) ^ 5 / 5 - ((1:ℝ)/9) ^ 7 / 7) := by
      have hconv2 : Real.arctan ((((9:ℝ)))⁻¹) = Real.arctan (((1:ℝ)/9)) := by rw [hconv]
      rw [hconv2]
      exact sub_le_sub_left hle2 (((3927:ℝ)/2500) : ℝ)
    _ = ((122216808841:ℝ)/83701957500) := by norm_num

private lemma vatan_ub_m10 : Real.arctan ((10:ℝ)) ≤ ((308937583:ℝ)/210000000) := by
  have hpos : 0 < ((10:ℝ)) := by norm_num
  have hrec := Real.arctan_inv_of_pos hpos
  have hrec' : Real.arctan ((10:ℝ)) = Real.pi / 2 - Real.arctan ((((10:ℝ)))⁻¹) := by
    linarith
  have hconv : (((10:ℝ)))⁻¹ = (((1:ℝ)/10)) := by norm_num
  have hle2 : ((1:ℝ)/10) - ((1:ℝ)/10) ^ 3 / 3 + ((1:ℝ)/10) ^ 5 / 5 - ((1:ℝ)/10) ^ 7 / 7 ≤ Real.arctan (((1:ℝ)/10)) := arctan_ge3 (((1:ℝ)/10)) (by positivity)
  have hpi : Real.pi / 2 ≤ ((3927:ℝ)/2500) := by
    have h := Real.pi_lt_d4
    norm_num at h
    linarith
  calc
    Real.arctan ((10:ℝ)) = Real.pi / 2 - Real.arctan ((((10:ℝ)))⁻¹) := hrec'
    _ ≤ ((3927:ℝ)/2500) - Real.arctan ((((10:ℝ)))⁻¹) := sub_le_sub_right hpi _
    _ ≤ ((3927:ℝ)/2500) - (((1:ℝ)/10) - ((1:ℝ)/10) ^ 3 / 3 + ((1:ℝ)/10) ^ 5 / 5 - ((1:ℝ)/10) ^ 7 / 7) := by
      have hconv2 : Real.arctan ((((10:ℝ)))⁻¹) = Real.arctan (((1:ℝ)/10)) := by rw [hconv]
      rw [hconv2]
      exact sub_le_sub_left hle2 (((3927:ℝ)/2500) : ℝ)
    _ = ((308937583:ℝ)/210000000) := by norm_num

private lemma vatan_ub_m65_6 : Real.arctan (((65:ℝ)/6)) ≤ ((202977178351209:ℝ)/137262380937500) := by
  have hpos : 0 < (((65:ℝ)/6)) := by norm_num
  have hrec := Real.arctan_inv_of_pos hpos
  have hrec' : Real.arctan (((65:ℝ)/6)) = Real.pi / 2 - Real.arctan (((((65:ℝ)/6)))⁻¹) := by
    linarith
  have hconv : ((((65:ℝ)/6)))⁻¹ = (((6:ℝ)/65)) := by norm_num
  have hle2 : ((6:ℝ)/65) - ((6:ℝ)/65) ^ 3 / 3 + ((6:ℝ)/65) ^ 5 / 5 - ((6:ℝ)/65) ^ 7 / 7 ≤ Real.arctan (((6:ℝ)/65)) := arctan_ge3 (((6:ℝ)/65)) (by positivity)
  have hpi : Real.pi / 2 ≤ ((3927:ℝ)/2500) := by
    have h := Real.pi_lt_d4
    norm_num at h
    linarith
  calc
    Real.arctan (((65:ℝ)/6)) = Real.pi / 2 - Real.arctan (((((65:ℝ)/6)))⁻¹) := hrec'
    _ ≤ ((3927:ℝ)/2500) - Real.arctan (((((65:ℝ)/6)))⁻¹) := sub_le_sub_right hpi _
    _ ≤ ((3927:ℝ)/2500) - (((6:ℝ)/65) - ((6:ℝ)/65) ^ 3 / 3 + ((6:ℝ)/65) ^ 5 / 5 - ((6:ℝ)/65) ^ 7 / 7) := by
      have hconv2 : Real.arctan (((((65:ℝ)/6)))⁻¹) = Real.arctan (((6:ℝ)/65)) := by rw [hconv]
      rw [hconv2]
      exact sub_le_sub_left hle2 (((3927:ℝ)/2500) : ℝ)
    _ = ((202977178351209:ℝ)/137262380937500) := by norm_num

private lemma vatan_ub_m25_2 : Real.arctan (((25:ℝ)/2)) ≤ ((764413337411:ℝ)/512695312500) := by
  have hpos : 0 < (((25:ℝ)/2)) := by norm_num
  have hrec := Real.arctan_inv_of_pos hpos
  have hrec' : Real.arctan (((25:ℝ)/2)) = Real.pi / 2 - Real.arctan (((((25:ℝ)/2)))⁻¹) := by
    linarith
  have hconv : ((((25:ℝ)/2)))⁻¹ = (((2:ℝ)/25)) := by norm_num
  have hle2 : ((2:ℝ)/25) - ((2:ℝ)/25) ^ 3 / 3 + ((2:ℝ)/25) ^ 5 / 5 - ((2:ℝ)/25) ^ 7 / 7 ≤ Real.arctan (((2:ℝ)/25)) := arctan_ge3 (((2:ℝ)/25)) (by positivity)
  have hpi : Real.pi / 2 ≤ ((3927:ℝ)/2500) := by
    have h := Real.pi_lt_d4
    norm_num at h
    linarith
  calc
    Real.arctan (((25:ℝ)/2)) = Real.pi / 2 - Real.arctan (((((25:ℝ)/2)))⁻¹) := hrec'
    _ ≤ ((3927:ℝ)/2500) - Real.arctan (((((25:ℝ)/2)))⁻¹) := sub_le_sub_right hpi _
    _ ≤ ((3927:ℝ)/2500) - (((2:ℝ)/25) - ((2:ℝ)/25) ^ 3 / 3 + ((2:ℝ)/25) ^ 5 / 5 - ((2:ℝ)/25) ^ 7 / 7) := by
      have hconv2 : Real.arctan (((((25:ℝ)/2)))⁻¹) = Real.arctan (((2:ℝ)/25)) := by rw [hconv]
      rw [hconv2]
      exact sub_le_sub_left hle2 (((3927:ℝ)/2500) : ℝ)
    _ = ((764413337411:ℝ)/512695312500) := by norm_num

private lemma vatan_ub_m13 : Real.arctan ((13:ℝ)) ≤ ((4921772529439:ℝ)/3294297142500) := by
  have hpos : 0 < ((13:ℝ)) := by norm_num
  have hrec := Real.arctan_inv_of_pos hpos
  have hrec' : Real.arctan ((13:ℝ)) = Real.pi / 2 - Real.arctan ((((13:ℝ)))⁻¹) := by
    linarith
  have hconv : (((13:ℝ)))⁻¹ = (((1:ℝ)/13)) := by norm_num
  have hle2 : ((1:ℝ)/13) - ((1:ℝ)/13) ^ 3 / 3 + ((1:ℝ)/13) ^ 5 / 5 - ((1:ℝ)/13) ^ 7 / 7 ≤ Real.arctan (((1:ℝ)/13)) := arctan_ge3 (((1:ℝ)/13)) (by positivity)
  have hpi : Real.pi / 2 ≤ ((3927:ℝ)/2500) := by
    have h := Real.pi_lt_d4
    norm_num at h
    linarith
  calc
    Real.arctan ((13:ℝ)) = Real.pi / 2 - Real.arctan ((((13:ℝ)))⁻¹) := hrec'
    _ ≤ ((3927:ℝ)/2500) - Real.arctan ((((13:ℝ)))⁻¹) := sub_le_sub_right hpi _
    _ ≤ ((3927:ℝ)/2500) - (((1:ℝ)/13) - ((1:ℝ)/13) ^ 3 / 3 + ((1:ℝ)/13) ^ 5 / 5 - ((1:ℝ)/13) ^ 7 / 7) := by
      have hconv2 : Real.arctan ((((13:ℝ)))⁻¹) = Real.arctan (((1:ℝ)/13)) := by rw [hconv]
      rw [hconv2]
      exact sub_le_sub_left hle2 (((3927:ℝ)/2500) : ℝ)
    _ = ((4921772529439:ℝ)/3294297142500) := by norm_num

private lemma vatan_ub_m15 : Real.arctan ((15:ℝ)) ≤ ((7196339119:ℝ)/4784062500) := by
  have hpos : 0 < ((15:ℝ)) := by norm_num
  have hrec := Real.arctan_inv_of_pos hpos
  have hrec' : Real.arctan ((15:ℝ)) = Real.pi / 2 - Real.arctan ((((15:ℝ)))⁻¹) := by
    linarith
  have hconv : (((15:ℝ)))⁻¹ = (((1:ℝ)/15)) := by norm_num
  have hle2 : ((1:ℝ)/15) - ((1:ℝ)/15) ^ 3 / 3 + ((1:ℝ)/15) ^ 5 / 5 - ((1:ℝ)/15) ^ 7 / 7 ≤ Real.arctan (((1:ℝ)/15)) := arctan_ge3 (((1:ℝ)/15)) (by positivity)
  have hpi : Real.pi / 2 ≤ ((3927:ℝ)/2500) := by
    have h := Real.pi_lt_d4
    norm_num at h
    linarith
  calc
    Real.arctan ((15:ℝ)) = Real.pi / 2 - Real.arctan ((((15:ℝ)))⁻¹) := hrec'
    _ ≤ ((3927:ℝ)/2500) - Real.arctan ((((15:ℝ)))⁻¹) := sub_le_sub_right hpi _
    _ ≤ ((3927:ℝ)/2500) - (((1:ℝ)/15) - ((1:ℝ)/15) ^ 3 / 3 + ((1:ℝ)/15) ^ 5 / 5 - ((1:ℝ)/15) ^ 7 / 7) := by
      have hconv2 : Real.arctan ((((15:ℝ)))⁻¹) = Real.arctan (((1:ℝ)/15)) := by rw [hconv]
      rw [hconv2]
      exact sub_le_sub_left hle2 (((3927:ℝ)/2500) : ℝ)
    _ = ((7196339119:ℝ)/4784062500) := by norm_num

private lemma vlog_lb_m2 : ((6931471803:ℝ)/10000000000) ≤ Real.log (2:ℝ) := by
  have hdec : (2:ℝ) = (2:ℝ)^(1) * (1 + (0:ℝ)) := by norm_num
  have harg' : 1 + (0:ℝ) ≠ 0 := by norm_num
  have h1 : (1:ℝ) * ((6931471803:ℝ)/10000000000) ≤ (1:ℝ) * Real.log 2 := by
    have hb : ((6931471803:ℝ)/10000000000) ≤ Real.log 2 := by
      have h := log_two_gt_d9
      norm_num at h ⊢
      linarith
    exact mul_le_mul_of_nonneg_left hb (by norm_num)
  have h2 : (0:ℝ) - (0:ℝ) ^ 2 / 2 + (0:ℝ) ^ 3 / 3 - (0:ℝ) ^ 4 / 4 + (0:ℝ) ^ 5 / 5 - (0:ℝ) ^ 6 / 6 + (0:ℝ) ^ 7 / 7 - (0:ℝ) ^ 8 / 8 ≤ Real.log (1 + (0:ℝ)) := log_one_add_ge7 (0:ℝ) (by norm_num)
  have hlogq : Real.log (2:ℝ) = (1:ℝ) * Real.log 2 + Real.log (1 + (0:ℝ)) := by
    rw [hdec]
    rw [Real.log_mul (by positivity : (2:ℝ)^(1) ≠ 0) harg']
    rw [Real.log_pow]
    norm_num
  calc
    ((6931471803:ℝ)/10000000000) = (1:ℝ) * ((6931471803:ℝ)/10000000000) + (0:ℝ) - (0:ℝ) ^ 2 / 2 + (0:ℝ) ^ 3 / 3 - (0:ℝ) ^ 4 / 4 + (0:ℝ) ^ 5 / 5 - (0:ℝ) ^ 6 / 6 + (0:ℝ) ^ 7 / 7 - (0:ℝ) ^ 8 / 8 := by norm_num
    _ ≤ (1:ℝ) * Real.log 2 + Real.log (1 + (0:ℝ)) := by
      nlinarith
    _ = Real.log (2:ℝ) := by rw [← hlogq]

private lemma vlog_lb_m61_25 : ((5853736396217449:ℝ)/6562500000000000) ≤ Real.log ((61:ℝ)/25) := by
  have hdec : ((61:ℝ)/25) = (2:ℝ)^(1) * (1 + ((11:ℝ)/50)) := by norm_num
  have harg' : 1 + ((11:ℝ)/50) ≠ 0 := by norm_num
  have h1 : (1:ℝ) * ((6931471803:ℝ)/10000000000) ≤ (1:ℝ) * Real.log 2 := by
    have hb : ((6931471803:ℝ)/10000000000) ≤ Real.log 2 := by
      have h := log_two_gt_d9
      norm_num at h ⊢
      linarith
    exact mul_le_mul_of_nonneg_left hb (by norm_num)
  have h2 : ((11:ℝ)/50) - ((11:ℝ)/50) ^ 2 / 2 + ((11:ℝ)/50) ^ 3 / 3 - ((11:ℝ)/50) ^ 4 / 4 + ((11:ℝ)/50) ^ 5 / 5 - ((11:ℝ)/50) ^ 6 / 6 + ((11:ℝ)/50) ^ 7 / 7 - ((11:ℝ)/50) ^ 8 / 8 ≤ Real.log (1 + ((11:ℝ)/50)) := log_one_add_ge7 ((11:ℝ)/50) (by norm_num)
  have hlogq : Real.log ((61:ℝ)/25) = (1:ℝ) * Real.log 2 + Real.log (1 + ((11:ℝ)/50)) := by
    rw [hdec]
    rw [Real.log_mul (by positivity : (2:ℝ)^(1) ≠ 0) harg']
    rw [Real.log_pow]
    norm_num
  calc
    ((5853736396217449:ℝ)/6562500000000000) = (1:ℝ) * ((6931471803:ℝ)/10000000000) + ((11:ℝ)/50) - ((11:ℝ)/50) ^ 2 / 2 + ((11:ℝ)/50) ^ 3 / 3 - ((11:ℝ)/50) ^ 4 / 4 + ((11:ℝ)/50) ^ 5 / 5 - ((11:ℝ)/50) ^ 6 / 6 + ((11:ℝ)/50) ^ 7 / 7 - ((11:ℝ)/50) ^ 8 / 8 := by norm_num
    _ ≤ (1:ℝ) * Real.log 2 + Real.log (1 + ((11:ℝ)/50)) := by
      nlinarith
    _ = Real.log ((61:ℝ)/25) := by rw [← hlogq]

private lemma vlog_lb_m3 : ((153784745867:ℝ)/140000000000) ≤ Real.log (3:ℝ) := by
  have hdec : (3:ℝ) = (2:ℝ)^(1) * (1 + ((1:ℝ)/2)) := by norm_num
  have harg' : 1 + ((1:ℝ)/2) ≠ 0 := by norm_num
  have h1 : (1:ℝ) * ((6931471803:ℝ)/10000000000) ≤ (1:ℝ) * Real.log 2 := by
    have hb : ((6931471803:ℝ)/10000000000) ≤ Real.log 2 := by
      have h := log_two_gt_d9
      norm_num at h ⊢
      linarith
    exact mul_le_mul_of_nonneg_left hb (by norm_num)
  have h2 : ((1:ℝ)/2) - ((1:ℝ)/2) ^ 2 / 2 + ((1:ℝ)/2) ^ 3 / 3 - ((1:ℝ)/2) ^ 4 / 4 + ((1:ℝ)/2) ^ 5 / 5 - ((1:ℝ)/2) ^ 6 / 6 + ((1:ℝ)/2) ^ 7 / 7 - ((1:ℝ)/2) ^ 8 / 8 ≤ Real.log (1 + ((1:ℝ)/2)) := log_one_add_ge7 ((1:ℝ)/2) (by norm_num)
  have hlogq : Real.log (3:ℝ) = (1:ℝ) * Real.log 2 + Real.log (1 + ((1:ℝ)/2)) := by
    rw [hdec]
    rw [Real.log_mul (by positivity : (2:ℝ)^(1) ≠ 0) harg']
    rw [Real.log_pow]
    norm_num
  calc
    ((153784745867:ℝ)/140000000000) = (1:ℝ) * ((6931471803:ℝ)/10000000000) + ((1:ℝ)/2) - ((1:ℝ)/2) ^ 2 / 2 + ((1:ℝ)/2) ^ 3 / 3 - ((1:ℝ)/2) ^ 4 / 4 + ((1:ℝ)/2) ^ 5 / 5 - ((1:ℝ)/2) ^ 6 / 6 + ((1:ℝ)/2) ^ 7 / 7 - ((1:ℝ)/2) ^ 8 / 8 := by norm_num
    _ ≤ (1:ℝ) * Real.log 2 + Real.log (1 + ((1:ℝ)/2)) := by
      nlinarith
    _ = Real.log (3:ℝ) := by rw [← hlogq]

private lemma vlog_lb_m13_4 : ((10814198157545049:ℝ)/9175040000000000) ≤ Real.log ((13:ℝ)/4) := by
  have hdec : ((13:ℝ)/4) = (2:ℝ)^(2) * (1 - ((3:ℝ)/16)) := by norm_num
  have harg' : 1 - ((3:ℝ)/16) ≠ 0 := by norm_num
  have h1 : (2:ℝ) * ((6931471803:ℝ)/10000000000) ≤ (2:ℝ) * Real.log 2 := by
    have hb : ((6931471803:ℝ)/10000000000) ≤ Real.log 2 := by
      have h := log_two_gt_d9
      norm_num at h ⊢
      linarith
    exact mul_le_mul_of_nonneg_left hb (by norm_num)
  have h2 : -( ((3:ℝ)/16) + ((3:ℝ)/16) ^ 2 / 2 + ((3:ℝ)/16) ^ 3 / 3 + ((3:ℝ)/16) ^ 4 / 4 + ((3:ℝ)/16) ^ 5 / 5 + ((3:ℝ)/16) ^ 6 / 6 ) - 2 * ((3:ℝ)/16) ^ 7 / 7 ≤ Real.log (1 - ((3:ℝ)/16)) := log_one_sub_ge6 ((3:ℝ)/16) (by norm_num) (by norm_num : ((3:ℝ)/16) ≤ (1:ℝ)/2)
  have hlogq : Real.log ((13:ℝ)/4) = (2:ℝ) * Real.log 2 + Real.log (1 - ((3:ℝ)/16)) := by
    rw [hdec]
    rw [Real.log_mul (by positivity : (2:ℝ)^(2) ≠ 0) harg']
    rw [Real.log_pow]
    norm_num
  calc
    ((10814198157545049:ℝ)/9175040000000000) = (2:ℝ) * ((6931471803:ℝ)/10000000000) + -( ((3:ℝ)/16) + ((3:ℝ)/16) ^ 2 / 2 + ((3:ℝ)/16) ^ 3 / 3 + ((3:ℝ)/16) ^ 4 / 4 + ((3:ℝ)/16) ^ 5 / 5 + ((3:ℝ)/16) ^ 6 / 6 ) - 2 * ((3:ℝ)/16) ^ 7 / 7 := by norm_num
    _ ≤ (2:ℝ) * Real.log 2 + Real.log (1 - ((3:ℝ)/16)) := by
      nlinarith
    _ = Real.log ((13:ℝ)/4) := by rw [← hlogq]

private lemma vlog_lb_m7_2 : ((269394135787799:ℝ)/215040000000000) ≤ Real.log ((7:ℝ)/2) := by
  have hdec : ((7:ℝ)/2) = (2:ℝ)^(2) * (1 - ((1:ℝ)/8)) := by norm_num
  have harg' : 1 - ((1:ℝ)/8) ≠ 0 := by norm_num
  have h1 : (2:ℝ) * ((6931471803:ℝ)/10000000000) ≤ (2:ℝ) * Real.log 2 := by
    have hb : ((6931471803:ℝ)/10000000000) ≤ Real.log 2 := by
      have h := log_two_gt_d9
      norm_num at h ⊢
      linarith
    exact mul_le_mul_of_nonneg_left hb (by norm_num)
  have h2 : -( ((1:ℝ)/8) + ((1:ℝ)/8) ^ 2 / 2 + ((1:ℝ)/8) ^ 3 / 3 + ((1:ℝ)/8) ^ 4 / 4 + ((1:ℝ)/8) ^ 5 / 5 + ((1:ℝ)/8) ^ 6 / 6 ) - 2 * ((1:ℝ)/8) ^ 7 / 7 ≤ Real.log (1 - ((1:ℝ)/8)) := log_one_sub_ge6 ((1:ℝ)/8) (by norm_num) (by norm_num : ((1:ℝ)/8) ≤ (1:ℝ)/2)
  have hlogq : Real.log ((7:ℝ)/2) = (2:ℝ) * Real.log 2 + Real.log (1 - ((1:ℝ)/8)) := by
    rw [hdec]
    rw [Real.log_mul (by positivity : (2:ℝ)^(2) ≠ 0) harg']
    rw [Real.log_pow]
    norm_num
  calc
    ((269394135787799:ℝ)/215040000000000) = (2:ℝ) * ((6931471803:ℝ)/10000000000) + -( ((1:ℝ)/8) + ((1:ℝ)/8) ^ 2 / 2 + ((1:ℝ)/8) ^ 3 / 3 + ((1:ℝ)/8) ^ 4 / 4 + ((1:ℝ)/8) ^ 5 / 5 + ((1:ℝ)/8) ^ 6 / 6 ) - 2 * ((1:ℝ)/8) ^ 7 / 7 := by norm_num
    _ ≤ (2:ℝ) * Real.log 2 + Real.log (1 - ((1:ℝ)/8)) := by
      nlinarith
    _ = Real.log ((7:ℝ)/2) := by rw [← hlogq]

private lemma vlog_lb_m369_100 : ((7486984345320254989:ℝ)/5734400000000000000) ≤ Real.log ((369:ℝ)/100) := by
  have hdec : ((369:ℝ)/100) = (2:ℝ)^(2) * (1 - ((31:ℝ)/400)) := by norm_num
  have harg' : 1 - ((31:ℝ)/400) ≠ 0 := by norm_num
  have h1 : (2:ℝ) * ((6931471803:ℝ)/10000000000) ≤ (2:ℝ) * Real.log 2 := by
    have hb : ((6931471803:ℝ)/10000000000) ≤ Real.log 2 := by
      have h := log_two_gt_d9
      norm_num at h ⊢
      linarith
    exact mul_le_mul_of_nonneg_left hb (by norm_num)
  have h2 : -( ((31:ℝ)/400) + ((31:ℝ)/400) ^ 2 / 2 + ((31:ℝ)/400) ^ 3 / 3 + ((31:ℝ)/400) ^ 4 / 4 + ((31:ℝ)/400) ^ 5 / 5 + ((31:ℝ)/400) ^ 6 / 6 ) - 2 * ((31:ℝ)/400) ^ 7 / 7 ≤ Real.log (1 - ((31:ℝ)/400)) := log_one_sub_ge6 ((31:ℝ)/400) (by norm_num) (by norm_num : ((31:ℝ)/400) ≤ (1:ℝ)/2)
  have hlogq : Real.log ((369:ℝ)/100) = (2:ℝ) * Real.log 2 + Real.log (1 - ((31:ℝ)/400)) := by
    rw [hdec]
    rw [Real.log_mul (by positivity : (2:ℝ)^(2) ≠ 0) harg']
    rw [Real.log_pow]
    norm_num
  calc
    ((7486984345320254989:ℝ)/5734400000000000000) = (2:ℝ) * ((6931471803:ℝ)/10000000000) + -( ((31:ℝ)/400) + ((31:ℝ)/400) ^ 2 / 2 + ((31:ℝ)/400) ^ 3 / 3 + ((31:ℝ)/400) ^ 4 / 4 + ((31:ℝ)/400) ^ 5 / 5 + ((31:ℝ)/400) ^ 6 / 6 ) - 2 * ((31:ℝ)/400) ^ 7 / 7 := by norm_num
    _ ≤ (2:ℝ) * Real.log 2 + Real.log (1 - ((31:ℝ)/400)) := by
      nlinarith
    _ = Real.log ((369:ℝ)/100) := by rw [← hlogq]

private lemma vlog_lb_m4 : ((6931471803:ℝ)/5000000000) ≤ Real.log (4:ℝ) := by
  have hdec : (4:ℝ) = (2:ℝ)^(2) * (1 + (0:ℝ)) := by norm_num
  have harg' : 1 + (0:ℝ) ≠ 0 := by norm_num
  have h1 : (2:ℝ) * ((6931471803:ℝ)/10000000000) ≤ (2:ℝ) * Real.log 2 := by
    have hb : ((6931471803:ℝ)/10000000000) ≤ Real.log 2 := by
      have h := log_two_gt_d9
      norm_num at h ⊢
      linarith
    exact mul_le_mul_of_nonneg_left hb (by norm_num)
  have h2 : (0:ℝ) - (0:ℝ) ^ 2 / 2 + (0:ℝ) ^ 3 / 3 - (0:ℝ) ^ 4 / 4 + (0:ℝ) ^ 5 / 5 - (0:ℝ) ^ 6 / 6 + (0:ℝ) ^ 7 / 7 - (0:ℝ) ^ 8 / 8 ≤ Real.log (1 + (0:ℝ)) := log_one_add_ge7 (0:ℝ) (by norm_num)
  have hlogq : Real.log (4:ℝ) = (2:ℝ) * Real.log 2 + Real.log (1 + (0:ℝ)) := by
    rw [hdec]
    rw [Real.log_mul (by positivity : (2:ℝ)^(2) ≠ 0) harg']
    rw [Real.log_pow]
    norm_num
  calc
    ((6931471803:ℝ)/5000000000) = (2:ℝ) * ((6931471803:ℝ)/10000000000) + (0:ℝ) - (0:ℝ) ^ 2 / 2 + (0:ℝ) ^ 3 / 3 - (0:ℝ) ^ 4 / 4 + (0:ℝ) ^ 5 / 5 - (0:ℝ) ^ 6 / 6 + (0:ℝ) ^ 7 / 7 - (0:ℝ) ^ 8 / 8 := by norm_num
    _ ≤ (2:ℝ) * Real.log 2 + Real.log (1 + (0:ℝ)) := by
      nlinarith
    _ = Real.log (4:ℝ) := by rw [← hlogq]

private lemma vlog_lb_m9_2 : ((13799970266920049:ℝ)/9175040000000000) ≤ Real.log ((9:ℝ)/2) := by
  have hdec : ((9:ℝ)/2) = (2:ℝ)^(2) * (1 + ((1:ℝ)/8)) := by norm_num
  have harg' : 1 + ((1:ℝ)/8) ≠ 0 := by norm_num
  have h1 : (2:ℝ) * ((6931471803:ℝ)/10000000000) ≤ (2:ℝ) * Real.log 2 := by
    have hb : ((6931471803:ℝ)/10000000000) ≤ Real.log 2 := by
      have h := log_two_gt_d9
      norm_num at h ⊢
      linarith
    exact mul_le_mul_of_nonneg_left hb (by norm_num)
  have h2 : ((1:ℝ)/8) - ((1:ℝ)/8) ^ 2 / 2 + ((1:ℝ)/8) ^ 3 / 3 - ((1:ℝ)/8) ^ 4 / 4 + ((1:ℝ)/8) ^ 5 / 5 - ((1:ℝ)/8) ^ 6 / 6 + ((1:ℝ)/8) ^ 7 / 7 - ((1:ℝ)/8) ^ 8 / 8 ≤ Real.log (1 + ((1:ℝ)/8)) := log_one_add_ge7 ((1:ℝ)/8) (by norm_num)
  have hlogq : Real.log ((9:ℝ)/2) = (2:ℝ) * Real.log 2 + Real.log (1 + ((1:ℝ)/8)) := by
    rw [hdec]
    rw [Real.log_mul (by positivity : (2:ℝ)^(2) ≠ 0) harg']
    rw [Real.log_pow]
    norm_num
  calc
    ((13799970266920049:ℝ)/9175040000000000) = (2:ℝ) * ((6931471803:ℝ)/10000000000) + ((1:ℝ)/8) - ((1:ℝ)/8) ^ 2 / 2 + ((1:ℝ)/8) ^ 3 / 3 - ((1:ℝ)/8) ^ 4 / 4 + ((1:ℝ)/8) ^ 5 / 5 - ((1:ℝ)/8) ^ 6 / 6 + ((1:ℝ)/8) ^ 7 / 7 - ((1:ℝ)/8) ^ 8 / 8 := by norm_num
    _ ≤ (2:ℝ) * Real.log 2 + Real.log (1 + ((1:ℝ)/8)) := by
      nlinarith
    _ = Real.log ((9:ℝ)/2) := by rw [← hlogq]

private lemma vlog_lb_m5 : ((173046727073587:ℝ)/107520000000000) ≤ Real.log (5:ℝ) := by
  have hdec : (5:ℝ) = (2:ℝ)^(2) * (1 + ((1:ℝ)/4)) := by norm_num
  have harg' : 1 + ((1:ℝ)/4) ≠ 0 := by norm_num
  have h1 : (2:ℝ) * ((6931471803:ℝ)/10000000000) ≤ (2:ℝ) * Real.log 2 := by
    have hb : ((6931471803:ℝ)/10000000000) ≤ Real.log 2 := by
      have h := log_two_gt_d9
      norm_num at h ⊢
      linarith
    exact mul_le_mul_of_nonneg_left hb (by norm_num)
  have h2 : ((1:ℝ)/4) - ((1:ℝ)/4) ^ 2 / 2 + ((1:ℝ)/4) ^ 3 / 3 - ((1:ℝ)/4) ^ 4 / 4 + ((1:ℝ)/4) ^ 5 / 5 - ((1:ℝ)/4) ^ 6 / 6 + ((1:ℝ)/4) ^ 7 / 7 - ((1:ℝ)/4) ^ 8 / 8 ≤ Real.log (1 + ((1:ℝ)/4)) := log_one_add_ge7 ((1:ℝ)/4) (by norm_num)
  have hlogq : Real.log (5:ℝ) = (2:ℝ) * Real.log 2 + Real.log (1 + ((1:ℝ)/4)) := by
    rw [hdec]
    rw [Real.log_mul (by positivity : (2:ℝ)^(2) ≠ 0) harg']
    rw [Real.log_pow]
    norm_num
  calc
    ((173046727073587:ℝ)/107520000000000) = (2:ℝ) * ((6931471803:ℝ)/10000000000) + ((1:ℝ)/4) - ((1:ℝ)/4) ^ 2 / 2 + ((1:ℝ)/4) ^ 3 / 3 - ((1:ℝ)/4) ^ 4 / 4 + ((1:ℝ)/4) ^ 5 / 5 - ((1:ℝ)/4) ^ 6 / 6 + ((1:ℝ)/4) ^ 7 / 7 - ((1:ℝ)/4) ^ 8 / 8 := by norm_num
    _ ≤ (2:ℝ) * Real.log 2 + Real.log (1 + ((1:ℝ)/4)) := by
      nlinarith
    _ = Real.log (5:ℝ) := by rw [← hlogq]

private lemma vlog_lb_m136_25 : ((926280759685317:ℝ)/546875000000000) ≤ Real.log ((136:ℝ)/25) := by
  have hdec : ((136:ℝ)/25) = (2:ℝ)^(2) * (1 + ((9:ℝ)/25)) := by norm_num
  have harg' : 1 + ((9:ℝ)/25) ≠ 0 := by norm_num
  have h1 : (2:ℝ) * ((6931471803:ℝ)/10000000000) ≤ (2:ℝ) * Real.log 2 := by
    have hb : ((6931471803:ℝ)/10000000000) ≤ Real.log 2 := by
      have h := log_two_gt_d9
      norm_num at h ⊢
      linarith
    exact mul_le_mul_of_nonneg_left hb (by norm_num)
  have h2 : ((9:ℝ)/25) - ((9:ℝ)/25) ^ 2 / 2 + ((9:ℝ)/25) ^ 3 / 3 - ((9:ℝ)/25) ^ 4 / 4 + ((9:ℝ)/25) ^ 5 / 5 - ((9:ℝ)/25) ^ 6 / 6 + ((9:ℝ)/25) ^ 7 / 7 - ((9:ℝ)/25) ^ 8 / 8 ≤ Real.log (1 + ((9:ℝ)/25)) := log_one_add_ge7 ((9:ℝ)/25) (by norm_num)
  have hlogq : Real.log ((136:ℝ)/25) = (2:ℝ) * Real.log 2 + Real.log (1 + ((9:ℝ)/25)) := by
    rw [hdec]
    rw [Real.log_mul (by positivity : (2:ℝ)^(2) ≠ 0) harg']
    rw [Real.log_pow]
    norm_num
  calc
    ((926280759685317:ℝ)/546875000000000) = (2:ℝ) * ((6931471803:ℝ)/10000000000) + ((9:ℝ)/25) - ((9:ℝ)/25) ^ 2 / 2 + ((9:ℝ)/25) ^ 3 / 3 - ((9:ℝ)/25) ^ 4 / 4 + ((9:ℝ)/25) ^ 5 / 5 - ((9:ℝ)/25) ^ 6 / 6 + ((9:ℝ)/25) ^ 7 / 7 - ((9:ℝ)/25) ^ 8 / 8 := by norm_num
    _ ≤ (2:ℝ) * Real.log 2 + Real.log (1 + ((9:ℝ)/25)) := by
      nlinarith
    _ = Real.log ((136:ℝ)/25) := by rw [← hlogq]

private lemma vlog_lb_m6 : ((250825351109:ℝ)/140000000000) ≤ Real.log (6:ℝ) := by
  have hdec : (6:ℝ) = (2:ℝ)^(2) * (1 + ((1:ℝ)/2)) := by norm_num
  have harg' : 1 + ((1:ℝ)/2) ≠ 0 := by norm_num
  have h1 : (2:ℝ) * ((6931471803:ℝ)/10000000000) ≤ (2:ℝ) * Real.log 2 := by
    have hb : ((6931471803:ℝ)/10000000000) ≤ Real.log 2 := by
      have h := log_two_gt_d9
      norm_num at h ⊢
      linarith
    exact mul_le_mul_of_nonneg_left hb (by norm_num)
  have h2 : ((1:ℝ)/2) - ((1:ℝ)/2) ^ 2 / 2 + ((1:ℝ)/2) ^ 3 / 3 - ((1:ℝ)/2) ^ 4 / 4 + ((1:ℝ)/2) ^ 5 / 5 - ((1:ℝ)/2) ^ 6 / 6 + ((1:ℝ)/2) ^ 7 / 7 - ((1:ℝ)/2) ^ 8 / 8 ≤ Real.log (1 + ((1:ℝ)/2)) := log_one_add_ge7 ((1:ℝ)/2) (by norm_num)
  have hlogq : Real.log (6:ℝ) = (2:ℝ) * Real.log 2 + Real.log (1 + ((1:ℝ)/2)) := by
    rw [hdec]
    rw [Real.log_mul (by positivity : (2:ℝ)^(2) ≠ 0) harg']
    rw [Real.log_pow]
    norm_num
  calc
    ((250825351109:ℝ)/140000000000) = (2:ℝ) * ((6931471803:ℝ)/10000000000) + ((1:ℝ)/2) - ((1:ℝ)/2) ^ 2 / 2 + ((1:ℝ)/2) ^ 3 / 3 - ((1:ℝ)/2) ^ 4 / 4 + ((1:ℝ)/2) ^ 5 / 5 - ((1:ℝ)/2) ^ 6 / 6 + ((1:ℝ)/2) ^ 7 / 7 - ((1:ℝ)/2) ^ 8 / 8 := by norm_num
    _ ≤ (2:ℝ) * Real.log 2 + Real.log (1 + ((1:ℝ)/2)) := by
      nlinarith
    _ = Real.log (6:ℝ) := by rw [← hlogq]

private lemma vlog_lb_m25_4 : ((922367137655392157:ℝ)/503316480000000000) ≤ Real.log ((25:ℝ)/4) := by
  have hdec : ((25:ℝ)/4) = (2:ℝ)^(3) * (1 - ((7:ℝ)/32)) := by norm_num
  have harg' : 1 - ((7:ℝ)/32) ≠ 0 := by norm_num
  have h1 : (3:ℝ) * ((6931471803:ℝ)/10000000000) ≤ (3:ℝ) * Real.log 2 := by
    have hb : ((6931471803:ℝ)/10000000000) ≤ Real.log 2 := by
      have h := log_two_gt_d9
      norm_num at h ⊢
      linarith
    exact mul_le_mul_of_nonneg_left hb (by norm_num)
  have h2 : -( ((7:ℝ)/32) + ((7:ℝ)/32) ^ 2 / 2 + ((7:ℝ)/32) ^ 3 / 3 + ((7:ℝ)/32) ^ 4 / 4 + ((7:ℝ)/32) ^ 5 / 5 + ((7:ℝ)/32) ^ 6 / 6 ) - 2 * ((7:ℝ)/32) ^ 7 / 7 ≤ Real.log (1 - ((7:ℝ)/32)) := log_one_sub_ge6 ((7:ℝ)/32) (by norm_num) (by norm_num : ((7:ℝ)/32) ≤ (1:ℝ)/2)
  have hlogq : Real.log ((25:ℝ)/4) = (3:ℝ) * Real.log 2 + Real.log (1 - ((7:ℝ)/32)) := by
    rw [hdec]
    rw [Real.log_mul (by positivity : (2:ℝ)^(3) ≠ 0) harg']
    rw [Real.log_pow]
    norm_num
  calc
    ((922367137655392157:ℝ)/503316480000000000) = (3:ℝ) * ((6931471803:ℝ)/10000000000) + -( ((7:ℝ)/32) + ((7:ℝ)/32) ^ 2 / 2 + ((7:ℝ)/32) ^ 3 / 3 + ((7:ℝ)/32) ^ 4 / 4 + ((7:ℝ)/32) ^ 5 / 5 + ((7:ℝ)/32) ^ 6 / 6 ) - 2 * ((7:ℝ)/32) ^ 7 / 7 := by norm_num
    _ ≤ (3:ℝ) * Real.log 2 + Real.log (1 - ((7:ℝ)/32)) := by
      nlinarith
    _ = Real.log ((25:ℝ)/4) := by rw [← hlogq]

private lemma vlog_lb_m29_4 : ((2326498257125602533:ℝ)/1174405120000000000) ≤ Real.log ((29:ℝ)/4) := by
  have hdec : ((29:ℝ)/4) = (2:ℝ)^(3) * (1 - ((3:ℝ)/32)) := by norm_num
  have harg' : 1 - ((3:ℝ)/32) ≠ 0 := by norm_num
  have h1 : (3:ℝ) * ((6931471803:ℝ)/10000000000) ≤ (3:ℝ) * Real.log 2 := by
    have hb : ((6931471803:ℝ)/10000000000) ≤ Real.log 2 := by
      have h := log_two_gt_d9
      norm_num at h ⊢
      linarith
    exact mul_le_mul_of_nonneg_left hb (by norm_num)
  have h2 : -( ((3:ℝ)/32) + ((3:ℝ)/32) ^ 2 / 2 + ((3:ℝ)/32) ^ 3 / 3 + ((3:ℝ)/32) ^ 4 / 4 + ((3:ℝ)/32) ^ 5 / 5 + ((3:ℝ)/32) ^ 6 / 6 ) - 2 * ((3:ℝ)/32) ^ 7 / 7 ≤ Real.log (1 - ((3:ℝ)/32)) := log_one_sub_ge6 ((3:ℝ)/32) (by norm_num) (by norm_num : ((3:ℝ)/32) ≤ (1:ℝ)/2)
  have hlogq : Real.log ((29:ℝ)/4) = (3:ℝ) * Real.log 2 + Real.log (1 - ((3:ℝ)/32)) := by
    rw [hdec]
    rw [Real.log_mul (by positivity : (2:ℝ)^(3) ≠ 0) harg']
    rw [Real.log_pow]
    norm_num
  calc
    ((2326498257125602533:ℝ)/1174405120000000000) = (3:ℝ) * ((6931471803:ℝ)/10000000000) + -( ((3:ℝ)/32) + ((3:ℝ)/32) ^ 2 / 2 + ((3:ℝ)/32) ^ 3 / 3 + ((3:ℝ)/32) ^ 4 / 4 + ((3:ℝ)/32) ^ 5 / 5 + ((3:ℝ)/32) ^ 6 / 6 ) - 2 * ((3:ℝ)/32) ^ 7 / 7 := by norm_num
    _ ≤ (3:ℝ) * Real.log 2 + Real.log (1 - ((3:ℝ)/32)) := by
      nlinarith
    _ = Real.log ((29:ℝ)/4) := by rw [← hlogq]

private lemma vlog_lb_m8 : ((20794415409:ℝ)/10000000000) ≤ Real.log (8:ℝ) := by
  have hdec : (8:ℝ) = (2:ℝ)^(3) * (1 + (0:ℝ)) := by norm_num
  have harg' : 1 + (0:ℝ) ≠ 0 := by norm_num
  have h1 : (3:ℝ) * ((6931471803:ℝ)/10000000000) ≤ (3:ℝ) * Real.log 2 := by
    have hb : ((6931471803:ℝ)/10000000000) ≤ Real.log 2 := by
      have h := log_two_gt_d9
      norm_num at h ⊢
      linarith
    exact mul_le_mul_of_nonneg_left hb (by norm_num)
  have h2 : (0:ℝ) - (0:ℝ) ^ 2 / 2 + (0:ℝ) ^ 3 / 3 - (0:ℝ) ^ 4 / 4 + (0:ℝ) ^ 5 / 5 - (0:ℝ) ^ 6 / 6 + (0:ℝ) ^ 7 / 7 - (0:ℝ) ^ 8 / 8 ≤ Real.log (1 + (0:ℝ)) := log_one_add_ge7 (0:ℝ) (by norm_num)
  have hlogq : Real.log (8:ℝ) = (3:ℝ) * Real.log 2 + Real.log (1 + (0:ℝ)) := by
    rw [hdec]
    rw [Real.log_mul (by positivity : (2:ℝ)^(3) ≠ 0) harg']
    rw [Real.log_pow]
    norm_num
  calc
    ((20794415409:ℝ)/10000000000) = (3:ℝ) * ((6931471803:ℝ)/10000000000) + (0:ℝ) - (0:ℝ) ^ 2 / 2 + (0:ℝ) ^ 3 / 3 - (0:ℝ) ^ 4 / 4 + (0:ℝ) ^ 5 / 5 - (0:ℝ) ^ 6 / 6 + (0:ℝ) ^ 7 / 7 - (0:ℝ) ^ 8 / 8 := by norm_num
    _ ≤ (3:ℝ) * Real.log 2 + Real.log (1 + (0:ℝ)) := by
      nlinarith
    _ = Real.log (8:ℝ) := by rw [← hlogq]

private lemma vlog_lb_m17_2 : ((15079827951786818323:ℝ)/7046430720000000000) ≤ Real.log ((17:ℝ)/2) := by
  have hdec : ((17:ℝ)/2) = (2:ℝ)^(3) * (1 + ((1:ℝ)/16)) := by norm_num
  have harg' : 1 + ((1:ℝ)/16) ≠ 0 := by norm_num
  have h1 : (3:ℝ) * ((6931471803:ℝ)/10000000000) ≤ (3:ℝ) * Real.log 2 := by
    have hb : ((6931471803:ℝ)/10000000000) ≤ Real.log 2 := by
      have h := log_two_gt_d9
      norm_num at h ⊢
      linarith
    exact mul_le_mul_of_nonneg_left hb (by norm_num)
  have h2 : ((1:ℝ)/16) - ((1:ℝ)/16) ^ 2 / 2 + ((1:ℝ)/16) ^ 3 / 3 - ((1:ℝ)/16) ^ 4 / 4 + ((1:ℝ)/16) ^ 5 / 5 - ((1:ℝ)/16) ^ 6 / 6 + ((1:ℝ)/16) ^ 7 / 7 - ((1:ℝ)/16) ^ 8 / 8 ≤ Real.log (1 + ((1:ℝ)/16)) := log_one_add_ge7 ((1:ℝ)/16) (by norm_num)
  have hlogq : Real.log ((17:ℝ)/2) = (3:ℝ) * Real.log 2 + Real.log (1 + ((1:ℝ)/16)) := by
    rw [hdec]
    rw [Real.log_mul (by positivity : (2:ℝ)^(3) ≠ 0) harg']
    rw [Real.log_pow]
    norm_num
  calc
    ((15079827951786818323:ℝ)/7046430720000000000) = (3:ℝ) * ((6931471803:ℝ)/10000000000) + ((1:ℝ)/16) - ((1:ℝ)/16) ^ 2 / 2 + ((1:ℝ)/16) ^ 3 / 3 - ((1:ℝ)/16) ^ 4 / 4 + ((1:ℝ)/16) ^ 5 / 5 - ((1:ℝ)/16) ^ 6 / 6 + ((1:ℝ)/16) ^ 7 / 7 - ((1:ℝ)/16) ^ 8 / 8 := by norm_num
    _ ≤ (3:ℝ) * Real.log 2 + Real.log (1 + ((1:ℝ)/16)) := by
      nlinarith
    _ = Real.log ((17:ℝ)/2) := by rw [← hlogq]

private lemma vlog_lb_m10 : ((247573911899443:ℝ)/107520000000000) ≤ Real.log (10:ℝ) := by
  have hdec : (10:ℝ) = (2:ℝ)^(3) * (1 + ((1:ℝ)/4)) := by norm_num
  have harg' : 1 + ((1:ℝ)/4) ≠ 0 := by norm_num
  have h1 : (3:ℝ) * ((6931471803:ℝ)/10000000000) ≤ (3:ℝ) * Real.log 2 := by
    have hb : ((6931471803:ℝ)/10000000000) ≤ Real.log 2 := by
      have h := log_two_gt_d9
      norm_num at h ⊢
      linarith
    exact mul_le_mul_of_nonneg_left hb (by norm_num)
  have h2 : ((1:ℝ)/4) - ((1:ℝ)/4) ^ 2 / 2 + ((1:ℝ)/4) ^ 3 / 3 - ((1:ℝ)/4) ^ 4 / 4 + ((1:ℝ)/4) ^ 5 / 5 - ((1:ℝ)/4) ^ 6 / 6 + ((1:ℝ)/4) ^ 7 / 7 - ((1:ℝ)/4) ^ 8 / 8 ≤ Real.log (1 + ((1:ℝ)/4)) := log_one_add_ge7 ((1:ℝ)/4) (by norm_num)
  have hlogq : Real.log (10:ℝ) = (3:ℝ) * Real.log 2 + Real.log (1 + ((1:ℝ)/4)) := by
    rw [hdec]
    rw [Real.log_mul (by positivity : (2:ℝ)^(3) ≠ 0) harg']
    rw [Real.log_pow]
    norm_num
  calc
    ((247573911899443:ℝ)/107520000000000) = (3:ℝ) * ((6931471803:ℝ)/10000000000) + ((1:ℝ)/4) - ((1:ℝ)/4) ^ 2 / 2 + ((1:ℝ)/4) ^ 3 / 3 - ((1:ℝ)/4) ^ 4 / 4 + ((1:ℝ)/4) ^ 5 / 5 - ((1:ℝ)/4) ^ 6 / 6 + ((1:ℝ)/4) ^ 7 / 7 - ((1:ℝ)/4) ^ 8 / 8 := by norm_num
    _ ≤ (3:ℝ) * Real.log 2 + Real.log (1 + ((1:ℝ)/4)) := by
      nlinarith
    _ = Real.log (10:ℝ) := by rw [← hlogq]

private lemma vlog_lb_m41_4 : ((1399380841006865137521:ℝ)/601295421440000000000) ≤ Real.log ((41:ℝ)/4) := by
  have hdec : ((41:ℝ)/4) = (2:ℝ)^(3) * (1 + ((9:ℝ)/32)) := by norm_num
  have harg' : 1 + ((9:ℝ)/32) ≠ 0 := by norm_num
  have h1 : (3:ℝ) * ((6931471803:ℝ)/10000000000) ≤ (3:ℝ) * Real.log 2 := by
    have hb : ((6931471803:ℝ)/10000000000) ≤ Real.log 2 := by
      have h := log_two_gt_d9
      norm_num at h ⊢
      linarith
    exact mul_le_mul_of_nonneg_left hb (by norm_num)
  have h2 : ((9:ℝ)/32) - ((9:ℝ)/32) ^ 2 / 2 + ((9:ℝ)/32) ^ 3 / 3 - ((9:ℝ)/32) ^ 4 / 4 + ((9:ℝ)/32) ^ 5 / 5 - ((9:ℝ)/32) ^ 6 / 6 + ((9:ℝ)/32) ^ 7 / 7 - ((9:ℝ)/32) ^ 8 / 8 ≤ Real.log (1 + ((9:ℝ)/32)) := log_one_add_ge7 ((9:ℝ)/32) (by norm_num)
  have hlogq : Real.log ((41:ℝ)/4) = (3:ℝ) * Real.log 2 + Real.log (1 + ((9:ℝ)/32)) := by
    rw [hdec]
    rw [Real.log_mul (by positivity : (2:ℝ)^(3) ≠ 0) harg']
    rw [Real.log_pow]
    norm_num
  calc
    ((1399380841006865137521:ℝ)/601295421440000000000) = (3:ℝ) * ((6931471803:ℝ)/10000000000) + ((9:ℝ)/32) - ((9:ℝ)/32) ^ 2 / 2 + ((9:ℝ)/32) ^ 3 / 3 - ((9:ℝ)/32) ^ 4 / 4 + ((9:ℝ)/32) ^ 5 / 5 - ((9:ℝ)/32) ^ 6 / 6 + ((9:ℝ)/32) ^ 7 / 7 - ((9:ℝ)/32) ^ 8 / 8 := by norm_num
    _ ≤ (3:ℝ) * Real.log 2 + Real.log (1 + ((9:ℝ)/32)) := by
      nlinarith
    _ = Real.log ((41:ℝ)/4) := by rw [← hlogq]

private lemma vlog_lb_m261_25 : ((336271321631178812633:ℝ)/143360000000000000000) ≤ Real.log ((261:ℝ)/25) := by
  have hdec : ((261:ℝ)/25) = (2:ℝ)^(3) * (1 + ((61:ℝ)/200)) := by norm_num
  have harg' : 1 + ((61:ℝ)/200) ≠ 0 := by norm_num
  have h1 : (3:ℝ) * ((6931471803:ℝ)/10000000000) ≤ (3:ℝ) * Real.log 2 := by
    have hb : ((6931471803:ℝ)/10000000000) ≤ Real.log 2 := by
      have h := log_two_gt_d9
      norm_num at h ⊢
      linarith
    exact mul_le_mul_of_nonneg_left hb (by norm_num)
  have h2 : ((61:ℝ)/200) - ((61:ℝ)/200) ^ 2 / 2 + ((61:ℝ)/200) ^ 3 / 3 - ((61:ℝ)/200) ^ 4 / 4 + ((61:ℝ)/200) ^ 5 / 5 - ((61:ℝ)/200) ^ 6 / 6 + ((61:ℝ)/200) ^ 7 / 7 - ((61:ℝ)/200) ^ 8 / 8 ≤ Real.log (1 + ((61:ℝ)/200)) := log_one_add_ge7 ((61:ℝ)/200) (by norm_num)
  have hlogq : Real.log ((261:ℝ)/25) = (3:ℝ) * Real.log 2 + Real.log (1 + ((61:ℝ)/200)) := by
    rw [hdec]
    rw [Real.log_mul (by positivity : (2:ℝ)^(3) ≠ 0) harg']
    rw [Real.log_pow]
    norm_num
  calc
    ((336271321631178812633:ℝ)/143360000000000000000) = (3:ℝ) * ((6931471803:ℝ)/10000000000) + ((61:ℝ)/200) - ((61:ℝ)/200) ^ 2 / 2 + ((61:ℝ)/200) ^ 3 / 3 - ((61:ℝ)/200) ^ 4 / 4 + ((61:ℝ)/200) ^ 5 / 5 - ((61:ℝ)/200) ^ 6 / 6 + ((61:ℝ)/200) ^ 7 / 7 - ((61:ℝ)/200) ^ 8 / 8 := by norm_num
    _ ≤ (3:ℝ) * Real.log 2 + Real.log (1 + ((61:ℝ)/200)) := by
      nlinarith
    _ = Real.log ((261:ℝ)/25) := by rw [← hlogq]

private lemma vlog_lb_m11 : ((22000673184559761:ℝ)/9175040000000000) ≤ Real.log (11:ℝ) := by
  have hdec : (11:ℝ) = (2:ℝ)^(3) * (1 + ((3:ℝ)/8)) := by norm_num
  have harg' : 1 + ((3:ℝ)/8) ≠ 0 := by norm_num
  have h1 : (3:ℝ) * ((6931471803:ℝ)/10000000000) ≤ (3:ℝ) * Real.log 2 := by
    have hb : ((6931471803:ℝ)/10000000000) ≤ Real.log 2 := by
      have h := log_two_gt_d9
      norm_num at h ⊢
      linarith
    exact mul_le_mul_of_nonneg_left hb (by norm_num)
  have h2 : ((3:ℝ)/8) - ((3:ℝ)/8) ^ 2 / 2 + ((3:ℝ)/8) ^ 3 / 3 - ((3:ℝ)/8) ^ 4 / 4 + ((3:ℝ)/8) ^ 5 / 5 - ((3:ℝ)/8) ^ 6 / 6 + ((3:ℝ)/8) ^ 7 / 7 - ((3:ℝ)/8) ^ 8 / 8 ≤ Real.log (1 + ((3:ℝ)/8)) := log_one_add_ge7 ((3:ℝ)/8) (by norm_num)
  have hlogq : Real.log (11:ℝ) = (3:ℝ) * Real.log 2 + Real.log (1 + ((3:ℝ)/8)) := by
    rw [hdec]
    rw [Real.log_mul (by positivity : (2:ℝ)^(3) ≠ 0) harg']
    rw [Real.log_pow]
    norm_num
  calc
    ((22000673184559761:ℝ)/9175040000000000) = (3:ℝ) * ((6931471803:ℝ)/10000000000) + ((3:ℝ)/8) - ((3:ℝ)/8) ^ 2 / 2 + ((3:ℝ)/8) ^ 3 / 3 - ((3:ℝ)/8) ^ 4 / 4 + ((3:ℝ)/8) ^ 5 / 5 - ((3:ℝ)/8) ^ 6 / 6 + ((3:ℝ)/8) ^ 7 / 7 - ((3:ℝ)/8) ^ 8 / 8 := by norm_num
    _ ≤ (3:ℝ) * Real.log 2 + Real.log (1 + ((3:ℝ)/8)) := by
      nlinarith
    _ = Real.log (11:ℝ) := by rw [← hlogq]

private lemma vlog_lb_m45_4 : ((1455341517017552637521:ℝ)/601295421440000000000) ≤ Real.log ((45:ℝ)/4) := by
  have hdec : ((45:ℝ)/4) = (2:ℝ)^(3) * (1 + ((13:ℝ)/32)) := by norm_num
  have harg' : 1 + ((13:ℝ)/32) ≠ 0 := by norm_num
  have h1 : (3:ℝ) * ((6931471803:ℝ)/10000000000) ≤ (3:ℝ) * Real.log 2 := by
    have hb : ((6931471803:ℝ)/10000000000) ≤ Real.log 2 := by
      have h := log_two_gt_d9
      norm_num at h ⊢
      linarith
    exact mul_le_mul_of_nonneg_left hb (by norm_num)
  have h2 : ((13:ℝ)/32) - ((13:ℝ)/32) ^ 2 / 2 + ((13:ℝ)/32) ^ 3 / 3 - ((13:ℝ)/32) ^ 4 / 4 + ((13:ℝ)/32) ^ 5 / 5 - ((13:ℝ)/32) ^ 6 / 6 + ((13:ℝ)/32) ^ 7 / 7 - ((13:ℝ)/32) ^ 8 / 8 ≤ Real.log (1 + ((13:ℝ)/32)) := log_one_add_ge7 ((13:ℝ)/32) (by norm_num)
  have hlogq : Real.log ((45:ℝ)/4) = (3:ℝ) * Real.log 2 + Real.log (1 + ((13:ℝ)/32)) := by
    rw [hdec]
    rw [Real.log_mul (by positivity : (2:ℝ)^(3) ≠ 0) harg']
    rw [Real.log_pow]
    norm_num
  calc
    ((1455341517017552637521:ℝ)/601295421440000000000) = (3:ℝ) * ((6931471803:ℝ)/10000000000) + ((13:ℝ)/32) - ((13:ℝ)/32) ^ 2 / 2 + ((13:ℝ)/32) ^ 3 / 3 - ((13:ℝ)/32) ^ 4 / 4 + ((13:ℝ)/32) ^ 5 / 5 - ((13:ℝ)/32) ^ 6 / 6 + ((13:ℝ)/32) ^ 7 / 7 - ((13:ℝ)/32) ^ 8 / 8 := by norm_num
    _ ≤ (3:ℝ) * Real.log 2 + Real.log (1 + ((13:ℝ)/32)) := by
      nlinarith
    _ = Real.log ((45:ℝ)/4) := by rw [← hlogq]

private lemma vlog_lb_m13 : ((23533504367824473:ℝ)/9175040000000000) ≤ Real.log (13:ℝ) := by
  have hdec : (13:ℝ) = (2:ℝ)^(4) * (1 - ((3:ℝ)/16)) := by norm_num
  have harg' : 1 - ((3:ℝ)/16) ≠ 0 := by norm_num
  have h1 : (4:ℝ) * ((6931471803:ℝ)/10000000000) ≤ (4:ℝ) * Real.log 2 := by
    have hb : ((6931471803:ℝ)/10000000000) ≤ Real.log 2 := by
      have h := log_two_gt_d9
      norm_num at h ⊢
      linarith
    exact mul_le_mul_of_nonneg_left hb (by norm_num)
  have h2 : -( ((3:ℝ)/16) + ((3:ℝ)/16) ^ 2 / 2 + ((3:ℝ)/16) ^ 3 / 3 + ((3:ℝ)/16) ^ 4 / 4 + ((3:ℝ)/16) ^ 5 / 5 + ((3:ℝ)/16) ^ 6 / 6 ) - 2 * ((3:ℝ)/16) ^ 7 / 7 ≤ Real.log (1 - ((3:ℝ)/16)) := log_one_sub_ge6 ((3:ℝ)/16) (by norm_num) (by norm_num : ((3:ℝ)/16) ≤ (1:ℝ)/2)
  have hlogq : Real.log (13:ℝ) = (4:ℝ) * Real.log 2 + Real.log (1 - ((3:ℝ)/16)) := by
    rw [hdec]
    rw [Real.log_mul (by positivity : (2:ℝ)^(4) ≠ 0) harg']
    rw [Real.log_pow]
    norm_num
  calc
    ((23533504367824473:ℝ)/9175040000000000) = (4:ℝ) * ((6931471803:ℝ)/10000000000) + -( ((3:ℝ)/16) + ((3:ℝ)/16) ^ 2 / 2 + ((3:ℝ)/16) ^ 3 / 3 + ((3:ℝ)/16) ^ 4 / 4 + ((3:ℝ)/16) ^ 5 / 5 + ((3:ℝ)/16) ^ 6 / 6 ) - 2 * ((3:ℝ)/16) ^ 7 / 7 := by norm_num
    _ ≤ (4:ℝ) * Real.log 2 + Real.log (1 - ((3:ℝ)/16)) := by
      nlinarith
    _ = Real.log (13:ℝ) := by rw [← hlogq]

private lemma vlog_lb_m15 : ((24846468902980723:ℝ)/9175040000000000) ≤ Real.log (15:ℝ) := by
  have hdec : (15:ℝ) = (2:ℝ)^(4) * (1 - ((1:ℝ)/16)) := by norm_num
  have harg' : 1 - ((1:ℝ)/16) ≠ 0 := by norm_num
  have h1 : (4:ℝ) * ((6931471803:ℝ)/10000000000) ≤ (4:ℝ) * Real.log 2 := by
    have hb : ((6931471803:ℝ)/10000000000) ≤ Real.log 2 := by
      have h := log_two_gt_d9
      norm_num at h ⊢
      linarith
    exact mul_le_mul_of_nonneg_left hb (by norm_num)
  have h2 : -( ((1:ℝ)/16) + ((1:ℝ)/16) ^ 2 / 2 + ((1:ℝ)/16) ^ 3 / 3 + ((1:ℝ)/16) ^ 4 / 4 + ((1:ℝ)/16) ^ 5 / 5 + ((1:ℝ)/16) ^ 6 / 6 ) - 2 * ((1:ℝ)/16) ^ 7 / 7 ≤ Real.log (1 - ((1:ℝ)/16)) := log_one_sub_ge6 ((1:ℝ)/16) (by norm_num) (by norm_num : ((1:ℝ)/16) ≤ (1:ℝ)/2)
  have hlogq : Real.log (15:ℝ) = (4:ℝ) * Real.log 2 + Real.log (1 - ((1:ℝ)/16)) := by
    rw [hdec]
    rw [Real.log_mul (by positivity : (2:ℝ)^(4) ≠ 0) harg']
    rw [Real.log_pow]
    norm_num
  calc
    ((24846468902980723:ℝ)/9175040000000000) = (4:ℝ) * ((6931471803:ℝ)/10000000000) + -( ((1:ℝ)/16) + ((1:ℝ)/16) ^ 2 / 2 + ((1:ℝ)/16) ^ 3 / 3 + ((1:ℝ)/16) ^ 4 / 4 + ((1:ℝ)/16) ^ 5 / 5 + ((1:ℝ)/16) ^ 6 / 6 ) - 2 * ((1:ℝ)/16) ^ 7 / 7 := by norm_num
    _ ≤ (4:ℝ) * Real.log 2 + Real.log (1 - ((1:ℝ)/16)) := by
      nlinarith
    _ = Real.log (15:ℝ) := by rw [← hlogq]

private lemma vlog_lb_m61_4 : ((409569294967297493757:ℝ)/150323855360000000000) ≤ Real.log ((61:ℝ)/4) := by
  have hdec : ((61:ℝ)/4) = (2:ℝ)^(4) * (1 - ((3:ℝ)/64)) := by norm_num
  have harg' : 1 - ((3:ℝ)/64) ≠ 0 := by norm_num
  have h1 : (4:ℝ) * ((6931471803:ℝ)/10000000000) ≤ (4:ℝ) * Real.log 2 := by
    have hb : ((6931471803:ℝ)/10000000000) ≤ Real.log 2 := by
      have h := log_two_gt_d9
      norm_num at h ⊢
      linarith
    exact mul_le_mul_of_nonneg_left hb (by norm_num)
  have h2 : -( ((3:ℝ)/64) + ((3:ℝ)/64) ^ 2 / 2 + ((3:ℝ)/64) ^ 3 / 3 + ((3:ℝ)/64) ^ 4 / 4 + ((3:ℝ)/64) ^ 5 / 5 + ((3:ℝ)/64) ^ 6 / 6 ) - 2 * ((3:ℝ)/64) ^ 7 / 7 ≤ Real.log (1 - ((3:ℝ)/64)) := log_one_sub_ge6 ((3:ℝ)/64) (by norm_num) (by norm_num : ((3:ℝ)/64) ≤ (1:ℝ)/2)
  have hlogq : Real.log ((61:ℝ)/4) = (4:ℝ) * Real.log 2 + Real.log (1 - ((3:ℝ)/64)) := by
    rw [hdec]
    rw [Real.log_mul (by positivity : (2:ℝ)^(4) ≠ 0) harg']
    rw [Real.log_pow]
    norm_num
  calc
    ((409569294967297493757:ℝ)/150323855360000000000) = (4:ℝ) * ((6931471803:ℝ)/10000000000) + -( ((3:ℝ)/64) + ((3:ℝ)/64) ^ 2 / 2 + ((3:ℝ)/64) ^ 3 / 3 + ((3:ℝ)/64) ^ 4 / 4 + ((3:ℝ)/64) ^ 5 / 5 + ((3:ℝ)/64) ^ 6 / 6 ) - 2 * ((3:ℝ)/64) ^ 7 / 7 := by norm_num
    _ ≤ (4:ℝ) * Real.log 2 + Real.log (1 - ((3:ℝ)/64)) := by
      nlinarith
    _ = Real.log ((61:ℝ)/4) := by rw [← hlogq]

private lemma vlog_lb_m17 : ((19964041536534117139:ℝ)/7046430720000000000) ≤ Real.log (17:ℝ) := by
  have hdec : (17:ℝ) = (2:ℝ)^(4) * (1 + ((1:ℝ)/16)) := by norm_num
  have harg' : 1 + ((1:ℝ)/16) ≠ 0 := by norm_num
  have h1 : (4:ℝ) * ((6931471803:ℝ)/10000000000) ≤ (4:ℝ) * Real.log 2 := by
    have hb : ((6931471803:ℝ)/10000000000) ≤ Real.log 2 := by
      have h := log_two_gt_d9
      norm_num at h ⊢
      linarith
    exact mul_le_mul_of_nonneg_left hb (by norm_num)
  have h2 : ((1:ℝ)/16) - ((1:ℝ)/16) ^ 2 / 2 + ((1:ℝ)/16) ^ 3 / 3 - ((1:ℝ)/16) ^ 4 / 4 + ((1:ℝ)/16) ^ 5 / 5 - ((1:ℝ)/16) ^ 6 / 6 + ((1:ℝ)/16) ^ 7 / 7 - ((1:ℝ)/16) ^ 8 / 8 ≤ Real.log (1 + ((1:ℝ)/16)) := log_one_add_ge7 ((1:ℝ)/16) (by norm_num)
  have hlogq : Real.log (17:ℝ) = (4:ℝ) * Real.log 2 + Real.log (1 + ((1:ℝ)/16)) := by
    rw [hdec]
    rw [Real.log_mul (by positivity : (2:ℝ)^(4) ≠ 0) harg']
    rw [Real.log_pow]
    norm_num
  calc
    ((19964041536534117139:ℝ)/7046430720000000000) = (4:ℝ) * ((6931471803:ℝ)/10000000000) + ((1:ℝ)/16) - ((1:ℝ)/16) ^ 2 / 2 + ((1:ℝ)/16) ^ 3 / 3 - ((1:ℝ)/16) ^ 4 / 4 + ((1:ℝ)/16) ^ 5 / 5 - ((1:ℝ)/16) ^ 6 / 6 + ((1:ℝ)/16) ^ 7 / 7 - ((1:ℝ)/16) ^ 8 / 8 := by norm_num
    _ ≤ (4:ℝ) * Real.log 2 + Real.log (1 + ((1:ℝ)/16)) := by
      nlinarith
    _ = Real.log (17:ℝ) := by rw [← hlogq]

private lemma vlog_lb_m436_25 : ((1600909193744688153:ℝ)/560000000000000000) ≤ Real.log ((436:ℝ)/25) := by
  have hdec : ((436:ℝ)/25) = (2:ℝ)^(4) * (1 + ((9:ℝ)/100)) := by norm_num
  have harg' : 1 + ((9:ℝ)/100) ≠ 0 := by norm_num
  have h1 : (4:ℝ) * ((6931471803:ℝ)/10000000000) ≤ (4:ℝ) * Real.log 2 := by
    have hb : ((6931471803:ℝ)/10000000000) ≤ Real.log 2 := by
      have h := log_two_gt_d9
      norm_num at h ⊢
      linarith
    exact mul_le_mul_of_nonneg_left hb (by norm_num)
  have h2 : ((9:ℝ)/100) - ((9:ℝ)/100) ^ 2 / 2 + ((9:ℝ)/100) ^ 3 / 3 - ((9:ℝ)/100) ^ 4 / 4 + ((9:ℝ)/100) ^ 5 / 5 - ((9:ℝ)/100) ^ 6 / 6 + ((9:ℝ)/100) ^ 7 / 7 - ((9:ℝ)/100) ^ 8 / 8 ≤ Real.log (1 + ((9:ℝ)/100)) := log_one_add_ge7 ((9:ℝ)/100) (by norm_num)
  have hlogq : Real.log ((436:ℝ)/25) = (4:ℝ) * Real.log 2 + Real.log (1 + ((9:ℝ)/100)) := by
    rw [hdec]
    rw [Real.log_mul (by positivity : (2:ℝ)^(4) ≠ 0) harg']
    rw [Real.log_pow]
    norm_num
  calc
    ((1600909193744688153:ℝ)/560000000000000000) = (4:ℝ) * ((6931471803:ℝ)/10000000000) + ((9:ℝ)/100) - ((9:ℝ)/100) ^ 2 / 2 + ((9:ℝ)/100) ^ 3 / 3 - ((9:ℝ)/100) ^ 4 / 4 + ((9:ℝ)/100) ^ 5 / 5 - ((9:ℝ)/100) ^ 6 / 6 + ((9:ℝ)/100) ^ 7 / 7 - ((9:ℝ)/100) ^ 8 / 8 := by norm_num
    _ ≤ (4:ℝ) * Real.log 2 + Real.log (1 + ((9:ℝ)/100)) := by
      nlinarith
    _ = Real.log ((436:ℝ)/25) := by rw [← hlogq]

private lemma vlog_lb_m18 : ((26519276477199473:ℝ)/9175040000000000) ≤ Real.log (18:ℝ) := by
  have hdec : (18:ℝ) = (2:ℝ)^(4) * (1 + ((1:ℝ)/8)) := by norm_num
  have harg' : 1 + ((1:ℝ)/8) ≠ 0 := by norm_num
  have h1 : (4:ℝ) * ((6931471803:ℝ)/10000000000) ≤ (4:ℝ) * Real.log 2 := by
    have hb : ((6931471803:ℝ)/10000000000) ≤ Real.log 2 := by
      have h := log_two_gt_d9
      norm_num at h ⊢
      linarith
    exact mul_le_mul_of_nonneg_left hb (by norm_num)
  have h2 : ((1:ℝ)/8) - ((1:ℝ)/8) ^ 2 / 2 + ((1:ℝ)/8) ^ 3 / 3 - ((1:ℝ)/8) ^ 4 / 4 + ((1:ℝ)/8) ^ 5 / 5 - ((1:ℝ)/8) ^ 6 / 6 + ((1:ℝ)/8) ^ 7 / 7 - ((1:ℝ)/8) ^ 8 / 8 ≤ Real.log (1 + ((1:ℝ)/8)) := log_one_add_ge7 ((1:ℝ)/8) (by norm_num)
  have hlogq : Real.log (18:ℝ) = (4:ℝ) * Real.log 2 + Real.log (1 + ((1:ℝ)/8)) := by
    rw [hdec]
    rw [Real.log_mul (by positivity : (2:ℝ)^(4) ≠ 0) harg']
    rw [Real.log_pow]
    norm_num
  calc
    ((26519276477199473:ℝ)/9175040000000000) = (4:ℝ) * ((6931471803:ℝ)/10000000000) + ((1:ℝ)/8) - ((1:ℝ)/8) ^ 2 / 2 + ((1:ℝ)/8) ^ 3 / 3 - ((1:ℝ)/8) ^ 4 / 4 + ((1:ℝ)/8) ^ 5 / 5 - ((1:ℝ)/8) ^ 6 / 6 + ((1:ℝ)/8) ^ 7 / 7 - ((1:ℝ)/8) ^ 8 / 8 := by norm_num
    _ ≤ (4:ℝ) * Real.log 2 + Real.log (1 + ((1:ℝ)/8)) := by
      nlinarith
    _ = Real.log (18:ℝ) := by rw [← hlogq]

private lemma vlog_lb_m73_4 : ((447042857939524690247793:ℝ)/153931627888640000000000) ≤ Real.log ((73:ℝ)/4) := by
  have hdec : ((73:ℝ)/4) = (2:ℝ)^(4) * (1 + ((9:ℝ)/64)) := by norm_num
  have harg' : 1 + ((9:ℝ)/64) ≠ 0 := by norm_num
  have h1 : (4:ℝ) * ((6931471803:ℝ)/10000000000) ≤ (4:ℝ) * Real.log 2 := by
    have hb : ((6931471803:ℝ)/10000000000) ≤ Real.log 2 := by
      have h := log_two_gt_d9
      norm_num at h ⊢
      linarith
    exact mul_le_mul_of_nonneg_left hb (by norm_num)
  have h2 : ((9:ℝ)/64) - ((9:ℝ)/64) ^ 2 / 2 + ((9:ℝ)/64) ^ 3 / 3 - ((9:ℝ)/64) ^ 4 / 4 + ((9:ℝ)/64) ^ 5 / 5 - ((9:ℝ)/64) ^ 6 / 6 + ((9:ℝ)/64) ^ 7 / 7 - ((9:ℝ)/64) ^ 8 / 8 ≤ Real.log (1 + ((9:ℝ)/64)) := log_one_add_ge7 ((9:ℝ)/64) (by norm_num)
  have hlogq : Real.log ((73:ℝ)/4) = (4:ℝ) * Real.log 2 + Real.log (1 + ((9:ℝ)/64)) := by
    rw [hdec]
    rw [Real.log_mul (by positivity : (2:ℝ)^(4) ≠ 0) harg']
    rw [Real.log_pow]
    norm_num
  calc
    ((447042857939524690247793:ℝ)/153931627888640000000000) = (4:ℝ) * ((6931471803:ℝ)/10000000000) + ((9:ℝ)/64) - ((9:ℝ)/64) ^ 2 / 2 + ((9:ℝ)/64) ^ 3 / 3 - ((9:ℝ)/64) ^ 4 / 4 + ((9:ℝ)/64) ^ 5 / 5 - ((9:ℝ)/64) ^ 6 / 6 + ((9:ℝ)/64) ^ 7 / 7 - ((9:ℝ)/64) ^ 8 / 8 := by norm_num
    _ ≤ (4:ℝ) * Real.log 2 + Real.log (1 + ((9:ℝ)/64)) := by
      nlinarith
    _ = Real.log ((73:ℝ)/4) := by rw [← hlogq]

private lemma vlog_lb_m20 : ((322101096725299:ℝ)/107520000000000) ≤ Real.log (20:ℝ) := by
  have hdec : (20:ℝ) = (2:ℝ)^(4) * (1 + ((1:ℝ)/4)) := by norm_num
  have harg' : 1 + ((1:ℝ)/4) ≠ 0 := by norm_num
  have h1 : (4:ℝ) * ((6931471803:ℝ)/10000000000) ≤ (4:ℝ) * Real.log 2 := by
    have hb : ((6931471803:ℝ)/10000000000) ≤ Real.log 2 := by
      have h := log_two_gt_d9
      norm_num at h ⊢
      linarith
    exact mul_le_mul_of_nonneg_left hb (by norm_num)
  have h2 : ((1:ℝ)/4) - ((1:ℝ)/4) ^ 2 / 2 + ((1:ℝ)/4) ^ 3 / 3 - ((1:ℝ)/4) ^ 4 / 4 + ((1:ℝ)/4) ^ 5 / 5 - ((1:ℝ)/4) ^ 6 / 6 + ((1:ℝ)/4) ^ 7 / 7 - ((1:ℝ)/4) ^ 8 / 8 ≤ Real.log (1 + ((1:ℝ)/4)) := log_one_add_ge7 ((1:ℝ)/4) (by norm_num)
  have hlogq : Real.log (20:ℝ) = (4:ℝ) * Real.log 2 + Real.log (1 + ((1:ℝ)/4)) := by
    rw [hdec]
    rw [Real.log_mul (by positivity : (2:ℝ)^(4) ≠ 0) harg']
    rw [Real.log_pow]
    norm_num
  calc
    ((322101096725299:ℝ)/107520000000000) = (4:ℝ) * ((6931471803:ℝ)/10000000000) + ((1:ℝ)/4) - ((1:ℝ)/4) ^ 2 / 2 + ((1:ℝ)/4) ^ 3 / 3 - ((1:ℝ)/4) ^ 4 / 4 + ((1:ℝ)/4) ^ 5 / 5 - ((1:ℝ)/4) ^ 6 / 6 + ((1:ℝ)/4) ^ 7 / 7 - ((1:ℝ)/4) ^ 8 / 8 := by norm_num
    _ ≤ (4:ℝ) * Real.log 2 + Real.log (1 + ((1:ℝ)/4)) := by
      nlinarith
    _ = Real.log (20:ℝ) := by rw [← hlogq]

private lemma vlog_lb_m89_4 : ((1432637621587863820743379:ℝ)/461794883665920000000000) ≤ Real.log ((89:ℝ)/4) := by
  have hdec : ((89:ℝ)/4) = (2:ℝ)^(4) * (1 + ((25:ℝ)/64)) := by norm_num
  have harg' : 1 + ((25:ℝ)/64) ≠ 0 := by norm_num
  have h1 : (4:ℝ) * ((6931471803:ℝ)/10000000000) ≤ (4:ℝ) * Real.log 2 := by
    have hb : ((6931471803:ℝ)/10000000000) ≤ Real.log 2 := by
      have h := log_two_gt_d9
      norm_num at h ⊢
      linarith
    exact mul_le_mul_of_nonneg_left hb (by norm_num)
  have h2 : ((25:ℝ)/64) - ((25:ℝ)/64) ^ 2 / 2 + ((25:ℝ)/64) ^ 3 / 3 - ((25:ℝ)/64) ^ 4 / 4 + ((25:ℝ)/64) ^ 5 / 5 - ((25:ℝ)/64) ^ 6 / 6 + ((25:ℝ)/64) ^ 7 / 7 - ((25:ℝ)/64) ^ 8 / 8 ≤ Real.log (1 + ((25:ℝ)/64)) := log_one_add_ge7 ((25:ℝ)/64) (by norm_num)
  have hlogq : Real.log ((89:ℝ)/4) = (4:ℝ) * Real.log 2 + Real.log (1 + ((25:ℝ)/64)) := by
    rw [hdec]
    rw [Real.log_mul (by positivity : (2:ℝ)^(4) ≠ 0) harg']
    rw [Real.log_pow]
    norm_num
  calc
    ((1432637621587863820743379:ℝ)/461794883665920000000000) = (4:ℝ) * ((6931471803:ℝ)/10000000000) + ((25:ℝ)/64) - ((25:ℝ)/64) ^ 2 / 2 + ((25:ℝ)/64) ^ 3 / 3 - ((25:ℝ)/64) ^ 4 / 4 + ((25:ℝ)/64) ^ 5 / 5 - ((25:ℝ)/64) ^ 6 / 6 + ((25:ℝ)/64) ^ 7 / 7 - ((25:ℝ)/64) ^ 8 / 8 := by norm_num
    _ ≤ (4:ℝ) * Real.log 2 + Real.log (1 + ((25:ℝ)/64)) := by
      nlinarith
    _ = Real.log ((89:ℝ)/4) := by rw [← hlogq]

private lemma vlog_lb_m25 : ((324022387095286969:ℝ)/100663296000000000) ≤ Real.log (25:ℝ) := by
  have hdec : (25:ℝ) = (2:ℝ)^(5) * (1 - ((7:ℝ)/32)) := by norm_num
  have harg' : 1 - ((7:ℝ)/32) ≠ 0 := by norm_num
  have h1 : (5:ℝ) * ((6931471803:ℝ)/10000000000) ≤ (5:ℝ) * Real.log 2 := by
    have hb : ((6931471803:ℝ)/10000000000) ≤ Real.log 2 := by
      have h := log_two_gt_d9
      norm_num at h ⊢
      linarith
    exact mul_le_mul_of_nonneg_left hb (by norm_num)
  have h2 : -( ((7:ℝ)/32) + ((7:ℝ)/32) ^ 2 / 2 + ((7:ℝ)/32) ^ 3 / 3 + ((7:ℝ)/32) ^ 4 / 4 + ((7:ℝ)/32) ^ 5 / 5 + ((7:ℝ)/32) ^ 6 / 6 ) - 2 * ((7:ℝ)/32) ^ 7 / 7 ≤ Real.log (1 - ((7:ℝ)/32)) := log_one_sub_ge6 ((7:ℝ)/32) (by norm_num) (by norm_num : ((7:ℝ)/32) ≤ (1:ℝ)/2)
  have hlogq : Real.log (25:ℝ) = (5:ℝ) * Real.log 2 + Real.log (1 - ((7:ℝ)/32)) := by
    rw [hdec]
    rw [Real.log_mul (by positivity : (2:ℝ)^(5) ≠ 0) harg']
    rw [Real.log_pow]
    norm_num
  calc
    ((324022387095286969:ℝ)/100663296000000000) = (5:ℝ) * ((6931471803:ℝ)/10000000000) + -( ((7:ℝ)/32) + ((7:ℝ)/32) ^ 2 / 2 + ((7:ℝ)/32) ^ 3 / 3 + ((7:ℝ)/32) ^ 4 / 4 + ((7:ℝ)/32) ^ 5 / 5 + ((7:ℝ)/32) ^ 6 / 6 ) - 2 * ((7:ℝ)/32) ^ 7 / 7 := by norm_num
    _ ≤ (5:ℝ) * Real.log 2 + Real.log (1 - ((7:ℝ)/32)) := by
      nlinarith
    _ = Real.log (25:ℝ) := by rw [← hlogq]

private lemma vlog_lb_m32 : ((6931471803:ℝ)/2000000000) ≤ Real.log (32:ℝ) := by
  have hdec : (32:ℝ) = (2:ℝ)^(5) * (1 + (0:ℝ)) := by norm_num
  have harg' : 1 + (0:ℝ) ≠ 0 := by norm_num
  have h1 : (5:ℝ) * ((6931471803:ℝ)/10000000000) ≤ (5:ℝ) * Real.log 2 := by
    have hb : ((6931471803:ℝ)/10000000000) ≤ Real.log 2 := by
      have h := log_two_gt_d9
      norm_num at h ⊢
      linarith
    exact mul_le_mul_of_nonneg_left hb (by norm_num)
  have h2 : (0:ℝ) - (0:ℝ) ^ 2 / 2 + (0:ℝ) ^ 3 / 3 - (0:ℝ) ^ 4 / 4 + (0:ℝ) ^ 5 / 5 - (0:ℝ) ^ 6 / 6 + (0:ℝ) ^ 7 / 7 - (0:ℝ) ^ 8 / 8 ≤ Real.log (1 + (0:ℝ)) := log_one_add_ge7 (0:ℝ) (by norm_num)
  have hlogq : Real.log (32:ℝ) = (5:ℝ) * Real.log 2 + Real.log (1 + (0:ℝ)) := by
    rw [hdec]
    rw [Real.log_mul (by positivity : (2:ℝ)^(5) ≠ 0) harg']
    rw [Real.log_pow]
    norm_num
  calc
    ((6931471803:ℝ)/2000000000) = (5:ℝ) * ((6931471803:ℝ)/10000000000) + (0:ℝ) - (0:ℝ) ^ 2 / 2 + (0:ℝ) ^ 3 / 3 - (0:ℝ) ^ 4 / 4 + (0:ℝ) ^ 5 / 5 - (0:ℝ) ^ 6 / 6 + (0:ℝ) ^ 7 / 7 - (0:ℝ) ^ 8 / 8 := by norm_num
    _ ≤ (5:ℝ) * Real.log 2 + Real.log (1 + (0:ℝ)) := by
      nlinarith
    _ = Real.log (32:ℝ) := by rw [← hlogq]

private lemma vlog_lb_m37 : ((1302737042421079981271:ℝ)/360777252864000000000) ≤ Real.log (37:ℝ) := by
  have hdec : (37:ℝ) = (2:ℝ)^(5) * (1 + ((5:ℝ)/32)) := by norm_num
  have harg' : 1 + ((5:ℝ)/32) ≠ 0 := by norm_num
  have h1 : (5:ℝ) * ((6931471803:ℝ)/10000000000) ≤ (5:ℝ) * Real.log 2 := by
    have hb : ((6931471803:ℝ)/10000000000) ≤ Real.log 2 := by
      have h := log_two_gt_d9
      norm_num at h ⊢
      linarith
    exact mul_le_mul_of_nonneg_left hb (by norm_num)
  have h2 : ((5:ℝ)/32) - ((5:ℝ)/32) ^ 2 / 2 + ((5:ℝ)/32) ^ 3 / 3 - ((5:ℝ)/32) ^ 4 / 4 + ((5:ℝ)/32) ^ 5 / 5 - ((5:ℝ)/32) ^ 6 / 6 + ((5:ℝ)/32) ^ 7 / 7 - ((5:ℝ)/32) ^ 8 / 8 ≤ Real.log (1 + ((5:ℝ)/32)) := log_one_add_ge7 ((5:ℝ)/32) (by norm_num)
  have hlogq : Real.log (37:ℝ) = (5:ℝ) * Real.log 2 + Real.log (1 + ((5:ℝ)/32)) := by
    rw [hdec]
    rw [Real.log_mul (by positivity : (2:ℝ)^(5) ≠ 0) harg']
    rw [Real.log_pow]
    norm_num
  calc
    ((1302737042421079981271:ℝ)/360777252864000000000) = (5:ℝ) * ((6931471803:ℝ)/10000000000) + ((5:ℝ)/32) - ((5:ℝ)/32) ^ 2 / 2 + ((5:ℝ)/32) ^ 3 / 3 - ((5:ℝ)/32) ^ 4 / 4 + ((5:ℝ)/32) ^ 5 / 5 - ((5:ℝ)/32) ^ 6 / 6 + ((5:ℝ)/32) ^ 7 / 7 - ((5:ℝ)/32) ^ 8 / 8 := by norm_num
    _ ≤ (5:ℝ) * Real.log 2 + Real.log (1 + ((5:ℝ)/32)) := by
      nlinarith
    _ = Real.log (37:ℝ) := by rw [← hlogq]

private lemma vlog_lb_m936_25 : ((2028734197772596313:ℝ)/560000000000000000) ≤ Real.log ((936:ℝ)/25) := by
  have hdec : ((936:ℝ)/25) = (2:ℝ)^(5) * (1 + ((17:ℝ)/100)) := by norm_num
  have harg' : 1 + ((17:ℝ)/100) ≠ 0 := by norm_num
  have h1 : (5:ℝ) * ((6931471803:ℝ)/10000000000) ≤ (5:ℝ) * Real.log 2 := by
    have hb : ((6931471803:ℝ)/10000000000) ≤ Real.log 2 := by
      have h := log_two_gt_d9
      norm_num at h ⊢
      linarith
    exact mul_le_mul_of_nonneg_left hb (by norm_num)
  have h2 : ((17:ℝ)/100) - ((17:ℝ)/100) ^ 2 / 2 + ((17:ℝ)/100) ^ 3 / 3 - ((17:ℝ)/100) ^ 4 / 4 + ((17:ℝ)/100) ^ 5 / 5 - ((17:ℝ)/100) ^ 6 / 6 + ((17:ℝ)/100) ^ 7 / 7 - ((17:ℝ)/100) ^ 8 / 8 ≤ Real.log (1 + ((17:ℝ)/100)) := log_one_add_ge7 ((17:ℝ)/100) (by norm_num)
  have hlogq : Real.log ((936:ℝ)/25) = (5:ℝ) * Real.log 2 + Real.log (1 + ((17:ℝ)/100)) := by
    rw [hdec]
    rw [Real.log_mul (by positivity : (2:ℝ)^(5) ≠ 0) harg']
    rw [Real.log_pow]
    norm_num
  calc
    ((2028734197772596313:ℝ)/560000000000000000) = (5:ℝ) * ((6931471803:ℝ)/10000000000) + ((17:ℝ)/100) - ((17:ℝ)/100) ^ 2 / 2 + ((17:ℝ)/100) ^ 3 / 3 - ((17:ℝ)/100) ^ 4 / 4 + ((17:ℝ)/100) ^ 5 / 5 - ((17:ℝ)/100) ^ 6 / 6 + ((17:ℝ)/100) ^ 7 / 7 - ((17:ℝ)/100) ^ 8 / 8 := by norm_num
    _ ≤ (5:ℝ) * Real.log 2 + Real.log (1 + ((17:ℝ)/100)) := by
      nlinarith
    _ = Real.log ((936:ℝ)/25) := by rw [← hlogq]

private lemma vlog_lb_m153_4 : ((28720585946874995412186877:ℝ)/7881299347898368000000000) ≤ Real.log ((153:ℝ)/4) := by
  have hdec : ((153:ℝ)/4) = (2:ℝ)^(5) * (1 + ((25:ℝ)/128)) := by norm_num
  have harg' : 1 + ((25:ℝ)/128) ≠ 0 := by norm_num
  have h1 : (5:ℝ) * ((6931471803:ℝ)/10000000000) ≤ (5:ℝ) * Real.log 2 := by
    have hb : ((6931471803:ℝ)/10000000000) ≤ Real.log 2 := by
      have h := log_two_gt_d9
      norm_num at h ⊢
      linarith
    exact mul_le_mul_of_nonneg_left hb (by norm_num)
  have h2 : ((25:ℝ)/128) - ((25:ℝ)/128) ^ 2 / 2 + ((25:ℝ)/128) ^ 3 / 3 - ((25:ℝ)/128) ^ 4 / 4 + ((25:ℝ)/128) ^ 5 / 5 - ((25:ℝ)/128) ^ 6 / 6 + ((25:ℝ)/128) ^ 7 / 7 - ((25:ℝ)/128) ^ 8 / 8 ≤ Real.log (1 + ((25:ℝ)/128)) := log_one_add_ge7 ((25:ℝ)/128) (by norm_num)
  have hlogq : Real.log ((153:ℝ)/4) = (5:ℝ) * Real.log 2 + Real.log (1 + ((25:ℝ)/128)) := by
    rw [hdec]
    rw [Real.log_mul (by positivity : (2:ℝ)^(5) ≠ 0) harg']
    rw [Real.log_pow]
    norm_num
  calc
    ((28720585946874995412186877:ℝ)/7881299347898368000000000) = (5:ℝ) * ((6931471803:ℝ)/10000000000) + ((25:ℝ)/128) - ((25:ℝ)/128) ^ 2 / 2 + ((25:ℝ)/128) ^ 3 / 3 - ((25:ℝ)/128) ^ 4 / 4 + ((25:ℝ)/128) ^ 5 / 5 - ((25:ℝ)/128) ^ 6 / 6 + ((25:ℝ)/128) ^ 7 / 7 - ((25:ℝ)/128) ^ 8 / 8 := by norm_num
    _ ≤ (5:ℝ) * Real.log 2 + Real.log (1 + ((25:ℝ)/128)) := by
      nlinarith
    _ = Real.log ((153:ℝ)/4) := by rw [← hlogq]

private lemma vlog_lb_m40 : ((79325656310231:ℝ)/21504000000000) ≤ Real.log (40:ℝ) := by
  have hdec : (40:ℝ) = (2:ℝ)^(5) * (1 + ((1:ℝ)/4)) := by norm_num
  have harg' : 1 + ((1:ℝ)/4) ≠ 0 := by norm_num
  have h1 : (5:ℝ) * ((6931471803:ℝ)/10000000000) ≤ (5:ℝ) * Real.log 2 := by
    have hb : ((6931471803:ℝ)/10000000000) ≤ Real.log 2 := by
      have h := log_two_gt_d9
      norm_num at h ⊢
      linarith
    exact mul_le_mul_of_nonneg_left hb (by norm_num)
  have h2 : ((1:ℝ)/4) - ((1:ℝ)/4) ^ 2 / 2 + ((1:ℝ)/4) ^ 3 / 3 - ((1:ℝ)/4) ^ 4 / 4 + ((1:ℝ)/4) ^ 5 / 5 - ((1:ℝ)/4) ^ 6 / 6 + ((1:ℝ)/4) ^ 7 / 7 - ((1:ℝ)/4) ^ 8 / 8 ≤ Real.log (1 + ((1:ℝ)/4)) := log_one_add_ge7 ((1:ℝ)/4) (by norm_num)
  have hlogq : Real.log (40:ℝ) = (5:ℝ) * Real.log 2 + Real.log (1 + ((1:ℝ)/4)) := by
    rw [hdec]
    rw [Real.log_mul (by positivity : (2:ℝ)^(5) ≠ 0) harg']
    rw [Real.log_pow]
    norm_num
  calc
    ((79325656310231:ℝ)/21504000000000) = (5:ℝ) * ((6931471803:ℝ)/10000000000) + ((1:ℝ)/4) - ((1:ℝ)/4) ^ 2 / 2 + ((1:ℝ)/4) ^ 3 / 3 - ((1:ℝ)/4) ^ 4 / 4 + ((1:ℝ)/4) ^ 5 / 5 - ((1:ℝ)/4) ^ 6 / 6 + ((1:ℝ)/4) ^ 7 / 7 - ((1:ℝ)/4) ^ 8 / 8 := by norm_num
    _ ≤ (5:ℝ) * Real.log 2 + Real.log (1 + ((1:ℝ)/4)) := by
      nlinarith
    _ = Real.log (40:ℝ) := by rw [← hlogq]

private lemma vlog_lb_m169_4 : ((88513327206541510586560631:ℝ)/23643898043695104000000000) ≤ Real.log ((169:ℝ)/4) := by
  have hdec : ((169:ℝ)/4) = (2:ℝ)^(5) * (1 + ((41:ℝ)/128)) := by norm_num
  have harg' : 1 + ((41:ℝ)/128) ≠ 0 := by norm_num
  have h1 : (5:ℝ) * ((6931471803:ℝ)/10000000000) ≤ (5:ℝ) * Real.log 2 := by
    have hb : ((6931471803:ℝ)/10000000000) ≤ Real.log 2 := by
      have h := log_two_gt_d9
      norm_num at h ⊢
      linarith
    exact mul_le_mul_of_nonneg_left hb (by norm_num)
  have h2 : ((41:ℝ)/128) - ((41:ℝ)/128) ^ 2 / 2 + ((41:ℝ)/128) ^ 3 / 3 - ((41:ℝ)/128) ^ 4 / 4 + ((41:ℝ)/128) ^ 5 / 5 - ((41:ℝ)/128) ^ 6 / 6 + ((41:ℝ)/128) ^ 7 / 7 - ((41:ℝ)/128) ^ 8 / 8 ≤ Real.log (1 + ((41:ℝ)/128)) := log_one_add_ge7 ((41:ℝ)/128) (by norm_num)
  have hlogq : Real.log ((169:ℝ)/4) = (5:ℝ) * Real.log 2 + Real.log (1 + ((41:ℝ)/128)) := by
    rw [hdec]
    rw [Real.log_mul (by positivity : (2:ℝ)^(5) ≠ 0) harg']
    rw [Real.log_pow]
    norm_num
  calc
    ((88513327206541510586560631:ℝ)/23643898043695104000000000) = (5:ℝ) * ((6931471803:ℝ)/10000000000) + ((41:ℝ)/128) - ((41:ℝ)/128) ^ 2 / 2 + ((41:ℝ)/128) ^ 3 / 3 - ((41:ℝ)/128) ^ 4 / 4 + ((41:ℝ)/128) ^ 5 / 5 - ((41:ℝ)/128) ^ 6 / 6 + ((41:ℝ)/128) ^ 7 / 7 - ((41:ℝ)/128) ^ 8 / 8 := by norm_num
    _ ≤ (5:ℝ) * Real.log 2 + Real.log (1 + ((41:ℝ)/128)) := by
      nlinarith
    _ = Real.log ((169:ℝ)/4) := by rw [← hlogq]

private lemma vlog_lb_m45 : ((457782793762884993757:ℝ)/120259084288000000000) ≤ Real.log (45:ℝ) := by
  have hdec : (45:ℝ) = (2:ℝ)^(5) * (1 + ((13:ℝ)/32)) := by norm_num
  have harg' : 1 + ((13:ℝ)/32) ≠ 0 := by norm_num
  have h1 : (5:ℝ) * ((6931471803:ℝ)/10000000000) ≤ (5:ℝ) * Real.log 2 := by
    have hb : ((6931471803:ℝ)/10000000000) ≤ Real.log 2 := by
      have h := log_two_gt_d9
      norm_num at h ⊢
      linarith
    exact mul_le_mul_of_nonneg_left hb (by norm_num)
  have h2 : ((13:ℝ)/32) - ((13:ℝ)/32) ^ 2 / 2 + ((13:ℝ)/32) ^ 3 / 3 - ((13:ℝ)/32) ^ 4 / 4 + ((13:ℝ)/32) ^ 5 / 5 - ((13:ℝ)/32) ^ 6 / 6 + ((13:ℝ)/32) ^ 7 / 7 - ((13:ℝ)/32) ^ 8 / 8 ≤ Real.log (1 + ((13:ℝ)/32)) := log_one_add_ge7 ((13:ℝ)/32) (by norm_num)
  have hlogq : Real.log (45:ℝ) = (5:ℝ) * Real.log 2 + Real.log (1 + ((13:ℝ)/32)) := by
    rw [hdec]
    rw [Real.log_mul (by positivity : (2:ℝ)^(5) ≠ 0) harg']
    rw [Real.log_pow]
    norm_num
  calc
    ((457782793762884993757:ℝ)/120259084288000000000) = (5:ℝ) * ((6931471803:ℝ)/10000000000) + ((13:ℝ)/32) - ((13:ℝ)/32) ^ 2 / 2 + ((13:ℝ)/32) ^ 3 / 3 - ((13:ℝ)/32) ^ 4 / 4 + ((13:ℝ)/32) ^ 5 / 5 - ((13:ℝ)/32) ^ 6 / 6 + ((13:ℝ)/32) ^ 7 / 7 - ((13:ℝ)/32) ^ 8 / 8 := by norm_num
    _ ≤ (5:ℝ) * Real.log 2 + Real.log (1 + ((13:ℝ)/32)) := by
      nlinarith
    _ = Real.log (45:ℝ) := by rw [← hlogq]

private lemma vlog_lb_m52 : ((36252810578103897:ℝ)/9175040000000000) ≤ Real.log (52:ℝ) := by
  have hdec : (52:ℝ) = (2:ℝ)^(6) * (1 - ((3:ℝ)/16)) := by norm_num
  have harg' : 1 - ((3:ℝ)/16) ≠ 0 := by norm_num
  have h1 : (6:ℝ) * ((6931471803:ℝ)/10000000000) ≤ (6:ℝ) * Real.log 2 := by
    have hb : ((6931471803:ℝ)/10000000000) ≤ Real.log 2 := by
      have h := log_two_gt_d9
      norm_num at h ⊢
      linarith
    exact mul_le_mul_of_nonneg_left hb (by norm_num)
  have h2 : -( ((3:ℝ)/16) + ((3:ℝ)/16) ^ 2 / 2 + ((3:ℝ)/16) ^ 3 / 3 + ((3:ℝ)/16) ^ 4 / 4 + ((3:ℝ)/16) ^ 5 / 5 + ((3:ℝ)/16) ^ 6 / 6 ) - 2 * ((3:ℝ)/16) ^ 7 / 7 ≤ Real.log (1 - ((3:ℝ)/16)) := log_one_sub_ge6 ((3:ℝ)/16) (by norm_num) (by norm_num : ((3:ℝ)/16) ≤ (1:ℝ)/2)
  have hlogq : Real.log (52:ℝ) = (6:ℝ) * Real.log 2 + Real.log (1 - ((3:ℝ)/16)) := by
    rw [hdec]
    rw [Real.log_mul (by positivity : (2:ℝ)^(6) ≠ 0) harg']
    rw [Real.log_pow]
    norm_num
  calc
    ((36252810578103897:ℝ)/9175040000000000) = (6:ℝ) * ((6931471803:ℝ)/10000000000) + -( ((3:ℝ)/16) + ((3:ℝ)/16) ^ 2 / 2 + ((3:ℝ)/16) ^ 3 / 3 + ((3:ℝ)/16) ^ 4 / 4 + ((3:ℝ)/16) ^ 5 / 5 + ((3:ℝ)/16) ^ 6 / 6 ) - 2 * ((3:ℝ)/16) ^ 7 / 7 := by norm_num
    _ ≤ (6:ℝ) * Real.log 2 + Real.log (1 - ((3:ℝ)/16)) := by
      nlinarith
    _ = Real.log (52:ℝ) := by rw [← hlogq]

private lemma vlog_lb_m72 : ((39238582687478897:ℝ)/9175040000000000) ≤ Real.log (72:ℝ) := by
  have hdec : (72:ℝ) = (2:ℝ)^(6) * (1 + ((1:ℝ)/8)) := by norm_num
  have harg' : 1 + ((1:ℝ)/8) ≠ 0 := by norm_num
  have h1 : (6:ℝ) * ((6931471803:ℝ)/10000000000) ≤ (6:ℝ) * Real.log 2 := by
    have hb : ((6931471803:ℝ)/10000000000) ≤ Real.log 2 := by
      have h := log_two_gt_d9
      norm_num at h ⊢
      linarith
    exact mul_le_mul_of_nonneg_left hb (by norm_num)
  have h2 : ((1:ℝ)/8) - ((1:ℝ)/8) ^ 2 / 2 + ((1:ℝ)/8) ^ 3 / 3 - ((1:ℝ)/8) ^ 4 / 4 + ((1:ℝ)/8) ^ 5 / 5 - ((1:ℝ)/8) ^ 6 / 6 + ((1:ℝ)/8) ^ 7 / 7 - ((1:ℝ)/8) ^ 8 / 8 ≤ Real.log (1 + ((1:ℝ)/8)) := log_one_add_ge7 ((1:ℝ)/8) (by norm_num)
  have hlogq : Real.log (72:ℝ) = (6:ℝ) * Real.log 2 + Real.log (1 + ((1:ℝ)/8)) := by
    rw [hdec]
    rw [Real.log_mul (by positivity : (2:ℝ)^(6) ≠ 0) harg']
    rw [Real.log_pow]
    norm_num
  calc
    ((39238582687478897:ℝ)/9175040000000000) = (6:ℝ) * ((6931471803:ℝ)/10000000000) + ((1:ℝ)/8) - ((1:ℝ)/8) ^ 2 / 2 + ((1:ℝ)/8) ^ 3 / 3 - ((1:ℝ)/8) ^ 4 / 4 + ((1:ℝ)/8) ^ 5 / 5 - ((1:ℝ)/8) ^ 6 / 6 + ((1:ℝ)/8) ^ 7 / 7 - ((1:ℝ)/8) ^ 8 / 8 := by norm_num
    _ ≤ (6:ℝ) * Real.log 2 + Real.log (1 + ((1:ℝ)/8)) := by
      nlinarith
    _ = Real.log (72:ℝ) := by rw [← hlogq]

private lemma vlog_lb_m82 : ((2649739518702173634417:ℝ)/601295421440000000000) ≤ Real.log (82:ℝ) := by
  have hdec : (82:ℝ) = (2:ℝ)^(6) * (1 + ((9:ℝ)/32)) := by norm_num
  have harg' : 1 + ((9:ℝ)/32) ≠ 0 := by norm_num
  have h1 : (6:ℝ) * ((6931471803:ℝ)/10000000000) ≤ (6:ℝ) * Real.log 2 := by
    have hb : ((6931471803:ℝ)/10000000000) ≤ Real.log 2 := by
      have h := log_two_gt_d9
      norm_num at h ⊢
      linarith
    exact mul_le_mul_of_nonneg_left hb (by norm_num)
  have h2 : ((9:ℝ)/32) - ((9:ℝ)/32) ^ 2 / 2 + ((9:ℝ)/32) ^ 3 / 3 - ((9:ℝ)/32) ^ 4 / 4 + ((9:ℝ)/32) ^ 5 / 5 - ((9:ℝ)/32) ^ 6 / 6 + ((9:ℝ)/32) ^ 7 / 7 - ((9:ℝ)/32) ^ 8 / 8 ≤ Real.log (1 + ((9:ℝ)/32)) := log_one_add_ge7 ((9:ℝ)/32) (by norm_num)
  have hlogq : Real.log (82:ℝ) = (6:ℝ) * Real.log 2 + Real.log (1 + ((9:ℝ)/32)) := by
    rw [hdec]
    rw [Real.log_mul (by positivity : (2:ℝ)^(6) ≠ 0) harg']
    rw [Real.log_pow]
    norm_num
  calc
    ((2649739518702173634417:ℝ)/601295421440000000000) = (6:ℝ) * ((6931471803:ℝ)/10000000000) + ((9:ℝ)/32) - ((9:ℝ)/32) ^ 2 / 2 + ((9:ℝ)/32) ^ 3 / 3 - ((9:ℝ)/32) ^ 4 / 4 + ((9:ℝ)/32) ^ 5 / 5 - ((9:ℝ)/32) ^ 6 / 6 + ((9:ℝ)/32) ^ 7 / 7 - ((9:ℝ)/32) ^ 8 / 8 := by norm_num
    _ ≤ (6:ℝ) * Real.log 2 + Real.log (1 + ((9:ℝ)/32)) := by
      nlinarith
    _ = Real.log (82:ℝ) := by rw [← hlogq]

private lemma vlog_lb_m2061_25 : ((10611828869600822546167537433:ℝ)/2405181685760000000000000000) ≤ Real.log ((2061:ℝ)/25) := by
  have hdec : ((2061:ℝ)/25) = (2:ℝ)^(6) * (1 + ((461:ℝ)/1600)) := by norm_num
  have harg' : 1 + ((461:ℝ)/1600) ≠ 0 := by norm_num
  have h1 : (6:ℝ) * ((6931471803:ℝ)/10000000000) ≤ (6:ℝ) * Real.log 2 := by
    have hb : ((6931471803:ℝ)/10000000000) ≤ Real.log 2 := by
      have h := log_two_gt_d9
      norm_num at h ⊢
      linarith
    exact mul_le_mul_of_nonneg_left hb (by norm_num)
  have h2 : ((461:ℝ)/1600) - ((461:ℝ)/1600) ^ 2 / 2 + ((461:ℝ)/1600) ^ 3 / 3 - ((461:ℝ)/1600) ^ 4 / 4 + ((461:ℝ)/1600) ^ 5 / 5 - ((461:ℝ)/1600) ^ 6 / 6 + ((461:ℝ)/1600) ^ 7 / 7 - ((461:ℝ)/1600) ^ 8 / 8 ≤ Real.log (1 + ((461:ℝ)/1600)) := log_one_add_ge7 ((461:ℝ)/1600) (by norm_num)
  have hlogq : Real.log ((2061:ℝ)/25) = (6:ℝ) * Real.log 2 + Real.log (1 + ((461:ℝ)/1600)) := by
    rw [hdec]
    rw [Real.log_mul (by positivity : (2:ℝ)^(6) ≠ 0) harg']
    rw [Real.log_pow]
    norm_num
  calc
    ((10611828869600822546167537433:ℝ)/2405181685760000000000000000) = (6:ℝ) * ((6931471803:ℝ)/10000000000) + ((461:ℝ)/1600) - ((461:ℝ)/1600) ^ 2 / 2 + ((461:ℝ)/1600) ^ 3 / 3 - ((461:ℝ)/1600) ^ 4 / 4 + ((461:ℝ)/1600) ^ 5 / 5 - ((461:ℝ)/1600) ^ 6 / 6 + ((461:ℝ)/1600) ^ 7 / 7 - ((461:ℝ)/1600) ^ 8 / 8 := by norm_num
    _ ≤ (6:ℝ) * Real.log 2 + Real.log (1 + ((461:ℝ)/1600)) := by
      nlinarith
    _ = Real.log ((2061:ℝ)/25) := by rw [← hlogq]

private lemma vlog_lb_m333_4 : ((6372552204783428613837597671:ℝ)/1441151880758558720000000000) ≤ Real.log ((333:ℝ)/4) := by
  have hdec : ((333:ℝ)/4) = (2:ℝ)^(6) * (1 + ((77:ℝ)/256)) := by norm_num
  have harg' : 1 + ((77:ℝ)/256) ≠ 0 := by norm_num
  have h1 : (6:ℝ) * ((6931471803:ℝ)/10000000000) ≤ (6:ℝ) * Real.log 2 := by
    have hb : ((6931471803:ℝ)/10000000000) ≤ Real.log 2 := by
      have h := log_two_gt_d9
      norm_num at h ⊢
      linarith
    exact mul_le_mul_of_nonneg_left hb (by norm_num)
  have h2 : ((77:ℝ)/256) - ((77:ℝ)/256) ^ 2 / 2 + ((77:ℝ)/256) ^ 3 / 3 - ((77:ℝ)/256) ^ 4 / 4 + ((77:ℝ)/256) ^ 5 / 5 - ((77:ℝ)/256) ^ 6 / 6 + ((77:ℝ)/256) ^ 7 / 7 - ((77:ℝ)/256) ^ 8 / 8 ≤ Real.log (1 + ((77:ℝ)/256)) := log_one_add_ge7 ((77:ℝ)/256) (by norm_num)
  have hlogq : Real.log ((333:ℝ)/4) = (6:ℝ) * Real.log 2 + Real.log (1 + ((77:ℝ)/256)) := by
    rw [hdec]
    rw [Real.log_mul (by positivity : (2:ℝ)^(6) ≠ 0) harg']
    rw [Real.log_pow]
    norm_num
  calc
    ((6372552204783428613837597671:ℝ)/1441151880758558720000000000) = (6:ℝ) * ((6931471803:ℝ)/10000000000) + ((77:ℝ)/256) - ((77:ℝ)/256) ^ 2 / 2 + ((77:ℝ)/256) ^ 3 / 3 - ((77:ℝ)/256) ^ 4 / 4 + ((77:ℝ)/256) ^ 5 / 5 - ((77:ℝ)/256) ^ 6 / 6 + ((77:ℝ)/256) ^ 7 / 7 - ((77:ℝ)/256) ^ 8 / 8 := by norm_num
    _ ≤ (6:ℝ) * Real.log 2 + Real.log (1 + ((77:ℝ)/256)) := by
      nlinarith
    _ = Real.log ((333:ℝ)/4) := by rw [← hlogq]

private lemma vlog_lb_m85 : ((97694851043729759935911:ℝ)/21990232555520000000000) ≤ Real.log (85:ℝ) := by
  have hdec : (85:ℝ) = (2:ℝ)^(6) * (1 + ((21:ℝ)/64)) := by norm_num
  have harg' : 1 + ((21:ℝ)/64) ≠ 0 := by norm_num
  have h1 : (6:ℝ) * ((6931471803:ℝ)/10000000000) ≤ (6:ℝ) * Real.log 2 := by
    have hb : ((6931471803:ℝ)/10000000000) ≤ Real.log 2 := by
      have h := log_two_gt_d9
      norm_num at h ⊢
      linarith
    exact mul_le_mul_of_nonneg_left hb (by norm_num)
  have h2 : ((21:ℝ)/64) - ((21:ℝ)/64) ^ 2 / 2 + ((21:ℝ)/64) ^ 3 / 3 - ((21:ℝ)/64) ^ 4 / 4 + ((21:ℝ)/64) ^ 5 / 5 - ((21:ℝ)/64) ^ 6 / 6 + ((21:ℝ)/64) ^ 7 / 7 - ((21:ℝ)/64) ^ 8 / 8 ≤ Real.log (1 + ((21:ℝ)/64)) := log_one_add_ge7 ((21:ℝ)/64) (by norm_num)
  have hlogq : Real.log (85:ℝ) = (6:ℝ) * Real.log 2 + Real.log (1 + ((21:ℝ)/64)) := by
    rw [hdec]
    rw [Real.log_mul (by positivity : (2:ℝ)^(6) ≠ 0) harg']
    rw [Real.log_pow]
    norm_num
  calc
    ((97694851043729759935911:ℝ)/21990232555520000000000) = (6:ℝ) * ((6931471803:ℝ)/10000000000) + ((21:ℝ)/64) - ((21:ℝ)/64) ^ 2 / 2 + ((21:ℝ)/64) ^ 3 / 3 - ((21:ℝ)/64) ^ 4 / 4 + ((21:ℝ)/64) ^ 5 / 5 - ((21:ℝ)/64) ^ 6 / 6 + ((21:ℝ)/64) ^ 7 / 7 - ((21:ℝ)/64) ^ 8 / 8 := by norm_num
    _ ≤ (6:ℝ) * Real.log 2 + Real.log (1 + ((21:ℝ)/64)) := by
      nlinarith
    _ = Real.log (85:ℝ) := by rw [← hlogq]

private lemma vlog_lb_m349_4 : ((45081217144194123531113183697:ℝ)/10088063165309911040000000000) ≤ Real.log ((349:ℝ)/4) := by
  have hdec : ((349:ℝ)/4) = (2:ℝ)^(6) * (1 + ((93:ℝ)/256)) := by norm_num
  have harg' : 1 + ((93:ℝ)/256) ≠ 0 := by norm_num
  have h1 : (6:ℝ) * ((6931471803:ℝ)/10000000000) ≤ (6:ℝ) * Real.log 2 := by
    have hb : ((6931471803:ℝ)/10000000000) ≤ Real.log 2 := by
      have h := log_two_gt_d9
      norm_num at h ⊢
      linarith
    exact mul_le_mul_of_nonneg_left hb (by norm_num)
  have h2 : ((93:ℝ)/256) - ((93:ℝ)/256) ^ 2 / 2 + ((93:ℝ)/256) ^ 3 / 3 - ((93:ℝ)/256) ^ 4 / 4 + ((93:ℝ)/256) ^ 5 / 5 - ((93:ℝ)/256) ^ 6 / 6 + ((93:ℝ)/256) ^ 7 / 7 - ((93:ℝ)/256) ^ 8 / 8 ≤ Real.log (1 + ((93:ℝ)/256)) := log_one_add_ge7 ((93:ℝ)/256) (by norm_num)
  have hlogq : Real.log ((349:ℝ)/4) = (6:ℝ) * Real.log 2 + Real.log (1 + ((93:ℝ)/256)) := by
    rw [hdec]
    rw [Real.log_mul (by positivity : (2:ℝ)^(6) ≠ 0) harg']
    rw [Real.log_pow]
    norm_num
  calc
    ((45081217144194123531113183697:ℝ)/10088063165309911040000000000) = (6:ℝ) * ((6931471803:ℝ)/10000000000) + ((93:ℝ)/256) - ((93:ℝ)/256) ^ 2 / 2 + ((93:ℝ)/256) ^ 3 / 3 - ((93:ℝ)/256) ^ 4 / 4 + ((93:ℝ)/256) ^ 5 / 5 - ((93:ℝ)/256) ^ 6 / 6 + ((93:ℝ)/256) ^ 7 / 7 - ((93:ℝ)/256) ^ 8 / 8 := by norm_num
    _ ≤ (6:ℝ) * Real.log 2 + Real.log (1 + ((93:ℝ)/256)) := by
      nlinarith
    _ = Real.log ((349:ℝ)/4) := by rw [← hlogq]

private lemma vlog_lb_m90 : ((2705700194712861134417:ℝ)/601295421440000000000) ≤ Real.log (90:ℝ) := by
  have hdec : (90:ℝ) = (2:ℝ)^(6) * (1 + ((13:ℝ)/32)) := by norm_num
  have harg' : 1 + ((13:ℝ)/32) ≠ 0 := by norm_num
  have h1 : (6:ℝ) * ((6931471803:ℝ)/10000000000) ≤ (6:ℝ) * Real.log 2 := by
    have hb : ((6931471803:ℝ)/10000000000) ≤ Real.log 2 := by
      have h := log_two_gt_d9
      norm_num at h ⊢
      linarith
    exact mul_le_mul_of_nonneg_left hb (by norm_num)
  have h2 : ((13:ℝ)/32) - ((13:ℝ)/32) ^ 2 / 2 + ((13:ℝ)/32) ^ 3 / 3 - ((13:ℝ)/32) ^ 4 / 4 + ((13:ℝ)/32) ^ 5 / 5 - ((13:ℝ)/32) ^ 6 / 6 + ((13:ℝ)/32) ^ 7 / 7 - ((13:ℝ)/32) ^ 8 / 8 ≤ Real.log (1 + ((13:ℝ)/32)) := log_one_add_ge7 ((13:ℝ)/32) (by norm_num)
  have hlogq : Real.log (90:ℝ) = (6:ℝ) * Real.log 2 + Real.log (1 + ((13:ℝ)/32)) := by
    rw [hdec]
    rw [Real.log_mul (by positivity : (2:ℝ)^(6) ≠ 0) harg']
    rw [Real.log_pow]
    norm_num
  calc
    ((2705700194712861134417:ℝ)/601295421440000000000) = (6:ℝ) * ((6931471803:ℝ)/10000000000) + ((13:ℝ)/32) - ((13:ℝ)/32) ^ 2 / 2 + ((13:ℝ)/32) ^ 3 / 3 - ((13:ℝ)/32) ^ 4 / 4 + ((13:ℝ)/32) ^ 5 / 5 - ((13:ℝ)/32) ^ 6 / 6 + ((13:ℝ)/32) ^ 7 / 7 - ((13:ℝ)/32) ^ 8 / 8 := by norm_num
    _ ≤ (6:ℝ) * Real.log 2 + Real.log (1 + ((13:ℝ)/32)) := by
      nlinarith
    _ = Real.log (90:ℝ) := by rw [← hlogq]

private lemma vlog_lb_m97 : ((264071971326534382601579:ℝ)/57724360458240000000000) ≤ Real.log (97:ℝ) := by
  have hdec : (97:ℝ) = (2:ℝ)^(7) * (1 - ((31:ℝ)/128)) := by norm_num
  have harg' : 1 - ((31:ℝ)/128) ≠ 0 := by norm_num
  have h1 : (7:ℝ) * ((6931471803:ℝ)/10000000000) ≤ (7:ℝ) * Real.log 2 := by
    have hb : ((6931471803:ℝ)/10000000000) ≤ Real.log 2 := by
      have h := log_two_gt_d9
      norm_num at h ⊢
      linarith
    exact mul_le_mul_of_nonneg_left hb (by norm_num)
  have h2 : -( ((31:ℝ)/128) + ((31:ℝ)/128) ^ 2 / 2 + ((31:ℝ)/128) ^ 3 / 3 + ((31:ℝ)/128) ^ 4 / 4 + ((31:ℝ)/128) ^ 5 / 5 + ((31:ℝ)/128) ^ 6 / 6 ) - 2 * ((31:ℝ)/128) ^ 7 / 7 ≤ Real.log (1 - ((31:ℝ)/128)) := log_one_sub_ge6 ((31:ℝ)/128) (by norm_num) (by norm_num : ((31:ℝ)/128) ≤ (1:ℝ)/2)
  have hlogq : Real.log (97:ℝ) = (7:ℝ) * Real.log 2 + Real.log (1 - ((31:ℝ)/128)) := by
    rw [hdec]
    rw [Real.log_mul (by positivity : (2:ℝ)^(7) ≠ 0) harg']
    rw [Real.log_pow]
    norm_num
  calc
    ((264071971326534382601579:ℝ)/57724360458240000000000) = (7:ℝ) * ((6931471803:ℝ)/10000000000) + -( ((31:ℝ)/128) + ((31:ℝ)/128) ^ 2 / 2 + ((31:ℝ)/128) ^ 3 / 3 + ((31:ℝ)/128) ^ 4 / 4 + ((31:ℝ)/128) ^ 5 / 5 + ((31:ℝ)/128) ^ 6 / 6 ) - 2 * ((31:ℝ)/128) ^ 7 / 7 := by norm_num
    _ ≤ (7:ℝ) * Real.log 2 + Real.log (1 - ((31:ℝ)/128)) := by
      nlinarith
    _ = Real.log (97:ℝ) := by rw [← hlogq]

private lemma vlog_lb_m117 : ((91631148136616734304693:ℝ)/19241453486080000000000) ≤ Real.log (117:ℝ) := by
  have hdec : (117:ℝ) = (2:ℝ)^(7) * (1 - ((11:ℝ)/128)) := by norm_num
  have harg' : 1 - ((11:ℝ)/128) ≠ 0 := by norm_num
  have h1 : (7:ℝ) * ((6931471803:ℝ)/10000000000) ≤ (7:ℝ) * Real.log 2 := by
    have hb : ((6931471803:ℝ)/10000000000) ≤ Real.log 2 := by
      have h := log_two_gt_d9
      norm_num at h ⊢
      linarith
    exact mul_le_mul_of_nonneg_left hb (by norm_num)
  have h2 : -( ((11:ℝ)/128) + ((11:ℝ)/128) ^ 2 / 2 + ((11:ℝ)/128) ^ 3 / 3 + ((11:ℝ)/128) ^ 4 / 4 + ((11:ℝ)/128) ^ 5 / 5 + ((11:ℝ)/128) ^ 6 / 6 ) - 2 * ((11:ℝ)/128) ^ 7 / 7 ≤ Real.log (1 - ((11:ℝ)/128)) := log_one_sub_ge6 ((11:ℝ)/128) (by norm_num) (by norm_num : ((11:ℝ)/128) ≤ (1:ℝ)/2)
  have hlogq : Real.log (117:ℝ) = (7:ℝ) * Real.log 2 + Real.log (1 - ((11:ℝ)/128)) := by
    rw [hdec]
    rw [Real.log_mul (by positivity : (2:ℝ)^(7) ≠ 0) harg']
    rw [Real.log_pow]
    norm_num
  calc
    ((91631148136616734304693:ℝ)/19241453486080000000000) = (7:ℝ) * ((6931471803:ℝ)/10000000000) + -( ((11:ℝ)/128) + ((11:ℝ)/128) ^ 2 / 2 + ((11:ℝ)/128) ^ 3 / 3 + ((11:ℝ)/128) ^ 4 / 4 + ((11:ℝ)/128) ^ 5 / 5 + ((11:ℝ)/128) ^ 6 / 6 ) - 2 * ((11:ℝ)/128) ^ 7 / 7 := by norm_num
    _ ≤ (7:ℝ) * Real.log 2 + Real.log (1 - ((11:ℝ)/128)) := by
      nlinarith
    _ = Real.log (117:ℝ) := by rw [← hlogq]

private lemma vlog_lb_m170 : ((112937318733729711136167:ℝ)/21990232555520000000000) ≤ Real.log (170:ℝ) := by
  have hdec : (170:ℝ) = (2:ℝ)^(7) * (1 + ((21:ℝ)/64)) := by norm_num
  have harg' : 1 + ((21:ℝ)/64) ≠ 0 := by norm_num
  have h1 : (7:ℝ) * ((6931471803:ℝ)/10000000000) ≤ (7:ℝ) * Real.log 2 := by
    have hb : ((6931471803:ℝ)/10000000000) ≤ Real.log 2 := by
      have h := log_two_gt_d9
      norm_num at h ⊢
      linarith
    exact mul_le_mul_of_nonneg_left hb (by norm_num)
  have h2 : ((21:ℝ)/64) - ((21:ℝ)/64) ^ 2 / 2 + ((21:ℝ)/64) ^ 3 / 3 - ((21:ℝ)/64) ^ 4 / 4 + ((21:ℝ)/64) ^ 5 / 5 - ((21:ℝ)/64) ^ 6 / 6 + ((21:ℝ)/64) ^ 7 / 7 - ((21:ℝ)/64) ^ 8 / 8 ≤ Real.log (1 + ((21:ℝ)/64)) := log_one_add_ge7 ((21:ℝ)/64) (by norm_num)
  have hlogq : Real.log (170:ℝ) = (7:ℝ) * Real.log 2 + Real.log (1 + ((21:ℝ)/64)) := by
    rw [hdec]
    rw [Real.log_mul (by positivity : (2:ℝ)^(7) ≠ 0) harg']
    rw [Real.log_pow]
    norm_num
  calc
    ((112937318733729711136167:ℝ)/21990232555520000000000) = (7:ℝ) * ((6931471803:ℝ)/10000000000) + ((21:ℝ)/64) - ((21:ℝ)/64) ^ 2 / 2 + ((21:ℝ)/64) ^ 3 / 3 - ((21:ℝ)/64) ^ 4 / 4 + ((21:ℝ)/64) ^ 5 / 5 - ((21:ℝ)/64) ^ 6 / 6 + ((21:ℝ)/64) ^ 7 / 7 - ((21:ℝ)/64) ^ 8 / 8 := by norm_num
    _ ≤ (7:ℝ) * Real.log 2 + Real.log (1 + ((21:ℝ)/64)) := by
      nlinarith
    _ = Real.log (170:ℝ) := by rw [← hlogq]

private lemma vlog_lb_m4261_25 : ((9491508863317597871306254421899:ℝ)/1847179534663680000000000000000) ≤ Real.log ((4261:ℝ)/25) := by
  have hdec : ((4261:ℝ)/25) = (2:ℝ)^(7) * (1 + ((1061:ℝ)/3200)) := by norm_num
  have harg' : 1 + ((1061:ℝ)/3200) ≠ 0 := by norm_num
  have h1 : (7:ℝ) * ((6931471803:ℝ)/10000000000) ≤ (7:ℝ) * Real.log 2 := by
    have hb : ((6931471803:ℝ)/10000000000) ≤ Real.log 2 := by
      have h := log_two_gt_d9
      norm_num at h ⊢
      linarith
    exact mul_le_mul_of_nonneg_left hb (by norm_num)
  have h2 : ((1061:ℝ)/3200) - ((1061:ℝ)/3200) ^ 2 / 2 + ((1061:ℝ)/3200) ^ 3 / 3 - ((1061:ℝ)/3200) ^ 4 / 4 + ((1061:ℝ)/3200) ^ 5 / 5 - ((1061:ℝ)/3200) ^ 6 / 6 + ((1061:ℝ)/3200) ^ 7 / 7 - ((1061:ℝ)/3200) ^ 8 / 8 ≤ Real.log (1 + ((1061:ℝ)/3200)) := log_one_add_ge7 ((1061:ℝ)/3200) (by norm_num)
  have hlogq : Real.log ((4261:ℝ)/25) = (7:ℝ) * Real.log 2 + Real.log (1 + ((1061:ℝ)/3200)) := by
    rw [hdec]
    rw [Real.log_mul (by positivity : (2:ℝ)^(7) ≠ 0) harg']
    rw [Real.log_pow]
    norm_num
  calc
    ((9491508863317597871306254421899:ℝ)/1847179534663680000000000000000) = (7:ℝ) * ((6931471803:ℝ)/10000000000) + ((1061:ℝ)/3200) - ((1061:ℝ)/3200) ^ 2 / 2 + ((1061:ℝ)/3200) ^ 3 / 3 - ((1061:ℝ)/3200) ^ 4 / 4 + ((1061:ℝ)/3200) ^ 5 / 5 - ((1061:ℝ)/3200) ^ 6 / 6 + ((1061:ℝ)/3200) ^ 7 / 7 - ((1061:ℝ)/3200) ^ 8 / 8 := by norm_num
    _ ≤ (7:ℝ) * Real.log 2 + Real.log (1 + ((1061:ℝ)/3200)) := by
      nlinarith
    _ = Real.log ((4261:ℝ)/25) := by rw [← hlogq]

private lemma vlog_lb_m685_4 : ((39847000474700510266731395014387:ℝ)/7747632510958011678720000000000) ≤ Real.log ((685:ℝ)/4) := by
  have hdec : ((685:ℝ)/4) = (2:ℝ)^(7) * (1 + ((173:ℝ)/512)) := by norm_num
  have harg' : 1 + ((173:ℝ)/512) ≠ 0 := by norm_num
  have h1 : (7:ℝ) * ((6931471803:ℝ)/10000000000) ≤ (7:ℝ) * Real.log 2 := by
    have hb : ((6931471803:ℝ)/10000000000) ≤ Real.log 2 := by
      have h := log_two_gt_d9
      norm_num at h ⊢
      linarith
    exact mul_le_mul_of_nonneg_left hb (by norm_num)
  have h2 : ((173:ℝ)/512) - ((173:ℝ)/512) ^ 2 / 2 + ((173:ℝ)/512) ^ 3 / 3 - ((173:ℝ)/512) ^ 4 / 4 + ((173:ℝ)/512) ^ 5 / 5 - ((173:ℝ)/512) ^ 6 / 6 + ((173:ℝ)/512) ^ 7 / 7 - ((173:ℝ)/512) ^ 8 / 8 ≤ Real.log (1 + ((173:ℝ)/512)) := log_one_add_ge7 ((173:ℝ)/512) (by norm_num)
  have hlogq : Real.log ((685:ℝ)/4) = (7:ℝ) * Real.log 2 + Real.log (1 + ((173:ℝ)/512)) := by
    rw [hdec]
    rw [Real.log_mul (by positivity : (2:ℝ)^(7) ≠ 0) harg']
    rw [Real.log_pow]
    norm_num
  calc
    ((39847000474700510266731395014387:ℝ)/7747632510958011678720000000000) = (7:ℝ) * ((6931471803:ℝ)/10000000000) + ((173:ℝ)/512) - ((173:ℝ)/512) ^ 2 / 2 + ((173:ℝ)/512) ^ 3 / 3 - ((173:ℝ)/512) ^ 4 / 4 + ((173:ℝ)/512) ^ 5 / 5 - ((173:ℝ)/512) ^ 6 / 6 + ((173:ℝ)/512) ^ 7 / 7 - ((173:ℝ)/512) ^ 8 / 8 := by norm_num
    _ ≤ (7:ℝ) * Real.log 2 + Real.log (1 + ((173:ℝ)/512)) := by
      nlinarith
    _ = Real.log ((685:ℝ)/4) := by rw [← hlogq]

private lemma vlog_lb_m173 : ((203072895307493988100151889:ℝ)/39406496739491840000000000) ≤ Real.log (173:ℝ) := by
  have hdec : (173:ℝ) = (2:ℝ)^(7) * (1 + ((45:ℝ)/128)) := by norm_num
  have harg' : 1 + ((45:ℝ)/128) ≠ 0 := by norm_num
  have h1 : (7:ℝ) * ((6931471803:ℝ)/10000000000) ≤ (7:ℝ) * Real.log 2 := by
    have hb : ((6931471803:ℝ)/10000000000) ≤ Real.log 2 := by
      have h := log_two_gt_d9
      norm_num at h ⊢
      linarith
    exact mul_le_mul_of_nonneg_left hb (by norm_num)
  have h2 : ((45:ℝ)/128) - ((45:ℝ)/128) ^ 2 / 2 + ((45:ℝ)/128) ^ 3 / 3 - ((45:ℝ)/128) ^ 4 / 4 + ((45:ℝ)/128) ^ 5 / 5 - ((45:ℝ)/128) ^ 6 / 6 + ((45:ℝ)/128) ^ 7 / 7 - ((45:ℝ)/128) ^ 8 / 8 ≤ Real.log (1 + ((45:ℝ)/128)) := log_one_add_ge7 ((45:ℝ)/128) (by norm_num)
  have hlogq : Real.log (173:ℝ) = (7:ℝ) * Real.log 2 + Real.log (1 + ((45:ℝ)/128)) := by
    rw [hdec]
    rw [Real.log_mul (by positivity : (2:ℝ)^(7) ≠ 0) harg']
    rw [Real.log_pow]
    norm_num
  calc
    ((203072895307493988100151889:ℝ)/39406496739491840000000000) = (7:ℝ) * ((6931471803:ℝ)/10000000000) + ((45:ℝ)/128) - ((45:ℝ)/128) ^ 2 / 2 + ((45:ℝ)/128) ^ 3 / 3 - ((45:ℝ)/128) ^ 4 / 4 + ((45:ℝ)/128) ^ 5 / 5 - ((45:ℝ)/128) ^ 6 / 6 + ((45:ℝ)/128) ^ 7 / 7 - ((45:ℝ)/128) ^ 8 / 8 := by norm_num
    _ ≤ (7:ℝ) * Real.log 2 + Real.log (1 + ((45:ℝ)/128)) := by
      nlinarith
    _ = Real.log (173:ℝ) := by rw [← hlogq]

private lemma vlog_lb_m701_4 : ((1905992455504679367682006905447:ℝ)/368934881474191032320000000000) ≤ Real.log ((701:ℝ)/4) := by
  have hdec : ((701:ℝ)/4) = (2:ℝ)^(7) * (1 + ((189:ℝ)/512)) := by norm_num
  have harg' : 1 + ((189:ℝ)/512) ≠ 0 := by norm_num
  have h1 : (7:ℝ) * ((6931471803:ℝ)/10000000000) ≤ (7:ℝ) * Real.log 2 := by
    have hb : ((6931471803:ℝ)/10000000000) ≤ Real.log 2 := by
      have h := log_two_gt_d9
      norm_num at h ⊢
      linarith
    exact mul_le_mul_of_nonneg_left hb (by norm_num)
  have h2 : ((189:ℝ)/512) - ((189:ℝ)/512) ^ 2 / 2 + ((189:ℝ)/512) ^ 3 / 3 - ((189:ℝ)/512) ^ 4 / 4 + ((189:ℝ)/512) ^ 5 / 5 - ((189:ℝ)/512) ^ 6 / 6 + ((189:ℝ)/512) ^ 7 / 7 - ((189:ℝ)/512) ^ 8 / 8 ≤ Real.log (1 + ((189:ℝ)/512)) := log_one_add_ge7 ((189:ℝ)/512) (by norm_num)
  have hlogq : Real.log ((701:ℝ)/4) = (7:ℝ) * Real.log 2 + Real.log (1 + ((189:ℝ)/512)) := by
    rw [hdec]
    rw [Real.log_mul (by positivity : (2:ℝ)^(7) ≠ 0) harg']
    rw [Real.log_pow]
    norm_num
  calc
    ((1905992455504679367682006905447:ℝ)/368934881474191032320000000000) = (7:ℝ) * ((6931471803:ℝ)/10000000000) + ((189:ℝ)/512) - ((189:ℝ)/512) ^ 2 / 2 + ((189:ℝ)/512) ^ 3 / 3 - ((189:ℝ)/512) ^ 4 / 4 + ((189:ℝ)/512) ^ 5 / 5 - ((189:ℝ)/512) ^ 6 / 6 + ((189:ℝ)/512) ^ 7 / 7 - ((189:ℝ)/512) ^ 8 / 8 := by norm_num
    _ ≤ (7:ℝ) * Real.log 2 + Real.log (1 + ((189:ℝ)/512)) := by
      nlinarith
    _ = Real.log ((701:ℝ)/4) := by rw [← hlogq]

private lemma vlog_lb_m178 : ((2392913086057860746359507:ℝ)/461794883665920000000000) ≤ Real.log (178:ℝ) := by
  have hdec : (178:ℝ) = (2:ℝ)^(7) * (1 + ((25:ℝ)/64)) := by norm_num
  have harg' : 1 + ((25:ℝ)/64) ≠ 0 := by norm_num
  have h1 : (7:ℝ) * ((6931471803:ℝ)/10000000000) ≤ (7:ℝ) * Real.log 2 := by
    have hb : ((6931471803:ℝ)/10000000000) ≤ Real.log 2 := by
      have h := log_two_gt_d9
      norm_num at h ⊢
      linarith
    exact mul_le_mul_of_nonneg_left hb (by norm_num)
  have h2 : ((25:ℝ)/64) - ((25:ℝ)/64) ^ 2 / 2 + ((25:ℝ)/64) ^ 3 / 3 - ((25:ℝ)/64) ^ 4 / 4 + ((25:ℝ)/64) ^ 5 / 5 - ((25:ℝ)/64) ^ 6 / 6 + ((25:ℝ)/64) ^ 7 / 7 - ((25:ℝ)/64) ^ 8 / 8 ≤ Real.log (1 + ((25:ℝ)/64)) := log_one_add_ge7 ((25:ℝ)/64) (by norm_num)
  have hlogq : Real.log (178:ℝ) = (7:ℝ) * Real.log 2 + Real.log (1 + ((25:ℝ)/64)) := by
    rw [hdec]
    rw [Real.log_mul (by positivity : (2:ℝ)^(7) ≠ 0) harg']
    rw [Real.log_pow]
    norm_num
  calc
    ((2392913086057860746359507:ℝ)/461794883665920000000000) = (7:ℝ) * ((6931471803:ℝ)/10000000000) + ((25:ℝ)/64) - ((25:ℝ)/64) ^ 2 / 2 + ((25:ℝ)/64) ^ 3 / 3 - ((25:ℝ)/64) ^ 4 / 4 + ((25:ℝ)/64) ^ 5 / 5 - ((25:ℝ)/64) ^ 6 / 6 + ((25:ℝ)/64) ^ 7 / 7 - ((25:ℝ)/64) ^ 8 / 8 := by norm_num
    _ ≤ (7:ℝ) * Real.log 2 + Real.log (1 + ((25:ℝ)/64)) := by
      nlinarith
    _ = Real.log (178:ℝ) := by rw [← hlogq]

private lemma vlog_lb_m185 : ((205713780384660156662651889:ℝ)/39406496739491840000000000) ≤ Real.log (185:ℝ) := by
  have hdec : (185:ℝ) = (2:ℝ)^(7) * (1 + ((57:ℝ)/128)) := by norm_num
  have harg' : 1 + ((57:ℝ)/128) ≠ 0 := by norm_num
  have h1 : (7:ℝ) * ((6931471803:ℝ)/10000000000) ≤ (7:ℝ) * Real.log 2 := by
    have hb : ((6931471803:ℝ)/10000000000) ≤ Real.log 2 := by
      have h := log_two_gt_d9
      norm_num at h ⊢
      linarith
    exact mul_le_mul_of_nonneg_left hb (by norm_num)
  have h2 : ((57:ℝ)/128) - ((57:ℝ)/128) ^ 2 / 2 + ((57:ℝ)/128) ^ 3 / 3 - ((57:ℝ)/128) ^ 4 / 4 + ((57:ℝ)/128) ^ 5 / 5 - ((57:ℝ)/128) ^ 6 / 6 + ((57:ℝ)/128) ^ 7 / 7 - ((57:ℝ)/128) ^ 8 / 8 ≤ Real.log (1 + ((57:ℝ)/128)) := log_one_add_ge7 ((57:ℝ)/128) (by norm_num)
  have hlogq : Real.log (185:ℝ) = (7:ℝ) * Real.log 2 + Real.log (1 + ((57:ℝ)/128)) := by
    rw [hdec]
    rw [Real.log_mul (by positivity : (2:ℝ)^(7) ≠ 0) harg']
    rw [Real.log_pow]
    norm_num
  calc
    ((205713780384660156662651889:ℝ)/39406496739491840000000000) = (7:ℝ) * ((6931471803:ℝ)/10000000000) + ((57:ℝ)/128) - ((57:ℝ)/128) ^ 2 / 2 + ((57:ℝ)/128) ^ 3 / 3 - ((57:ℝ)/128) ^ 4 / 4 + ((57:ℝ)/128) ^ 5 / 5 - ((57:ℝ)/128) ^ 6 / 6 + ((57:ℝ)/128) ^ 7 / 7 - ((57:ℝ)/128) ^ 8 / 8 := by norm_num
    _ ≤ (7:ℝ) * Real.log 2 + Real.log (1 + ((57:ℝ)/128)) := by
      nlinarith
    _ = Real.log (185:ℝ) := by rw [← hlogq]

private lemma vlog_lb_m205 : ((13110070003415114261757501:ℝ)/2462906046218240000000000) ≤ Real.log (205:ℝ) := by
  have hdec : (205:ℝ) = (2:ℝ)^(8) * (1 - ((51:ℝ)/256)) := by norm_num
  have harg' : 1 - ((51:ℝ)/256) ≠ 0 := by norm_num
  have h1 : (8:ℝ) * ((6931471803:ℝ)/10000000000) ≤ (8:ℝ) * Real.log 2 := by
    have hb : ((6931471803:ℝ)/10000000000) ≤ Real.log 2 := by
      have h := log_two_gt_d9
      norm_num at h ⊢
      linarith
    exact mul_le_mul_of_nonneg_left hb (by norm_num)
  have h2 : -( ((51:ℝ)/256) + ((51:ℝ)/256) ^ 2 / 2 + ((51:ℝ)/256) ^ 3 / 3 + ((51:ℝ)/256) ^ 4 / 4 + ((51:ℝ)/256) ^ 5 / 5 + ((51:ℝ)/256) ^ 6 / 6 ) - 2 * ((51:ℝ)/256) ^ 7 / 7 ≤ Real.log (1 - ((51:ℝ)/256)) := log_one_sub_ge6 ((51:ℝ)/256) (by norm_num) (by norm_num : ((51:ℝ)/256) ≤ (1:ℝ)/2)
  have hlogq : Real.log (205:ℝ) = (8:ℝ) * Real.log 2 + Real.log (1 - ((51:ℝ)/256)) := by
    rw [hdec]
    rw [Real.log_mul (by positivity : (2:ℝ)^(8) ≠ 0) harg']
    rw [Real.log_pow]
    norm_num
  calc
    ((13110070003415114261757501:ℝ)/2462906046218240000000000) = (8:ℝ) * ((6931471803:ℝ)/10000000000) + -( ((51:ℝ)/256) + ((51:ℝ)/256) ^ 2 / 2 + ((51:ℝ)/256) ^ 3 / 3 + ((51:ℝ)/256) ^ 4 / 4 + ((51:ℝ)/256) ^ 5 / 5 + ((51:ℝ)/256) ^ 6 / 6 ) - 2 * ((51:ℝ)/256) ^ 7 / 7 := by norm_num
    _ ≤ (8:ℝ) * Real.log 2 + Real.log (1 - ((51:ℝ)/256)) := by
      nlinarith
    _ = Real.log (205:ℝ) := by rw [← hlogq]

private lemma vlog_ub_m369_100 : Real.log ((369:ℝ)/100) ≤ ((10695691969381813:ℝ)/8192000000000000) := by
  have hdec : ((369:ℝ)/100) = (2:ℝ)^(2) * (1 - ((31:ℝ)/400)) := by norm_num
  have harg' : 1 - ((31:ℝ)/400) ≠ 0 := by norm_num
  rw [hdec]
  rw [Real.log_mul (by positivity : (2:ℝ)^(2) ≠ 0) harg']
  rw [Real.log_pow]
  have h1 : (2:ℝ) * Real.log 2 ≤ (2:ℝ) * ((108304247:ℝ)/156250000) := by
    have hb : Real.log 2 ≤ ((108304247:ℝ)/156250000) := by
      have h := log_two_lt_d9
      norm_num at h ⊢
      linarith
    exact mul_le_mul_of_nonneg_left hb (by norm_num)
  have h2 : Real.log (1 - ((31:ℝ)/400)) ≤ -( ((31:ℝ)/400) + ((31:ℝ)/400) ^ 2 / 2 + ((31:ℝ)/400) ^ 3 / 3 + ((31:ℝ)/400) ^ 4 / 4 + ((31:ℝ)/400) ^ 5 / 5 + ((31:ℝ)/400) ^ 6 / 6 ) := log_one_sub_le6 ((31:ℝ)/400) (by norm_num) (by norm_num : ((31:ℝ)/400) ≤ (1:ℝ)/2)
  calc
    (2:ℝ) * Real.log 2 + Real.log (1 - ((31:ℝ)/400)) ≤ (2:ℝ) * ((108304247:ℝ)/156250000) + -( ((31:ℝ)/400) + ((31:ℝ)/400) ^ 2 / 2 + ((31:ℝ)/400) ^ 3 / 3 + ((31:ℝ)/400) ^ 4 / 4 + ((31:ℝ)/400) ^ 5 / 5 + ((31:ℝ)/400) ^ 6 / 6 ) := by
      nlinarith
    _ = ((10695691969381813:ℝ)/8192000000000000) := by norm_num

private lemma vlog_ub_m9_2 : Real.log ((9:ℝ)/2) ≤ ((215624536632101:ℝ)/143360000000000) := by
  have hdec : ((9:ℝ)/2) = (2:ℝ)^(2) * (1 + ((1:ℝ)/8)) := by norm_num
  have harg' : 1 + ((1:ℝ)/8) ≠ 0 := by norm_num
  rw [hdec]
  rw [Real.log_mul (by positivity : (2:ℝ)^(2) ≠ 0) harg']
  rw [Real.log_pow]
  have h1 : (2:ℝ) * Real.log 2 ≤ (2:ℝ) * ((108304247:ℝ)/156250000) := by
    have hb : Real.log 2 ≤ ((108304247:ℝ)/156250000) := by
      have h := log_two_lt_d9
      norm_num at h ⊢
      linarith
    exact mul_le_mul_of_nonneg_left hb (by norm_num)
  have h2 : Real.log (1 + ((1:ℝ)/8)) ≤ ((1:ℝ)/8) - ((1:ℝ)/8) ^ 2 / 2 + ((1:ℝ)/8) ^ 3 / 3 - ((1:ℝ)/8) ^ 4 / 4 + ((1:ℝ)/8) ^ 5 / 5 - ((1:ℝ)/8) ^ 6 / 6 + ((1:ℝ)/8) ^ 7 / 7 := log_one_add_le7 ((1:ℝ)/8) (by norm_num)
  calc
    (2:ℝ) * Real.log 2 + Real.log (1 + ((1:ℝ)/8)) ≤ (2:ℝ) * ((108304247:ℝ)/156250000) + ((1:ℝ)/8) - ((1:ℝ)/8) ^ 2 / 2 + ((1:ℝ)/8) ^ 3 / 3 - ((1:ℝ)/8) ^ 4 / 4 + ((1:ℝ)/8) ^ 5 / 5 - ((1:ℝ)/8) ^ 6 / 6 + ((1:ℝ)/8) ^ 7 / 7 := by
      nlinarith
    _ = ((215624536632101:ℝ)/143360000000000) := by norm_num

private lemma vlog_ub_m136_25 : Real.log ((136:ℝ)/25) ≤ ((578937528227:ℝ)/341796875000) := by
  have hdec : ((136:ℝ)/25) = (2:ℝ)^(2) * (1 + ((9:ℝ)/25)) := by norm_num
  have harg' : 1 + ((9:ℝ)/25) ≠ 0 := by norm_num
  rw [hdec]
  rw [Real.log_mul (by positivity : (2:ℝ)^(2) ≠ 0) harg']
  rw [Real.log_pow]
  have h1 : (2:ℝ) * Real.log 2 ≤ (2:ℝ) * ((108304247:ℝ)/156250000) := by
    have hb : Real.log 2 ≤ ((108304247:ℝ)/156250000) := by
      have h := log_two_lt_d9
      norm_num at h ⊢
      linarith
    exact mul_le_mul_of_nonneg_left hb (by norm_num)
  have h2 : Real.log (1 + ((9:ℝ)/25)) ≤ ((9:ℝ)/25) - ((9:ℝ)/25) ^ 2 / 2 + ((9:ℝ)/25) ^ 3 / 3 - ((9:ℝ)/25) ^ 4 / 4 + ((9:ℝ)/25) ^ 5 / 5 - ((9:ℝ)/25) ^ 6 / 6 + ((9:ℝ)/25) ^ 7 / 7 := log_one_add_le7 ((9:ℝ)/25) (by norm_num)
  calc
    (2:ℝ) * Real.log 2 + Real.log (1 + ((9:ℝ)/25)) ≤ (2:ℝ) * ((108304247:ℝ)/156250000) + ((9:ℝ)/25) - ((9:ℝ)/25) ^ 2 / 2 + ((9:ℝ)/25) ^ 3 / 3 - ((9:ℝ)/25) ^ 4 / 4 + ((9:ℝ)/25) ^ 5 / 5 - ((9:ℝ)/25) ^ 6 / 6 + ((9:ℝ)/25) ^ 7 / 7 := by
      nlinarith
    _ = ((578937528227:ℝ)/341796875000) := by norm_num

private lemma vlog_ub_m25_4 : Real.log ((25:ℝ)/4) ≤ ((115296323144801719:ℝ)/62914560000000000) := by
  have hdec : ((25:ℝ)/4) = (2:ℝ)^(3) * (1 - ((7:ℝ)/32)) := by norm_num
  have harg' : 1 - ((7:ℝ)/32) ≠ 0 := by norm_num
  rw [hdec]
  rw [Real.log_mul (by positivity : (2:ℝ)^(3) ≠ 0) harg']
  rw [Real.log_pow]
  have h1 : (3:ℝ) * Real.log 2 ≤ (3:ℝ) * ((108304247:ℝ)/156250000) := by
    have hb : Real.log 2 ≤ ((108304247:ℝ)/156250000) := by
      have h := log_two_lt_d9
      norm_num at h ⊢
      linarith
    exact mul_le_mul_of_nonneg_left hb (by norm_num)
  have h2 : Real.log (1 - ((7:ℝ)/32)) ≤ -( ((7:ℝ)/32) + ((7:ℝ)/32) ^ 2 / 2 + ((7:ℝ)/32) ^ 3 / 3 + ((7:ℝ)/32) ^ 4 / 4 + ((7:ℝ)/32) ^ 5 / 5 + ((7:ℝ)/32) ^ 6 / 6 ) := log_one_sub_le6 ((7:ℝ)/32) (by norm_num) (by norm_num : ((7:ℝ)/32) ≤ (1:ℝ)/2)
  calc
    (3:ℝ) * Real.log 2 + Real.log (1 - ((7:ℝ)/32)) ≤ (3:ℝ) * ((108304247:ℝ)/156250000) + -( ((7:ℝ)/32) + ((7:ℝ)/32) ^ 2 / 2 + ((7:ℝ)/32) ^ 3 / 3 + ((7:ℝ)/32) ^ 4 / 4 + ((7:ℝ)/32) ^ 5 / 5 + ((7:ℝ)/32) ^ 6 / 6 ) := by
      nlinarith
    _ = ((115296323144801719:ℝ)/62914560000000000) := by norm_num

private lemma vlog_ub_m8 : Real.log (8:ℝ) ≤ ((324912741:ℝ)/156250000) := by
  have hdec : (8:ℝ) = (2:ℝ)^(3) * (1 + (0:ℝ)) := by norm_num
  have harg' : 1 + (0:ℝ) ≠ 0 := by norm_num
  rw [hdec]
  rw [Real.log_mul (by positivity : (2:ℝ)^(3) ≠ 0) harg']
  rw [Real.log_pow]
  have h1 : (3:ℝ) * Real.log 2 ≤ (3:ℝ) * ((108304247:ℝ)/156250000) := by
    have hb : Real.log 2 ≤ ((108304247:ℝ)/156250000) := by
      have h := log_two_lt_d9
      norm_num at h ⊢
      linarith
    exact mul_le_mul_of_nonneg_left hb (by norm_num)
  have h2 : Real.log (1 + (0:ℝ)) ≤ (0:ℝ) - (0:ℝ) ^ 2 / 2 + (0:ℝ) ^ 3 / 3 - (0:ℝ) ^ 4 / 4 + (0:ℝ) ^ 5 / 5 - (0:ℝ) ^ 6 / 6 + (0:ℝ) ^ 7 / 7 := log_one_add_le7 (0:ℝ) (by norm_num)
  calc
    (3:ℝ) * Real.log 2 + Real.log (1 + (0:ℝ)) ≤ (3:ℝ) * ((108304247:ℝ)/156250000) + (0:ℝ) - (0:ℝ) ^ 2 / 2 + (0:ℝ) ^ 3 / 3 - (0:ℝ) ^ 4 / 4 + (0:ℝ) ^ 5 / 5 - (0:ℝ) ^ 6 / 6 + (0:ℝ) ^ 7 / 7 := by
      nlinarith
    _ = ((324912741:ℝ)/156250000) := by norm_num

private lemma vlog_ub_m17_2 : Real.log ((17:ℝ)/2) ≤ ((117811155957512051:ℝ)/55050240000000000) := by
  have hdec : ((17:ℝ)/2) = (2:ℝ)^(3) * (1 + ((1:ℝ)/16)) := by norm_num
  have harg' : 1 + ((1:ℝ)/16) ≠ 0 := by norm_num
  rw [hdec]
  rw [Real.log_mul (by positivity : (2:ℝ)^(3) ≠ 0) harg']
  rw [Real.log_pow]
  have h1 : (3:ℝ) * Real.log 2 ≤ (3:ℝ) * ((108304247:ℝ)/156250000) := by
    have hb : Real.log 2 ≤ ((108304247:ℝ)/156250000) := by
      have h := log_two_lt_d9
      norm_num at h ⊢
      linarith
    exact mul_le_mul_of_nonneg_left hb (by norm_num)
  have h2 : Real.log (1 + ((1:ℝ)/16)) ≤ ((1:ℝ)/16) - ((1:ℝ)/16) ^ 2 / 2 + ((1:ℝ)/16) ^ 3 / 3 - ((1:ℝ)/16) ^ 4 / 4 + ((1:ℝ)/16) ^ 5 / 5 - ((1:ℝ)/16) ^ 6 / 6 + ((1:ℝ)/16) ^ 7 / 7 := log_one_add_le7 ((1:ℝ)/16) (by norm_num)
  calc
    (3:ℝ) * Real.log 2 + Real.log (1 + ((1:ℝ)/16)) ≤ (3:ℝ) * ((108304247:ℝ)/156250000) + ((1:ℝ)/16) - ((1:ℝ)/16) ^ 2 / 2 + ((1:ℝ)/16) ^ 3 / 3 - ((1:ℝ)/16) ^ 4 / 4 + ((1:ℝ)/16) ^ 5 / 5 - ((1:ℝ)/16) ^ 6 / 6 + ((1:ℝ)/16) ^ 7 / 7 := by
      nlinarith
    _ = ((117811155957512051:ℝ)/55050240000000000) := by norm_num

private lemma vlog_ub_m41_4 : Real.log ((41:ℝ)/4) ≤ ((5466342908420904801:ℝ)/2348810240000000000) := by
  have hdec : ((41:ℝ)/4) = (2:ℝ)^(3) * (1 + ((9:ℝ)/32)) := by norm_num
  have harg' : 1 + ((9:ℝ)/32) ≠ 0 := by norm_num
  rw [hdec]
  rw [Real.log_mul (by positivity : (2:ℝ)^(3) ≠ 0) harg']
  rw [Real.log_pow]
  have h1 : (3:ℝ) * Real.log 2 ≤ (3:ℝ) * ((108304247:ℝ)/156250000) := by
    have hb : Real.log 2 ≤ ((108304247:ℝ)/156250000) := by
      have h := log_two_lt_d9
      norm_num at h ⊢
      linarith
    exact mul_le_mul_of_nonneg_left hb (by norm_num)
  have h2 : Real.log (1 + ((9:ℝ)/32)) ≤ ((9:ℝ)/32) - ((9:ℝ)/32) ^ 2 / 2 + ((9:ℝ)/32) ^ 3 / 3 - ((9:ℝ)/32) ^ 4 / 4 + ((9:ℝ)/32) ^ 5 / 5 - ((9:ℝ)/32) ^ 6 / 6 + ((9:ℝ)/32) ^ 7 / 7 := log_one_add_le7 ((9:ℝ)/32) (by norm_num)
  calc
    (3:ℝ) * Real.log 2 + Real.log (1 + ((9:ℝ)/32)) ≤ (3:ℝ) * ((108304247:ℝ)/156250000) + ((9:ℝ)/32) - ((9:ℝ)/32) ^ 2 / 2 + ((9:ℝ)/32) ^ 3 / 3 - ((9:ℝ)/32) ^ 4 / 4 + ((9:ℝ)/32) ^ 5 / 5 - ((9:ℝ)/32) ^ 6 / 6 + ((9:ℝ)/32) ^ 7 / 7 := by
      nlinarith
    _ = ((5466342908420904801:ℝ)/2348810240000000000) := by norm_num

private lemma vlog_ub_m261_25 : Real.log ((261:ℝ)/25) ≤ ((210170414873381121:ℝ)/89600000000000000) := by
  have hdec : ((261:ℝ)/25) = (2:ℝ)^(3) * (1 + ((61:ℝ)/200)) := by norm_num
  have harg' : 1 + ((61:ℝ)/200) ≠ 0 := by norm_num
  rw [hdec]
  rw [Real.log_mul (by positivity : (2:ℝ)^(3) ≠ 0) harg']
  rw [Real.log_pow]
  have h1 : (3:ℝ) * Real.log 2 ≤ (3:ℝ) * ((108304247:ℝ)/156250000) := by
    have hb : Real.log 2 ≤ ((108304247:ℝ)/156250000) := by
      have h := log_two_lt_d9
      norm_num at h ⊢
      linarith
    exact mul_le_mul_of_nonneg_left hb (by norm_num)
  have h2 : Real.log (1 + ((61:ℝ)/200)) ≤ ((61:ℝ)/200) - ((61:ℝ)/200) ^ 2 / 2 + ((61:ℝ)/200) ^ 3 / 3 - ((61:ℝ)/200) ^ 4 / 4 + ((61:ℝ)/200) ^ 5 / 5 - ((61:ℝ)/200) ^ 6 / 6 + ((61:ℝ)/200) ^ 7 / 7 := log_one_add_le7 ((61:ℝ)/200) (by norm_num)
  calc
    (3:ℝ) * Real.log 2 + Real.log (1 + ((61:ℝ)/200)) ≤ (3:ℝ) * ((108304247:ℝ)/156250000) + ((61:ℝ)/200) - ((61:ℝ)/200) ^ 2 / 2 + ((61:ℝ)/200) ^ 3 / 3 - ((61:ℝ)/200) ^ 4 / 4 + ((61:ℝ)/200) ^ 5 / 5 - ((61:ℝ)/200) ^ 6 / 6 + ((61:ℝ)/200) ^ 7 / 7 := by
      nlinarith
    _ = ((210170414873381121:ℝ)/89600000000000000) := by norm_num

private lemma vlog_ub_m45_4 : Real.log ((45:ℝ)/4) ≤ ((5685145627975592301:ℝ)/2348810240000000000) := by
  have hdec : ((45:ℝ)/4) = (2:ℝ)^(3) * (1 + ((13:ℝ)/32)) := by norm_num
  have harg' : 1 + ((13:ℝ)/32) ≠ 0 := by norm_num
  rw [hdec]
  rw [Real.log_mul (by positivity : (2:ℝ)^(3) ≠ 0) harg']
  rw [Real.log_pow]
  have h1 : (3:ℝ) * Real.log 2 ≤ (3:ℝ) * ((108304247:ℝ)/156250000) := by
    have hb : Real.log 2 ≤ ((108304247:ℝ)/156250000) := by
      have h := log_two_lt_d9
      norm_num at h ⊢
      linarith
    exact mul_le_mul_of_nonneg_left hb (by norm_num)
  have h2 : Real.log (1 + ((13:ℝ)/32)) ≤ ((13:ℝ)/32) - ((13:ℝ)/32) ^ 2 / 2 + ((13:ℝ)/32) ^ 3 / 3 - ((13:ℝ)/32) ^ 4 / 4 + ((13:ℝ)/32) ^ 5 / 5 - ((13:ℝ)/32) ^ 6 / 6 + ((13:ℝ)/32) ^ 7 / 7 := log_one_add_le7 ((13:ℝ)/32) (by norm_num)
  calc
    (3:ℝ) * Real.log 2 + Real.log (1 + ((13:ℝ)/32)) ≤ (3:ℝ) * ((108304247:ℝ)/156250000) + ((13:ℝ)/32) - ((13:ℝ)/32) ^ 2 / 2 + ((13:ℝ)/32) ^ 3 / 3 - ((13:ℝ)/32) ^ 4 / 4 + ((13:ℝ)/32) ^ 5 / 5 - ((13:ℝ)/32) ^ 6 / 6 + ((13:ℝ)/32) ^ 7 / 7 := by
      nlinarith
    _ = ((5685145627975592301:ℝ)/2348810240000000000) := by norm_num

private lemma vlog_ub_m13 : Real.log (13:ℝ) ≤ ((840483062271301:ℝ)/327680000000000) := by
  have hdec : (13:ℝ) = (2:ℝ)^(4) * (1 - ((3:ℝ)/16)) := by norm_num
  have harg' : 1 - ((3:ℝ)/16) ≠ 0 := by norm_num
  rw [hdec]
  rw [Real.log_mul (by positivity : (2:ℝ)^(4) ≠ 0) harg']
  rw [Real.log_pow]
  have h1 : (4:ℝ) * Real.log 2 ≤ (4:ℝ) * ((108304247:ℝ)/156250000) := by
    have hb : Real.log 2 ≤ ((108304247:ℝ)/156250000) := by
      have h := log_two_lt_d9
      norm_num at h ⊢
      linarith
    exact mul_le_mul_of_nonneg_left hb (by norm_num)
  have h2 : Real.log (1 - ((3:ℝ)/16)) ≤ -( ((3:ℝ)/16) + ((3:ℝ)/16) ^ 2 / 2 + ((3:ℝ)/16) ^ 3 / 3 + ((3:ℝ)/16) ^ 4 / 4 + ((3:ℝ)/16) ^ 5 / 5 + ((3:ℝ)/16) ^ 6 / 6 ) := log_one_sub_le6 ((3:ℝ)/16) (by norm_num) (by norm_num : ((3:ℝ)/16) ≤ (1:ℝ)/2)
  calc
    (4:ℝ) * Real.log 2 + Real.log (1 - ((3:ℝ)/16)) ≤ (4:ℝ) * ((108304247:ℝ)/156250000) + -( ((3:ℝ)/16) + ((3:ℝ)/16) ^ 2 / 2 + ((3:ℝ)/16) ^ 3 / 3 + ((3:ℝ)/16) ^ 4 / 4 + ((3:ℝ)/16) ^ 5 / 5 + ((3:ℝ)/16) ^ 6 / 6 ) := by
      nlinarith
    _ = ((840483062271301:ℝ)/327680000000000) := by norm_num

private lemma vlog_ub_m61_4 : Real.log ((61:ℝ)/4) ≤ ((3656868707940202021:ℝ)/1342177280000000000) := by
  have hdec : ((61:ℝ)/4) = (2:ℝ)^(4) * (1 - ((3:ℝ)/64)) := by norm_num
  have harg' : 1 - ((3:ℝ)/64) ≠ 0 := by norm_num
  rw [hdec]
  rw [Real.log_mul (by positivity : (2:ℝ)^(4) ≠ 0) harg']
  rw [Real.log_pow]
  have h1 : (4:ℝ) * Real.log 2 ≤ (4:ℝ) * ((108304247:ℝ)/156250000) := by
    have hb : Real.log 2 ≤ ((108304247:ℝ)/156250000) := by
      have h := log_two_lt_d9
      norm_num at h ⊢
      linarith
    exact mul_le_mul_of_nonneg_left hb (by norm_num)
  have h2 : Real.log (1 - ((3:ℝ)/64)) ≤ -( ((3:ℝ)/64) + ((3:ℝ)/64) ^ 2 / 2 + ((3:ℝ)/64) ^ 3 / 3 + ((3:ℝ)/64) ^ 4 / 4 + ((3:ℝ)/64) ^ 5 / 5 + ((3:ℝ)/64) ^ 6 / 6 ) := log_one_sub_le6 ((3:ℝ)/64) (by norm_num) (by norm_num : ((3:ℝ)/64) ≤ (1:ℝ)/2)
  calc
    (4:ℝ) * Real.log 2 + Real.log (1 - ((3:ℝ)/64)) ≤ (4:ℝ) * ((108304247:ℝ)/156250000) + -( ((3:ℝ)/64) + ((3:ℝ)/64) ^ 2 / 2 + ((3:ℝ)/64) ^ 3 / 3 + ((3:ℝ)/64) ^ 4 / 4 + ((3:ℝ)/64) ^ 5 / 5 + ((3:ℝ)/64) ^ 6 / 6 ) := by
      nlinarith
    _ = ((3656868707940202021:ℝ)/1342177280000000000) := by norm_num

private lemma vlog_ub_m436_25 : Real.log ((436:ℝ)/25) ≤ ((2001136493957519:ℝ)/700000000000000) := by
  have hdec : ((436:ℝ)/25) = (2:ℝ)^(4) * (1 + ((9:ℝ)/100)) := by norm_num
  have harg' : 1 + ((9:ℝ)/100) ≠ 0 := by norm_num
  rw [hdec]
  rw [Real.log_mul (by positivity : (2:ℝ)^(4) ≠ 0) harg']
  rw [Real.log_pow]
  have h1 : (4:ℝ) * Real.log 2 ≤ (4:ℝ) * ((108304247:ℝ)/156250000) := by
    have hb : Real.log 2 ≤ ((108304247:ℝ)/156250000) := by
      have h := log_two_lt_d9
      norm_num at h ⊢
      linarith
    exact mul_le_mul_of_nonneg_left hb (by norm_num)
  have h2 : Real.log (1 + ((9:ℝ)/100)) ≤ ((9:ℝ)/100) - ((9:ℝ)/100) ^ 2 / 2 + ((9:ℝ)/100) ^ 3 / 3 - ((9:ℝ)/100) ^ 4 / 4 + ((9:ℝ)/100) ^ 5 / 5 - ((9:ℝ)/100) ^ 6 / 6 + ((9:ℝ)/100) ^ 7 / 7 := log_one_add_le7 ((9:ℝ)/100) (by norm_num)
  calc
    (4:ℝ) * Real.log 2 + Real.log (1 + ((9:ℝ)/100)) ≤ (4:ℝ) * ((108304247:ℝ)/156250000) + ((9:ℝ)/100) - ((9:ℝ)/100) ^ 2 / 2 + ((9:ℝ)/100) ^ 3 / 3 - ((9:ℝ)/100) ^ 4 / 4 + ((9:ℝ)/100) ^ 5 / 5 - ((9:ℝ)/100) ^ 6 / 6 + ((9:ℝ)/100) ^ 7 / 7 := by
      nlinarith
    _ = ((2001136493957519:ℝ)/700000000000000) := by norm_num

private lemma vlog_ub_m18 : Real.log (18:ℝ) ≤ ((414363696311077:ℝ)/143360000000000) := by
  have hdec : (18:ℝ) = (2:ℝ)^(4) * (1 + ((1:ℝ)/8)) := by norm_num
  have harg' : 1 + ((1:ℝ)/8) ≠ 0 := by norm_num
  rw [hdec]
  rw [Real.log_mul (by positivity : (2:ℝ)^(4) ≠ 0) harg']
  rw [Real.log_pow]
  have h1 : (4:ℝ) * Real.log 2 ≤ (4:ℝ) * ((108304247:ℝ)/156250000) := by
    have hb : Real.log 2 ≤ ((108304247:ℝ)/156250000) := by
      have h := log_two_lt_d9
      norm_num at h ⊢
      linarith
    exact mul_le_mul_of_nonneg_left hb (by norm_num)
  have h2 : Real.log (1 + ((1:ℝ)/8)) ≤ ((1:ℝ)/8) - ((1:ℝ)/8) ^ 2 / 2 + ((1:ℝ)/8) ^ 3 / 3 - ((1:ℝ)/8) ^ 4 / 4 + ((1:ℝ)/8) ^ 5 / 5 - ((1:ℝ)/8) ^ 6 / 6 + ((1:ℝ)/8) ^ 7 / 7 := log_one_add_le7 ((1:ℝ)/8) (by norm_num)
  calc
    (4:ℝ) * Real.log 2 + Real.log (1 + ((1:ℝ)/8)) ≤ (4:ℝ) * ((108304247:ℝ)/156250000) + ((1:ℝ)/8) - ((1:ℝ)/8) ^ 2 / 2 + ((1:ℝ)/8) ^ 3 / 3 - ((1:ℝ)/8) ^ 4 / 4 + ((1:ℝ)/8) ^ 5 / 5 - ((1:ℝ)/8) ^ 6 / 6 + ((1:ℝ)/8) ^ 7 / 7 := by
      nlinarith
    _ = ((414363696311077:ℝ)/143360000000000) := by norm_num

private lemma vlog_ub_m73_4 : Real.log ((73:ℝ)/4) ≤ ((873130588261786893329:ℝ)/300647710720000000000) := by
  have hdec : ((73:ℝ)/4) = (2:ℝ)^(4) * (1 + ((9:ℝ)/64)) := by norm_num
  have harg' : 1 + ((9:ℝ)/64) ≠ 0 := by norm_num
  rw [hdec]
  rw [Real.log_mul (by positivity : (2:ℝ)^(4) ≠ 0) harg']
  rw [Real.log_pow]
  have h1 : (4:ℝ) * Real.log 2 ≤ (4:ℝ) * ((108304247:ℝ)/156250000) := by
    have hb : Real.log 2 ≤ ((108304247:ℝ)/156250000) := by
      have h := log_two_lt_d9
      norm_num at h ⊢
      linarith
    exact mul_le_mul_of_nonneg_left hb (by norm_num)
  have h2 : Real.log (1 + ((9:ℝ)/64)) ≤ ((9:ℝ)/64) - ((9:ℝ)/64) ^ 2 / 2 + ((9:ℝ)/64) ^ 3 / 3 - ((9:ℝ)/64) ^ 4 / 4 + ((9:ℝ)/64) ^ 5 / 5 - ((9:ℝ)/64) ^ 6 / 6 + ((9:ℝ)/64) ^ 7 / 7 := log_one_add_le7 ((9:ℝ)/64) (by norm_num)
  calc
    (4:ℝ) * Real.log 2 + Real.log (1 + ((9:ℝ)/64)) ≤ (4:ℝ) * ((108304247:ℝ)/156250000) + ((9:ℝ)/64) - ((9:ℝ)/64) ^ 2 / 2 + ((9:ℝ)/64) ^ 3 / 3 - ((9:ℝ)/64) ^ 4 / 4 + ((9:ℝ)/64) ^ 5 / 5 - ((9:ℝ)/64) ^ 6 / 6 + ((9:ℝ)/64) ^ 7 / 7 := by
      nlinarith
    _ = ((873130588261786893329:ℝ)/300647710720000000000) := by norm_num

private lemma vlog_ub_m20 : Real.log (20:ℝ) ≤ ((10065665688077:ℝ)/3360000000000) := by
  have hdec : (20:ℝ) = (2:ℝ)^(4) * (1 + ((1:ℝ)/4)) := by norm_num
  have harg' : 1 + ((1:ℝ)/4) ≠ 0 := by norm_num
  rw [hdec]
  rw [Real.log_mul (by positivity : (2:ℝ)^(4) ≠ 0) harg']
  rw [Real.log_pow]
  have h1 : (4:ℝ) * Real.log 2 ≤ (4:ℝ) * ((108304247:ℝ)/156250000) := by
    have hb : Real.log 2 ≤ ((108304247:ℝ)/156250000) := by
      have h := log_two_lt_d9
      norm_num at h ⊢
      linarith
    exact mul_le_mul_of_nonneg_left hb (by norm_num)
  have h2 : Real.log (1 + ((1:ℝ)/4)) ≤ ((1:ℝ)/4) - ((1:ℝ)/4) ^ 2 / 2 + ((1:ℝ)/4) ^ 3 / 3 - ((1:ℝ)/4) ^ 4 / 4 + ((1:ℝ)/4) ^ 5 / 5 - ((1:ℝ)/4) ^ 6 / 6 + ((1:ℝ)/4) ^ 7 / 7 := log_one_add_le7 ((1:ℝ)/4) (by norm_num)
  calc
    (4:ℝ) * Real.log 2 + Real.log (1 + ((1:ℝ)/4)) ≤ (4:ℝ) * ((108304247:ℝ)/156250000) + ((1:ℝ)/4) - ((1:ℝ)/4) ^ 2 / 2 + ((1:ℝ)/4) ^ 3 / 3 - ((1:ℝ)/4) ^ 4 / 4 + ((1:ℝ)/4) ^ 5 / 5 - ((1:ℝ)/4) ^ 6 / 6 + ((1:ℝ)/4) ^ 7 / 7 := by
      nlinarith
    _ = ((10065665688077:ℝ)/3360000000000) := by norm_num

private lemma vlog_ub_m89_4 : Real.log ((89:ℝ)/4) ≤ ((2798181474511641929987:ℝ)/901943132160000000000) := by
  have hdec : ((89:ℝ)/4) = (2:ℝ)^(4) * (1 + ((25:ℝ)/64)) := by norm_num
  have harg' : 1 + ((25:ℝ)/64) ≠ 0 := by norm_num
  rw [hdec]
  rw [Real.log_mul (by positivity : (2:ℝ)^(4) ≠ 0) harg']
  rw [Real.log_pow]
  have h1 : (4:ℝ) * Real.log 2 ≤ (4:ℝ) * ((108304247:ℝ)/156250000) := by
    have hb : Real.log 2 ≤ ((108304247:ℝ)/156250000) := by
      have h := log_two_lt_d9
      norm_num at h ⊢
      linarith
    exact mul_le_mul_of_nonneg_left hb (by norm_num)
  have h2 : Real.log (1 + ((25:ℝ)/64)) ≤ ((25:ℝ)/64) - ((25:ℝ)/64) ^ 2 / 2 + ((25:ℝ)/64) ^ 3 / 3 - ((25:ℝ)/64) ^ 4 / 4 + ((25:ℝ)/64) ^ 5 / 5 - ((25:ℝ)/64) ^ 6 / 6 + ((25:ℝ)/64) ^ 7 / 7 := log_one_add_le7 ((25:ℝ)/64) (by norm_num)
  calc
    (4:ℝ) * Real.log 2 + Real.log (1 + ((25:ℝ)/64)) ≤ (4:ℝ) * ((108304247:ℝ)/156250000) + ((25:ℝ)/64) - ((25:ℝ)/64) ^ 2 / 2 + ((25:ℝ)/64) ^ 3 / 3 - ((25:ℝ)/64) ^ 4 / 4 + ((25:ℝ)/64) ^ 5 / 5 - ((25:ℝ)/64) ^ 6 / 6 + ((25:ℝ)/64) ^ 7 / 7 := by
      nlinarith
    _ = ((2798181474511641929987:ℝ)/901943132160000000000) := by norm_num

private lemma vlog_ub_m25 : Real.log (25:ℝ) ≤ ((40502884587069323:ℝ)/12582912000000000) := by
  have hdec : (25:ℝ) = (2:ℝ)^(5) * (1 - ((7:ℝ)/32)) := by norm_num
  have harg' : 1 - ((7:ℝ)/32) ≠ 0 := by norm_num
  rw [hdec]
  rw [Real.log_mul (by positivity : (2:ℝ)^(5) ≠ 0) harg']
  rw [Real.log_pow]
  have h1 : (5:ℝ) * Real.log 2 ≤ (5:ℝ) * ((108304247:ℝ)/156250000) := by
    have hb : Real.log 2 ≤ ((108304247:ℝ)/156250000) := by
      have h := log_two_lt_d9
      norm_num at h ⊢
      linarith
    exact mul_le_mul_of_nonneg_left hb (by norm_num)
  have h2 : Real.log (1 - ((7:ℝ)/32)) ≤ -( ((7:ℝ)/32) + ((7:ℝ)/32) ^ 2 / 2 + ((7:ℝ)/32) ^ 3 / 3 + ((7:ℝ)/32) ^ 4 / 4 + ((7:ℝ)/32) ^ 5 / 5 + ((7:ℝ)/32) ^ 6 / 6 ) := log_one_sub_le6 ((7:ℝ)/32) (by norm_num) (by norm_num : ((7:ℝ)/32) ≤ (1:ℝ)/2)
  calc
    (5:ℝ) * Real.log 2 + Real.log (1 - ((7:ℝ)/32)) ≤ (5:ℝ) * ((108304247:ℝ)/156250000) + -( ((7:ℝ)/32) + ((7:ℝ)/32) ^ 2 / 2 + ((7:ℝ)/32) ^ 3 / 3 + ((7:ℝ)/32) ^ 4 / 4 + ((7:ℝ)/32) ^ 5 / 5 + ((7:ℝ)/32) ^ 6 / 6 ) := by
      nlinarith
    _ = ((40502884587069323:ℝ)/12582912000000000) := by norm_num

private lemma vlog_ub_m32 : Real.log (32:ℝ) ≤ ((108304247:ℝ)/31250000) := by
  have hdec : (32:ℝ) = (2:ℝ)^(5) * (1 + (0:ℝ)) := by norm_num
  have harg' : 1 + (0:ℝ) ≠ 0 := by norm_num
  rw [hdec]
  rw [Real.log_mul (by positivity : (2:ℝ)^(5) ≠ 0) harg']
  rw [Real.log_pow]
  have h1 : (5:ℝ) * Real.log 2 ≤ (5:ℝ) * ((108304247:ℝ)/156250000) := by
    have hb : Real.log 2 ≤ ((108304247:ℝ)/156250000) := by
      have h := log_two_lt_d9
      norm_num at h ⊢
      linarith
    exact mul_le_mul_of_nonneg_left hb (by norm_num)
  have h2 : Real.log (1 + (0:ℝ)) ≤ (0:ℝ) - (0:ℝ) ^ 2 / 2 + (0:ℝ) ^ 3 / 3 - (0:ℝ) ^ 4 / 4 + (0:ℝ) ^ 5 / 5 - (0:ℝ) ^ 6 / 6 + (0:ℝ) ^ 7 / 7 := log_one_add_le7 (0:ℝ) (by norm_num)
  calc
    (5:ℝ) * Real.log 2 + Real.log (1 + (0:ℝ)) ≤ (5:ℝ) * ((108304247:ℝ)/156250000) + (0:ℝ) - (0:ℝ) ^ 2 / 2 + (0:ℝ) ^ 3 / 3 - (0:ℝ) ^ 4 / 4 + (0:ℝ) ^ 5 / 5 - (0:ℝ) ^ 6 / 6 + (0:ℝ) ^ 7 / 7 := by
      nlinarith
    _ = ((108304247:ℝ)/31250000) := by norm_num

private lemma vlog_ub_m936_25 : Real.log ((936:ℝ)/25) ≤ ((2535917810003623:ℝ)/700000000000000) := by
  have hdec : ((936:ℝ)/25) = (2:ℝ)^(5) * (1 + ((17:ℝ)/100)) := by norm_num
  have harg' : 1 + ((17:ℝ)/100) ≠ 0 := by norm_num
  rw [hdec]
  rw [Real.log_mul (by positivity : (2:ℝ)^(5) ≠ 0) harg']
  rw [Real.log_pow]
  have h1 : (5:ℝ) * Real.log 2 ≤ (5:ℝ) * ((108304247:ℝ)/156250000) := by
    have hb : Real.log 2 ≤ ((108304247:ℝ)/156250000) := by
      have h := log_two_lt_d9
      norm_num at h ⊢
      linarith
    exact mul_le_mul_of_nonneg_left hb (by norm_num)
  have h2 : Real.log (1 + ((17:ℝ)/100)) ≤ ((17:ℝ)/100) - ((17:ℝ)/100) ^ 2 / 2 + ((17:ℝ)/100) ^ 3 / 3 - ((17:ℝ)/100) ^ 4 / 4 + ((17:ℝ)/100) ^ 5 / 5 - ((17:ℝ)/100) ^ 6 / 6 + ((17:ℝ)/100) ^ 7 / 7 := log_one_add_le7 ((17:ℝ)/100) (by norm_num)
  calc
    (5:ℝ) * Real.log 2 + Real.log (1 + ((17:ℝ)/100)) ≤ (5:ℝ) * ((108304247:ℝ)/156250000) + ((17:ℝ)/100) - ((17:ℝ)/100) ^ 2 / 2 + ((17:ℝ)/100) ^ 3 / 3 - ((17:ℝ)/100) ^ 4 / 4 + ((17:ℝ)/100) ^ 5 / 5 - ((17:ℝ)/100) ^ 6 / 6 + ((17:ℝ)/100) ^ 7 / 7 := by
      nlinarith
    _ = ((2535917810003623:ℝ)/700000000000000) := by norm_num

private lemma vlog_ub_m153_4 : Real.log ((153:ℝ)/4) ≤ ((28047449270254698164653:ℝ)/7696581394432000000000) := by
  have hdec : ((153:ℝ)/4) = (2:ℝ)^(5) * (1 + ((25:ℝ)/128)) := by norm_num
  have harg' : 1 + ((25:ℝ)/128) ≠ 0 := by norm_num
  rw [hdec]
  rw [Real.log_mul (by positivity : (2:ℝ)^(5) ≠ 0) harg']
  rw [Real.log_pow]
  have h1 : (5:ℝ) * Real.log 2 ≤ (5:ℝ) * ((108304247:ℝ)/156250000) := by
    have hb : Real.log 2 ≤ ((108304247:ℝ)/156250000) := by
      have h := log_two_lt_d9
      norm_num at h ⊢
      linarith
    exact mul_le_mul_of_nonneg_left hb (by norm_num)
  have h2 : Real.log (1 + ((25:ℝ)/128)) ≤ ((25:ℝ)/128) - ((25:ℝ)/128) ^ 2 / 2 + ((25:ℝ)/128) ^ 3 / 3 - ((25:ℝ)/128) ^ 4 / 4 + ((25:ℝ)/128) ^ 5 / 5 - ((25:ℝ)/128) ^ 6 / 6 + ((25:ℝ)/128) ^ 7 / 7 := log_one_add_le7 ((25:ℝ)/128) (by norm_num)
  calc
    (5:ℝ) * Real.log 2 + Real.log (1 + ((25:ℝ)/128)) ≤ (5:ℝ) * ((108304247:ℝ)/156250000) + ((25:ℝ)/128) - ((25:ℝ)/128) ^ 2 / 2 + ((25:ℝ)/128) ^ 3 / 3 - ((25:ℝ)/128) ^ 4 / 4 + ((25:ℝ)/128) ^ 5 / 5 - ((25:ℝ)/128) ^ 6 / 6 + ((25:ℝ)/128) ^ 7 / 7 := by
      nlinarith
    _ = ((28047449270254698164653:ℝ)/7696581394432000000000) := by norm_num

private lemma vlog_ub_m40 : Real.log (40:ℝ) ≤ ((2478928043113:ℝ)/672000000000) := by
  have hdec : (40:ℝ) = (2:ℝ)^(5) * (1 + ((1:ℝ)/4)) := by norm_num
  have harg' : 1 + ((1:ℝ)/4) ≠ 0 := by norm_num
  rw [hdec]
  rw [Real.log_mul (by positivity : (2:ℝ)^(5) ≠ 0) harg']
  rw [Real.log_pow]
  have h1 : (5:ℝ) * Real.log 2 ≤ (5:ℝ) * ((108304247:ℝ)/156250000) := by
    have hb : Real.log 2 ≤ ((108304247:ℝ)/156250000) := by
      have h := log_two_lt_d9
      norm_num at h ⊢
      linarith
    exact mul_le_mul_of_nonneg_left hb (by norm_num)
  have h2 : Real.log (1 + ((1:ℝ)/4)) ≤ ((1:ℝ)/4) - ((1:ℝ)/4) ^ 2 / 2 + ((1:ℝ)/4) ^ 3 / 3 - ((1:ℝ)/4) ^ 4 / 4 + ((1:ℝ)/4) ^ 5 / 5 - ((1:ℝ)/4) ^ 6 / 6 + ((1:ℝ)/4) ^ 7 / 7 := log_one_add_le7 ((1:ℝ)/4) (by norm_num)
  calc
    (5:ℝ) * Real.log 2 + Real.log (1 + ((1:ℝ)/4)) ≤ (5:ℝ) * ((108304247:ℝ)/156250000) + ((1:ℝ)/4) - ((1:ℝ)/4) ^ 2 / 2 + ((1:ℝ)/4) ^ 3 / 3 - ((1:ℝ)/4) ^ 4 / 4 + ((1:ℝ)/4) ^ 5 / 5 - ((1:ℝ)/4) ^ 6 / 6 + ((1:ℝ)/4) ^ 7 / 7 := by
      nlinarith
    _ = ((2478928043113:ℝ)/672000000000) := by norm_num

private lemma vlog_ub_m169_4 : Real.log ((169:ℝ)/4) ≤ ((86439115988623150743959:ℝ)/23089744183296000000000) := by
  have hdec : ((169:ℝ)/4) = (2:ℝ)^(5) * (1 + ((41:ℝ)/128)) := by norm_num
  have harg' : 1 + ((41:ℝ)/128) ≠ 0 := by norm_num
  rw [hdec]
  rw [Real.log_mul (by positivity : (2:ℝ)^(5) ≠ 0) harg']
  rw [Real.log_pow]
  have h1 : (5:ℝ) * Real.log 2 ≤ (5:ℝ) * ((108304247:ℝ)/156250000) := by
    have hb : Real.log 2 ≤ ((108304247:ℝ)/156250000) := by
      have h := log_two_lt_d9
      norm_num at h ⊢
      linarith
    exact mul_le_mul_of_nonneg_left hb (by norm_num)
  have h2 : Real.log (1 + ((41:ℝ)/128)) ≤ ((41:ℝ)/128) - ((41:ℝ)/128) ^ 2 / 2 + ((41:ℝ)/128) ^ 3 / 3 - ((41:ℝ)/128) ^ 4 / 4 + ((41:ℝ)/128) ^ 5 / 5 - ((41:ℝ)/128) ^ 6 / 6 + ((41:ℝ)/128) ^ 7 / 7 := log_one_add_le7 ((41:ℝ)/128) (by norm_num)
  calc
    (5:ℝ) * Real.log 2 + Real.log (1 + ((41:ℝ)/128)) ≤ (5:ℝ) * ((108304247:ℝ)/156250000) + ((41:ℝ)/128) - ((41:ℝ)/128) ^ 2 / 2 + ((41:ℝ)/128) ^ 3 / 3 - ((41:ℝ)/128) ^ 4 / 4 + ((41:ℝ)/128) ^ 5 / 5 - ((41:ℝ)/128) ^ 6 / 6 + ((41:ℝ)/128) ^ 7 / 7 := by
      nlinarith
    _ = ((86439115988623150743959:ℝ)/23089744183296000000000) := by norm_num

private lemma vlog_ub_m45 : Real.log (45:ℝ) ≤ ((1788257604031187017:ℝ)/469762048000000000) := by
  have hdec : (45:ℝ) = (2:ℝ)^(5) * (1 + ((13:ℝ)/32)) := by norm_num
  have harg' : 1 + ((13:ℝ)/32) ≠ 0 := by norm_num
  rw [hdec]
  rw [Real.log_mul (by positivity : (2:ℝ)^(5) ≠ 0) harg']
  rw [Real.log_pow]
  have h1 : (5:ℝ) * Real.log 2 ≤ (5:ℝ) * ((108304247:ℝ)/156250000) := by
    have hb : Real.log 2 ≤ ((108304247:ℝ)/156250000) := by
      have h := log_two_lt_d9
      norm_num at h ⊢
      linarith
    exact mul_le_mul_of_nonneg_left hb (by norm_num)
  have h2 : Real.log (1 + ((13:ℝ)/32)) ≤ ((13:ℝ)/32) - ((13:ℝ)/32) ^ 2 / 2 + ((13:ℝ)/32) ^ 3 / 3 - ((13:ℝ)/32) ^ 4 / 4 + ((13:ℝ)/32) ^ 5 / 5 - ((13:ℝ)/32) ^ 6 / 6 + ((13:ℝ)/32) ^ 7 / 7 := log_one_add_le7 ((13:ℝ)/32) (by norm_num)
  calc
    (5:ℝ) * Real.log 2 + Real.log (1 + ((13:ℝ)/32)) ≤ (5:ℝ) * ((108304247:ℝ)/156250000) + ((13:ℝ)/32) - ((13:ℝ)/32) ^ 2 / 2 + ((13:ℝ)/32) ^ 3 / 3 - ((13:ℝ)/32) ^ 4 / 4 + ((13:ℝ)/32) ^ 5 / 5 - ((13:ℝ)/32) ^ 6 / 6 + ((13:ℝ)/32) ^ 7 / 7 := by
      nlinarith
    _ = ((1788257604031187017:ℝ)/469762048000000000) := by norm_num

private lemma vlog_ub_m52 : Real.log (52:ℝ) ≤ ((1294743998680389:ℝ)/327680000000000) := by
  have hdec : (52:ℝ) = (2:ℝ)^(6) * (1 - ((3:ℝ)/16)) := by norm_num
  have harg' : 1 - ((3:ℝ)/16) ≠ 0 := by norm_num
  rw [hdec]
  rw [Real.log_mul (by positivity : (2:ℝ)^(6) ≠ 0) harg']
  rw [Real.log_pow]
  have h1 : (6:ℝ) * Real.log 2 ≤ (6:ℝ) * ((108304247:ℝ)/156250000) := by
    have hb : Real.log 2 ≤ ((108304247:ℝ)/156250000) := by
      have h := log_two_lt_d9
      norm_num at h ⊢
      linarith
    exact mul_le_mul_of_nonneg_left hb (by norm_num)
  have h2 : Real.log (1 - ((3:ℝ)/16)) ≤ -( ((3:ℝ)/16) + ((3:ℝ)/16) ^ 2 / 2 + ((3:ℝ)/16) ^ 3 / 3 + ((3:ℝ)/16) ^ 4 / 4 + ((3:ℝ)/16) ^ 5 / 5 + ((3:ℝ)/16) ^ 6 / 6 ) := log_one_sub_le6 ((3:ℝ)/16) (by norm_num) (by norm_num : ((3:ℝ)/16) ≤ (1:ℝ)/2)
  calc
    (6:ℝ) * Real.log 2 + Real.log (1 - ((3:ℝ)/16)) ≤ (6:ℝ) * ((108304247:ℝ)/156250000) + -( ((3:ℝ)/16) + ((3:ℝ)/16) ^ 2 / 2 + ((3:ℝ)/16) ^ 3 / 3 + ((3:ℝ)/16) ^ 4 / 4 + ((3:ℝ)/16) ^ 5 / 5 + ((3:ℝ)/16) ^ 6 / 6 ) := by
      nlinarith
    _ = ((1294743998680389:ℝ)/327680000000000) := by norm_num

private lemma vlog_ub_m265_4 : Real.log ((265:ℝ)/4) ≤ ((20656075128786747122094129:ℝ)/4925812092436480000000000) := by
  have hdec : ((265:ℝ)/4) = (2:ℝ)^(6) * (1 + ((9:ℝ)/256)) := by norm_num
  have harg' : 1 + ((9:ℝ)/256) ≠ 0 := by norm_num
  rw [hdec]
  rw [Real.log_mul (by positivity : (2:ℝ)^(6) ≠ 0) harg']
  rw [Real.log_pow]
  have h1 : (6:ℝ) * Real.log 2 ≤ (6:ℝ) * ((108304247:ℝ)/156250000) := by
    have hb : Real.log 2 ≤ ((108304247:ℝ)/156250000) := by
      have h := log_two_lt_d9
      norm_num at h ⊢
      linarith
    exact mul_le_mul_of_nonneg_left hb (by norm_num)
  have h2 : Real.log (1 + ((9:ℝ)/256)) ≤ ((9:ℝ)/256) - ((9:ℝ)/256) ^ 2 / 2 + ((9:ℝ)/256) ^ 3 / 3 - ((9:ℝ)/256) ^ 4 / 4 + ((9:ℝ)/256) ^ 5 / 5 - ((9:ℝ)/256) ^ 6 / 6 + ((9:ℝ)/256) ^ 7 / 7 := log_one_add_le7 ((9:ℝ)/256) (by norm_num)
  calc
    (6:ℝ) * Real.log 2 + Real.log (1 + ((9:ℝ)/256)) ≤ (6:ℝ) * ((108304247:ℝ)/156250000) + ((9:ℝ)/256) - ((9:ℝ)/256) ^ 2 / 2 + ((9:ℝ)/256) ^ 3 / 3 - ((9:ℝ)/256) ^ 4 / 4 + ((9:ℝ)/256) ^ 5 / 5 - ((9:ℝ)/256) ^ 6 / 6 + ((9:ℝ)/256) ^ 7 / 7 := by
      nlinarith
    _ = ((20656075128786747122094129:ℝ)/4925812092436480000000000) := by norm_num

private lemma vlog_ub_m68 : Real.log (68:ℝ) ≤ ((232284911932602227:ℝ)/55050240000000000) := by
  have hdec : (68:ℝ) = (2:ℝ)^(6) * (1 + ((1:ℝ)/16)) := by norm_num
  have harg' : 1 + ((1:ℝ)/16) ≠ 0 := by norm_num
  rw [hdec]
  rw [Real.log_mul (by positivity : (2:ℝ)^(6) ≠ 0) harg']
  rw [Real.log_pow]
  have h1 : (6:ℝ) * Real.log 2 ≤ (6:ℝ) * ((108304247:ℝ)/156250000) := by
    have hb : Real.log 2 ≤ ((108304247:ℝ)/156250000) := by
      have h := log_two_lt_d9
      norm_num at h ⊢
      linarith
    exact mul_le_mul_of_nonneg_left hb (by norm_num)
  have h2 : Real.log (1 + ((1:ℝ)/16)) ≤ ((1:ℝ)/16) - ((1:ℝ)/16) ^ 2 / 2 + ((1:ℝ)/16) ^ 3 / 3 - ((1:ℝ)/16) ^ 4 / 4 + ((1:ℝ)/16) ^ 5 / 5 - ((1:ℝ)/16) ^ 6 / 6 + ((1:ℝ)/16) ^ 7 / 7 := log_one_add_le7 ((1:ℝ)/16) (by norm_num)
  calc
    (6:ℝ) * Real.log 2 + Real.log (1 + ((1:ℝ)/16)) ≤ (6:ℝ) * ((108304247:ℝ)/156250000) + ((1:ℝ)/16) - ((1:ℝ)/16) ^ 2 / 2 + ((1:ℝ)/16) ^ 3 / 3 - ((1:ℝ)/16) ^ 4 / 4 + ((1:ℝ)/16) ^ 5 / 5 - ((1:ℝ)/16) ^ 6 / 6 + ((1:ℝ)/16) ^ 7 / 7 := by
      nlinarith
    _ = ((232284911932602227:ℝ)/55050240000000000) := by norm_num

private lemma vlog_ub_m72 : Real.log (72:ℝ) ≤ ((613102855990053:ℝ)/143360000000000) := by
  have hdec : (72:ℝ) = (2:ℝ)^(6) * (1 + ((1:ℝ)/8)) := by norm_num
  have harg' : 1 + ((1:ℝ)/8) ≠ 0 := by norm_num
  rw [hdec]
  rw [Real.log_mul (by positivity : (2:ℝ)^(6) ≠ 0) harg']
  rw [Real.log_pow]
  have h1 : (6:ℝ) * Real.log 2 ≤ (6:ℝ) * ((108304247:ℝ)/156250000) := by
    have hb : Real.log 2 ≤ ((108304247:ℝ)/156250000) := by
      have h := log_two_lt_d9
      norm_num at h ⊢
      linarith
    exact mul_le_mul_of_nonneg_left hb (by norm_num)
  have h2 : Real.log (1 + ((1:ℝ)/8)) ≤ ((1:ℝ)/8) - ((1:ℝ)/8) ^ 2 / 2 + ((1:ℝ)/8) ^ 3 / 3 - ((1:ℝ)/8) ^ 4 / 4 + ((1:ℝ)/8) ^ 5 / 5 - ((1:ℝ)/8) ^ 6 / 6 + ((1:ℝ)/8) ^ 7 / 7 := log_one_add_le7 ((1:ℝ)/8) (by norm_num)
  calc
    (6:ℝ) * Real.log 2 + Real.log (1 + ((1:ℝ)/8)) ≤ (6:ℝ) * ((108304247:ℝ)/156250000) + ((1:ℝ)/8) - ((1:ℝ)/8) ^ 2 / 2 + ((1:ℝ)/8) ^ 3 / 3 - ((1:ℝ)/8) ^ 4 / 4 + ((1:ℝ)/8) ^ 5 / 5 - ((1:ℝ)/8) ^ 6 / 6 + ((1:ℝ)/8) ^ 7 / 7 := by
      nlinarith
    _ = ((613102855990053:ℝ)/143360000000000) := by norm_num

private lemma vlog_ub_m73 : Real.log (73:ℝ) ≤ ((1289916814460870769681:ℝ)/300647710720000000000) := by
  have hdec : (73:ℝ) = (2:ℝ)^(6) * (1 + ((9:ℝ)/64)) := by norm_num
  have harg' : 1 + ((9:ℝ)/64) ≠ 0 := by norm_num
  rw [hdec]
  rw [Real.log_mul (by positivity : (2:ℝ)^(6) ≠ 0) harg']
  rw [Real.log_pow]
  have h1 : (6:ℝ) * Real.log 2 ≤ (6:ℝ) * ((108304247:ℝ)/156250000) := by
    have hb : Real.log 2 ≤ ((108304247:ℝ)/156250000) := by
      have h := log_two_lt_d9
      norm_num at h ⊢
      linarith
    exact mul_le_mul_of_nonneg_left hb (by norm_num)
  have h2 : Real.log (1 + ((9:ℝ)/64)) ≤ ((9:ℝ)/64) - ((9:ℝ)/64) ^ 2 / 2 + ((9:ℝ)/64) ^ 3 / 3 - ((9:ℝ)/64) ^ 4 / 4 + ((9:ℝ)/64) ^ 5 / 5 - ((9:ℝ)/64) ^ 6 / 6 + ((9:ℝ)/64) ^ 7 / 7 := log_one_add_le7 ((9:ℝ)/64) (by norm_num)
  calc
    (6:ℝ) * Real.log 2 + Real.log (1 + ((9:ℝ)/64)) ≤ (6:ℝ) * ((108304247:ℝ)/156250000) + ((9:ℝ)/64) - ((9:ℝ)/64) ^ 2 / 2 + ((9:ℝ)/64) ^ 3 / 3 - ((9:ℝ)/64) ^ 4 / 4 + ((9:ℝ)/64) ^ 5 / 5 - ((9:ℝ)/64) ^ 6 / 6 + ((9:ℝ)/64) ^ 7 / 7 := by
      nlinarith
    _ = ((1289916814460870769681:ℝ)/300647710720000000000) := by norm_num

private lemma vlog_ub_m80 : Real.log (80:ℝ) ≤ ((14723614743053:ℝ)/3360000000000) := by
  have hdec : (80:ℝ) = (2:ℝ)^(6) * (1 + ((1:ℝ)/4)) := by norm_num
  have harg' : 1 + ((1:ℝ)/4) ≠ 0 := by norm_num
  rw [hdec]
  rw [Real.log_mul (by positivity : (2:ℝ)^(6) ≠ 0) harg']
  rw [Real.log_pow]
  have h1 : (6:ℝ) * Real.log 2 ≤ (6:ℝ) * ((108304247:ℝ)/156250000) := by
    have hb : Real.log 2 ≤ ((108304247:ℝ)/156250000) := by
      have h := log_two_lt_d9
      norm_num at h ⊢
      linarith
    exact mul_le_mul_of_nonneg_left hb (by norm_num)
  have h2 : Real.log (1 + ((1:ℝ)/4)) ≤ ((1:ℝ)/4) - ((1:ℝ)/4) ^ 2 / 2 + ((1:ℝ)/4) ^ 3 / 3 - ((1:ℝ)/4) ^ 4 / 4 + ((1:ℝ)/4) ^ 5 / 5 - ((1:ℝ)/4) ^ 6 / 6 + ((1:ℝ)/4) ^ 7 / 7 := log_one_add_le7 ((1:ℝ)/4) (by norm_num)
  calc
    (6:ℝ) * Real.log 2 + Real.log (1 + ((1:ℝ)/4)) ≤ (6:ℝ) * ((108304247:ℝ)/156250000) + ((1:ℝ)/4) - ((1:ℝ)/4) ^ 2 / 2 + ((1:ℝ)/4) ^ 3 / 3 - ((1:ℝ)/4) ^ 4 / 4 + ((1:ℝ)/4) ^ 5 / 5 - ((1:ℝ)/4) ^ 6 / 6 + ((1:ℝ)/4) ^ 7 / 7 := by
      nlinarith
    _ = ((14723614743053:ℝ)/3360000000000) := by norm_num

private lemma vlog_ub_m2061_25 : Real.log ((2061:ℝ)/25) ≤ ((829050246567802806063621:ℝ)/187904819200000000000000) := by
  have hdec : ((2061:ℝ)/25) = (2:ℝ)^(6) * (1 + ((461:ℝ)/1600)) := by norm_num
  have harg' : 1 + ((461:ℝ)/1600) ≠ 0 := by norm_num
  rw [hdec]
  rw [Real.log_mul (by positivity : (2:ℝ)^(6) ≠ 0) harg']
  rw [Real.log_pow]
  have h1 : (6:ℝ) * Real.log 2 ≤ (6:ℝ) * ((108304247:ℝ)/156250000) := by
    have hb : Real.log 2 ≤ ((108304247:ℝ)/156250000) := by
      have h := log_two_lt_d9
      norm_num at h ⊢
      linarith
    exact mul_le_mul_of_nonneg_left hb (by norm_num)
  have h2 : Real.log (1 + ((461:ℝ)/1600)) ≤ ((461:ℝ)/1600) - ((461:ℝ)/1600) ^ 2 / 2 + ((461:ℝ)/1600) ^ 3 / 3 - ((461:ℝ)/1600) ^ 4 / 4 + ((461:ℝ)/1600) ^ 5 / 5 - ((461:ℝ)/1600) ^ 6 / 6 + ((461:ℝ)/1600) ^ 7 / 7 := log_one_add_le7 ((461:ℝ)/1600) (by norm_num)
  calc
    (6:ℝ) * Real.log 2 + Real.log (1 + ((461:ℝ)/1600)) ≤ (6:ℝ) * ((108304247:ℝ)/156250000) + ((461:ℝ)/1600) - ((461:ℝ)/1600) ^ 2 / 2 + ((461:ℝ)/1600) ^ 3 / 3 - ((461:ℝ)/1600) ^ 4 / 4 + ((461:ℝ)/1600) ^ 5 / 5 - ((461:ℝ)/1600) ^ 6 / 6 + ((461:ℝ)/1600) ^ 7 / 7 := by
      nlinarith
    _ = ((829050246567802806063621:ℝ)/187904819200000000000000) := by norm_num

private lemma vlog_ub_m333_4 : Real.log ((333:ℝ)/4) ≤ ((3111603650802786328825947:ℝ)/703687441776640000000000) := by
  have hdec : ((333:ℝ)/4) = (2:ℝ)^(6) * (1 + ((77:ℝ)/256)) := by norm_num
  have harg' : 1 + ((77:ℝ)/256) ≠ 0 := by norm_num
  rw [hdec]
  rw [Real.log_mul (by positivity : (2:ℝ)^(6) ≠ 0) harg']
  rw [Real.log_pow]
  have h1 : (6:ℝ) * Real.log 2 ≤ (6:ℝ) * ((108304247:ℝ)/156250000) := by
    have hb : Real.log 2 ≤ ((108304247:ℝ)/156250000) := by
      have h := log_two_lt_d9
      norm_num at h ⊢
      linarith
    exact mul_le_mul_of_nonneg_left hb (by norm_num)
  have h2 : Real.log (1 + ((77:ℝ)/256)) ≤ ((77:ℝ)/256) - ((77:ℝ)/256) ^ 2 / 2 + ((77:ℝ)/256) ^ 3 / 3 - ((77:ℝ)/256) ^ 4 / 4 + ((77:ℝ)/256) ^ 5 / 5 - ((77:ℝ)/256) ^ 6 / 6 + ((77:ℝ)/256) ^ 7 / 7 := log_one_add_le7 ((77:ℝ)/256) (by norm_num)
  calc
    (6:ℝ) * Real.log 2 + Real.log (1 + ((77:ℝ)/256)) ≤ (6:ℝ) * ((108304247:ℝ)/156250000) + ((77:ℝ)/256) - ((77:ℝ)/256) ^ 2 / 2 + ((77:ℝ)/256) ^ 3 / 3 - ((77:ℝ)/256) ^ 4 / 4 + ((77:ℝ)/256) ^ 5 / 5 - ((77:ℝ)/256) ^ 6 / 6 + ((77:ℝ)/256) ^ 7 / 7 := by
      nlinarith
    _ = ((3111603650802786328825947:ℝ)/703687441776640000000000) := by norm_num

private lemma vlog_ub_m85 : Real.log (85:ℝ) ≤ ((190810977487424618883:ℝ)/42949672960000000000) := by
  have hdec : (85:ℝ) = (2:ℝ)^(6) * (1 + ((21:ℝ)/64)) := by norm_num
  have harg' : 1 + ((21:ℝ)/64) ≠ 0 := by norm_num
  rw [hdec]
  rw [Real.log_mul (by positivity : (2:ℝ)^(6) ≠ 0) harg']
  rw [Real.log_pow]
  have h1 : (6:ℝ) * Real.log 2 ≤ (6:ℝ) * ((108304247:ℝ)/156250000) := by
    have hb : Real.log 2 ≤ ((108304247:ℝ)/156250000) := by
      have h := log_two_lt_d9
      norm_num at h ⊢
      linarith
    exact mul_le_mul_of_nonneg_left hb (by norm_num)
  have h2 : Real.log (1 + ((21:ℝ)/64)) ≤ ((21:ℝ)/64) - ((21:ℝ)/64) ^ 2 / 2 + ((21:ℝ)/64) ^ 3 / 3 - ((21:ℝ)/64) ^ 4 / 4 + ((21:ℝ)/64) ^ 5 / 5 - ((21:ℝ)/64) ^ 6 / 6 + ((21:ℝ)/64) ^ 7 / 7 := log_one_add_le7 ((21:ℝ)/64) (by norm_num)
  calc
    (6:ℝ) * Real.log 2 + Real.log (1 + ((21:ℝ)/64)) ≤ (6:ℝ) * ((108304247:ℝ)/156250000) + ((21:ℝ)/64) - ((21:ℝ)/64) ^ 2 / 2 + ((21:ℝ)/64) ^ 3 / 3 - ((21:ℝ)/64) ^ 4 / 4 + ((21:ℝ)/64) ^ 5 / 5 - ((21:ℝ)/64) ^ 6 / 6 + ((21:ℝ)/64) ^ 7 / 7 := by
      nlinarith
    _ = ((190810977487424618883:ℝ)/42949672960000000000) := by norm_num

private lemma vlog_ub_m349_4 : Real.log ((349:ℝ)/4) ≤ ((22012499854045905145531629:ℝ)/4925812092436480000000000) := by
  have hdec : ((349:ℝ)/4) = (2:ℝ)^(6) * (1 + ((93:ℝ)/256)) := by norm_num
  have harg' : 1 + ((93:ℝ)/256) ≠ 0 := by norm_num
  rw [hdec]
  rw [Real.log_mul (by positivity : (2:ℝ)^(6) ≠ 0) harg']
  rw [Real.log_pow]
  have h1 : (6:ℝ) * Real.log 2 ≤ (6:ℝ) * ((108304247:ℝ)/156250000) := by
    have hb : Real.log 2 ≤ ((108304247:ℝ)/156250000) := by
      have h := log_two_lt_d9
      norm_num at h ⊢
      linarith
    exact mul_le_mul_of_nonneg_left hb (by norm_num)
  have h2 : Real.log (1 + ((93:ℝ)/256)) ≤ ((93:ℝ)/256) - ((93:ℝ)/256) ^ 2 / 2 + ((93:ℝ)/256) ^ 3 / 3 - ((93:ℝ)/256) ^ 4 / 4 + ((93:ℝ)/256) ^ 5 / 5 - ((93:ℝ)/256) ^ 6 / 6 + ((93:ℝ)/256) ^ 7 / 7 := log_one_add_le7 ((93:ℝ)/256) (by norm_num)
  calc
    (6:ℝ) * Real.log 2 + Real.log (1 + ((93:ℝ)/256)) ≤ (6:ℝ) * ((108304247:ℝ)/156250000) + ((93:ℝ)/256) - ((93:ℝ)/256) ^ 2 / 2 + ((93:ℝ)/256) ^ 3 / 3 - ((93:ℝ)/256) ^ 4 / 4 + ((93:ℝ)/256) ^ 5 / 5 - ((93:ℝ)/256) ^ 6 / 6 + ((93:ℝ)/256) ^ 7 / 7 := by
      nlinarith
    _ = ((22012499854045905145531629:ℝ)/4925812092436480000000000) := by norm_num

private lemma vlog_ub_m90 : Real.log (90:ℝ) ≤ ((10569359216246106477:ℝ)/2348810240000000000) := by
  have hdec : (90:ℝ) = (2:ℝ)^(6) * (1 + ((13:ℝ)/32)) := by norm_num
  have harg' : 1 + ((13:ℝ)/32) ≠ 0 := by norm_num
  rw [hdec]
  rw [Real.log_mul (by positivity : (2:ℝ)^(6) ≠ 0) harg']
  rw [Real.log_pow]
  have h1 : (6:ℝ) * Real.log 2 ≤ (6:ℝ) * ((108304247:ℝ)/156250000) := by
    have hb : Real.log 2 ≤ ((108304247:ℝ)/156250000) := by
      have h := log_two_lt_d9
      norm_num at h ⊢
      linarith
    exact mul_le_mul_of_nonneg_left hb (by norm_num)
  have h2 : Real.log (1 + ((13:ℝ)/32)) ≤ ((13:ℝ)/32) - ((13:ℝ)/32) ^ 2 / 2 + ((13:ℝ)/32) ^ 3 / 3 - ((13:ℝ)/32) ^ 4 / 4 + ((13:ℝ)/32) ^ 5 / 5 - ((13:ℝ)/32) ^ 6 / 6 + ((13:ℝ)/32) ^ 7 / 7 := log_one_add_le7 ((13:ℝ)/32) (by norm_num)
  calc
    (6:ℝ) * Real.log 2 + Real.log (1 + ((13:ℝ)/32)) ≤ (6:ℝ) * ((108304247:ℝ)/156250000) + ((13:ℝ)/32) - ((13:ℝ)/32) ^ 2 / 2 + ((13:ℝ)/32) ^ 3 / 3 - ((13:ℝ)/32) ^ 4 / 4 + ((13:ℝ)/32) ^ 5 / 5 - ((13:ℝ)/32) ^ 6 / 6 + ((13:ℝ)/32) ^ 7 / 7 := by
      nlinarith
    _ = ((10569359216246106477:ℝ)/2348810240000000000) := by norm_num

private lemma vlog_ub_m97 : Real.log (97:ℝ) ≤ ((1178896328402616863431:ℝ)/257698037760000000000) := by
  have hdec : (97:ℝ) = (2:ℝ)^(7) * (1 - ((31:ℝ)/128)) := by norm_num
  have harg' : 1 - ((31:ℝ)/128) ≠ 0 := by norm_num
  rw [hdec]
  rw [Real.log_mul (by positivity : (2:ℝ)^(7) ≠ 0) harg']
  rw [Real.log_pow]
  have h1 : (7:ℝ) * Real.log 2 ≤ (7:ℝ) * ((108304247:ℝ)/156250000) := by
    have hb : Real.log 2 ≤ ((108304247:ℝ)/156250000) := by
      have h := log_two_lt_d9
      norm_num at h ⊢
      linarith
    exact mul_le_mul_of_nonneg_left hb (by norm_num)
  have h2 : Real.log (1 - ((31:ℝ)/128)) ≤ -( ((31:ℝ)/128) + ((31:ℝ)/128) ^ 2 / 2 + ((31:ℝ)/128) ^ 3 / 3 + ((31:ℝ)/128) ^ 4 / 4 + ((31:ℝ)/128) ^ 5 / 5 + ((31:ℝ)/128) ^ 6 / 6 ) := log_one_sub_le6 ((31:ℝ)/128) (by norm_num) (by norm_num : ((31:ℝ)/128) ≤ (1:ℝ)/2)
  calc
    (7:ℝ) * Real.log 2 + Real.log (1 - ((31:ℝ)/128)) ≤ (7:ℝ) * ((108304247:ℝ)/156250000) + -( ((31:ℝ)/128) + ((31:ℝ)/128) ^ 2 / 2 + ((31:ℝ)/128) ^ 3 / 3 + ((31:ℝ)/128) ^ 4 / 4 + ((31:ℝ)/128) ^ 5 / 5 + ((31:ℝ)/128) ^ 6 / 6 ) := by
      nlinarith
    _ = ((1178896328402616863431:ℝ)/257698037760000000000) := by norm_num

private lemma vlog_ub_m100 : Real.log (100:ℝ) ≤ ((289732522725891511:ℝ)/62914560000000000) := by
  have hdec : (100:ℝ) = (2:ℝ)^(7) * (1 - ((7:ℝ)/32)) := by norm_num
  have harg' : 1 - ((7:ℝ)/32) ≠ 0 := by norm_num
  rw [hdec]
  rw [Real.log_mul (by positivity : (2:ℝ)^(7) ≠ 0) harg']
  rw [Real.log_pow]
  have h1 : (7:ℝ) * Real.log 2 ≤ (7:ℝ) * ((108304247:ℝ)/156250000) := by
    have hb : Real.log 2 ≤ ((108304247:ℝ)/156250000) := by
      have h := log_two_lt_d9
      norm_num at h ⊢
      linarith
    exact mul_le_mul_of_nonneg_left hb (by norm_num)
  have h2 : Real.log (1 - ((7:ℝ)/32)) ≤ -( ((7:ℝ)/32) + ((7:ℝ)/32) ^ 2 / 2 + ((7:ℝ)/32) ^ 3 / 3 + ((7:ℝ)/32) ^ 4 / 4 + ((7:ℝ)/32) ^ 5 / 5 + ((7:ℝ)/32) ^ 6 / 6 ) := log_one_sub_le6 ((7:ℝ)/32) (by norm_num) (by norm_num : ((7:ℝ)/32) ≤ (1:ℝ)/2)
  calc
    (7:ℝ) * Real.log 2 + Real.log (1 - ((7:ℝ)/32)) ≤ (7:ℝ) * ((108304247:ℝ)/156250000) + -( ((7:ℝ)/32) + ((7:ℝ)/32) ^ 2 / 2 + ((7:ℝ)/32) ^ 3 / 3 + ((7:ℝ)/32) ^ 4 / 4 + ((7:ℝ)/32) ^ 5 / 5 + ((7:ℝ)/32) ^ 6 / 6 ) := by
      nlinarith
    _ = ((289732522725891511:ℝ)/62914560000000000) := by norm_num

private lemma vlog_ub_m117 : Real.log (117:ℝ) ≤ ((409067626760117079477:ℝ)/85899345920000000000) := by
  have hdec : (117:ℝ) = (2:ℝ)^(7) * (1 - ((11:ℝ)/128)) := by norm_num
  have harg' : 1 - ((11:ℝ)/128) ≠ 0 := by norm_num
  rw [hdec]
  rw [Real.log_mul (by positivity : (2:ℝ)^(7) ≠ 0) harg']
  rw [Real.log_pow]
  have h1 : (7:ℝ) * Real.log 2 ≤ (7:ℝ) * ((108304247:ℝ)/156250000) := by
    have hb : Real.log 2 ≤ ((108304247:ℝ)/156250000) := by
      have h := log_two_lt_d9
      norm_num at h ⊢
      linarith
    exact mul_le_mul_of_nonneg_left hb (by norm_num)
  have h2 : Real.log (1 - ((11:ℝ)/128)) ≤ -( ((11:ℝ)/128) + ((11:ℝ)/128) ^ 2 / 2 + ((11:ℝ)/128) ^ 3 / 3 + ((11:ℝ)/128) ^ 4 / 4 + ((11:ℝ)/128) ^ 5 / 5 + ((11:ℝ)/128) ^ 6 / 6 ) := log_one_sub_le6 ((11:ℝ)/128) (by norm_num) (by norm_num : ((11:ℝ)/128) ≤ (1:ℝ)/2)
  calc
    (7:ℝ) * Real.log 2 + Real.log (1 - ((11:ℝ)/128)) ≤ (7:ℝ) * ((108304247:ℝ)/156250000) + -( ((11:ℝ)/128) + ((11:ℝ)/128) ^ 2 / 2 + ((11:ℝ)/128) ^ 3 / 3 + ((11:ℝ)/128) ^ 4 / 4 + ((11:ℝ)/128) ^ 5 / 5 + ((11:ℝ)/128) ^ 6 / 6 ) := by
      nlinarith
    _ = ((409067626760117079477:ℝ)/85899345920000000000) := by norm_num

private lemma vlog_ub_m145 : Real.log (145:ℝ) ≤ ((574557546348049165363963:ℝ)/115448720916480000000000) := by
  have hdec : (145:ℝ) = (2:ℝ)^(7) * (1 + ((17:ℝ)/128)) := by norm_num
  have harg' : 1 + ((17:ℝ)/128) ≠ 0 := by norm_num
  rw [hdec]
  rw [Real.log_mul (by positivity : (2:ℝ)^(7) ≠ 0) harg']
  rw [Real.log_pow]
  have h1 : (7:ℝ) * Real.log 2 ≤ (7:ℝ) * ((108304247:ℝ)/156250000) := by
    have hb : Real.log 2 ≤ ((108304247:ℝ)/156250000) := by
      have h := log_two_lt_d9
      norm_num at h ⊢
      linarith
    exact mul_le_mul_of_nonneg_left hb (by norm_num)
  have h2 : Real.log (1 + ((17:ℝ)/128)) ≤ ((17:ℝ)/128) - ((17:ℝ)/128) ^ 2 / 2 + ((17:ℝ)/128) ^ 3 / 3 - ((17:ℝ)/128) ^ 4 / 4 + ((17:ℝ)/128) ^ 5 / 5 - ((17:ℝ)/128) ^ 6 / 6 + ((17:ℝ)/128) ^ 7 / 7 := log_one_add_le7 ((17:ℝ)/128) (by norm_num)
  calc
    (7:ℝ) * Real.log 2 + Real.log (1 + ((17:ℝ)/128)) ≤ (7:ℝ) * ((108304247:ℝ)/156250000) + ((17:ℝ)/128) - ((17:ℝ)/128) ^ 2 / 2 + ((17:ℝ)/128) ^ 3 / 3 - ((17:ℝ)/128) ^ 4 / 4 + ((17:ℝ)/128) ^ 5 / 5 - ((17:ℝ)/128) ^ 6 / 6 + ((17:ℝ)/128) ^ 7 / 7 := by
      nlinarith
    _ = ((574557546348049165363963:ℝ)/115448720916480000000000) := by norm_num

private lemma vlog_ub_m4261_25 : Real.log ((4261:ℝ)/25) ≤ ((370763382579603115210133863:ℝ)/72155450572800000000000000) := by
  have hdec : ((4261:ℝ)/25) = (2:ℝ)^(7) * (1 + ((1061:ℝ)/3200)) := by norm_num
  have harg' : 1 + ((1061:ℝ)/3200) ≠ 0 := by norm_num
  rw [hdec]
  rw [Real.log_mul (by positivity : (2:ℝ)^(7) ≠ 0) harg']
  rw [Real.log_pow]
  have h1 : (7:ℝ) * Real.log 2 ≤ (7:ℝ) * ((108304247:ℝ)/156250000) := by
    have hb : Real.log 2 ≤ ((108304247:ℝ)/156250000) := by
      have h := log_two_lt_d9
      norm_num at h ⊢
      linarith
    exact mul_le_mul_of_nonneg_left hb (by norm_num)
  have h2 : Real.log (1 + ((1061:ℝ)/3200)) ≤ ((1061:ℝ)/3200) - ((1061:ℝ)/3200) ^ 2 / 2 + ((1061:ℝ)/3200) ^ 3 / 3 - ((1061:ℝ)/3200) ^ 4 / 4 + ((1061:ℝ)/3200) ^ 5 / 5 - ((1061:ℝ)/3200) ^ 6 / 6 + ((1061:ℝ)/3200) ^ 7 / 7 := log_one_add_le7 ((1061:ℝ)/3200) (by norm_num)
  calc
    (7:ℝ) * Real.log 2 + Real.log (1 + ((1061:ℝ)/3200)) ≤ (7:ℝ) * ((108304247:ℝ)/156250000) + ((1061:ℝ)/3200) - ((1061:ℝ)/3200) ^ 2 / 2 + ((1061:ℝ)/3200) ^ 3 / 3 - ((1061:ℝ)/3200) ^ 4 / 4 + ((1061:ℝ)/3200) ^ 5 / 5 - ((1061:ℝ)/3200) ^ 6 / 6 + ((1061:ℝ)/3200) ^ 7 / 7 := by
      nlinarith
    _ = ((370763382579603115210133863:ℝ)/72155450572800000000000000) := by norm_num

private lemma vlog_ub_m685_4 : Real.log ((685:ℝ)/4) ≤ ((9728311779329375603594654167:ℝ)/1891511843495608320000000000) := by
  have hdec : ((685:ℝ)/4) = (2:ℝ)^(7) * (1 + ((173:ℝ)/512)) := by norm_num
  have harg' : 1 + ((173:ℝ)/512) ≠ 0 := by norm_num
  rw [hdec]
  rw [Real.log_mul (by positivity : (2:ℝ)^(7) ≠ 0) harg']
  rw [Real.log_pow]
  have h1 : (7:ℝ) * Real.log 2 ≤ (7:ℝ) * ((108304247:ℝ)/156250000) := by
    have hb : Real.log 2 ≤ ((108304247:ℝ)/156250000) := by
      have h := log_two_lt_d9
      norm_num at h ⊢
      linarith
    exact mul_le_mul_of_nonneg_left hb (by norm_num)
  have h2 : Real.log (1 + ((173:ℝ)/512)) ≤ ((173:ℝ)/512) - ((173:ℝ)/512) ^ 2 / 2 + ((173:ℝ)/512) ^ 3 / 3 - ((173:ℝ)/512) ^ 4 / 4 + ((173:ℝ)/512) ^ 5 / 5 - ((173:ℝ)/512) ^ 6 / 6 + ((173:ℝ)/512) ^ 7 / 7 := log_one_add_le7 ((173:ℝ)/512) (by norm_num)
  calc
    (7:ℝ) * Real.log 2 + Real.log (1 + ((173:ℝ)/512)) ≤ (7:ℝ) * ((108304247:ℝ)/156250000) + ((173:ℝ)/512) - ((173:ℝ)/512) ^ 2 / 2 + ((173:ℝ)/512) ^ 3 / 3 - ((173:ℝ)/512) ^ 4 / 4 + ((173:ℝ)/512) ^ 5 / 5 - ((173:ℝ)/512) ^ 6 / 6 + ((173:ℝ)/512) ^ 7 / 7 := by
      nlinarith
    _ = ((9728311779329375603594654167:ℝ)/1891511843495608320000000000) := by norm_num

private lemma vlog_ub_m173 : Real.log (173:ℝ) ≤ ((198314496989139625433821:ℝ)/38482906972160000000000) := by
  have hdec : (173:ℝ) = (2:ℝ)^(7) * (1 + ((45:ℝ)/128)) := by norm_num
  have harg' : 1 + ((45:ℝ)/128) ≠ 0 := by norm_num
  rw [hdec]
  rw [Real.log_mul (by positivity : (2:ℝ)^(7) ≠ 0) harg']
  rw [Real.log_pow]
  have h1 : (7:ℝ) * Real.log 2 ≤ (7:ℝ) * ((108304247:ℝ)/156250000) := by
    have hb : Real.log 2 ≤ ((108304247:ℝ)/156250000) := by
      have h := log_two_lt_d9
      norm_num at h ⊢
      linarith
    exact mul_le_mul_of_nonneg_left hb (by norm_num)
  have h2 : Real.log (1 + ((45:ℝ)/128)) ≤ ((45:ℝ)/128) - ((45:ℝ)/128) ^ 2 / 2 + ((45:ℝ)/128) ^ 3 / 3 - ((45:ℝ)/128) ^ 4 / 4 + ((45:ℝ)/128) ^ 5 / 5 - ((45:ℝ)/128) ^ 6 / 6 + ((45:ℝ)/128) ^ 7 / 7 := log_one_add_le7 ((45:ℝ)/128) (by norm_num)
  calc
    (7:ℝ) * Real.log 2 + Real.log (1 + ((45:ℝ)/128)) ≤ (7:ℝ) * ((108304247:ℝ)/156250000) + ((45:ℝ)/128) - ((45:ℝ)/128) ^ 2 / 2 + ((45:ℝ)/128) ^ 3 / 3 - ((45:ℝ)/128) ^ 4 / 4 + ((45:ℝ)/128) ^ 5 / 5 - ((45:ℝ)/128) ^ 6 / 6 + ((45:ℝ)/128) ^ 7 / 7 := by
      nlinarith
    _ = ((198314496989139625433821:ℝ)/38482906972160000000000) := by norm_num

private lemma vlog_ub_m701_4 : Real.log ((701:ℝ)/4) ≤ ((465334071459721956196471627:ℝ)/90071992547409920000000000) := by
  have hdec : ((701:ℝ)/4) = (2:ℝ)^(7) * (1 + ((189:ℝ)/512)) := by norm_num
  have harg' : 1 + ((189:ℝ)/512) ≠ 0 := by norm_num
  rw [hdec]
  rw [Real.log_mul (by positivity : (2:ℝ)^(7) ≠ 0) harg']
  rw [Real.log_pow]
  have h1 : (7:ℝ) * Real.log 2 ≤ (7:ℝ) * ((108304247:ℝ)/156250000) := by
    have hb : Real.log 2 ≤ ((108304247:ℝ)/156250000) := by
      have h := log_two_lt_d9
      norm_num at h ⊢
      linarith
    exact mul_le_mul_of_nonneg_left hb (by norm_num)
  have h2 : Real.log (1 + ((189:ℝ)/512)) ≤ ((189:ℝ)/512) - ((189:ℝ)/512) ^ 2 / 2 + ((189:ℝ)/512) ^ 3 / 3 - ((189:ℝ)/512) ^ 4 / 4 + ((189:ℝ)/512) ^ 5 / 5 - ((189:ℝ)/512) ^ 6 / 6 + ((189:ℝ)/512) ^ 7 / 7 := log_one_add_le7 ((189:ℝ)/512) (by norm_num)
  calc
    (7:ℝ) * Real.log 2 + Real.log (1 + ((189:ℝ)/512)) ≤ (7:ℝ) * ((108304247:ℝ)/156250000) + ((189:ℝ)/512) - ((189:ℝ)/512) ^ 2 / 2 + ((189:ℝ)/512) ^ 3 / 3 - ((189:ℝ)/512) ^ 4 / 4 + ((189:ℝ)/512) ^ 5 / 5 - ((189:ℝ)/512) ^ 6 / 6 + ((189:ℝ)/512) ^ 7 / 7 := by
      nlinarith
    _ = ((465334071459721956196471627:ℝ)/90071992547409920000000000) := by norm_num

private lemma vlog_ub_m178 : Real.log (178:ℝ) ≤ ((4673719492407519373571:ℝ)/901943132160000000000) := by
  have hdec : (178:ℝ) = (2:ℝ)^(7) * (1 + ((25:ℝ)/64)) := by norm_num
  have harg' : 1 + ((25:ℝ)/64) ≠ 0 := by norm_num
  rw [hdec]
  rw [Real.log_mul (by positivity : (2:ℝ)^(7) ≠ 0) harg']
  rw [Real.log_pow]
  have h1 : (7:ℝ) * Real.log 2 ≤ (7:ℝ) * ((108304247:ℝ)/156250000) := by
    have hb : Real.log 2 ≤ ((108304247:ℝ)/156250000) := by
      have h := log_two_lt_d9
      norm_num at h ⊢
      linarith
    exact mul_le_mul_of_nonneg_left hb (by norm_num)
  have h2 : Real.log (1 + ((25:ℝ)/64)) ≤ ((25:ℝ)/64) - ((25:ℝ)/64) ^ 2 / 2 + ((25:ℝ)/64) ^ 3 / 3 - ((25:ℝ)/64) ^ 4 / 4 + ((25:ℝ)/64) ^ 5 / 5 - ((25:ℝ)/64) ^ 6 / 6 + ((25:ℝ)/64) ^ 7 / 7 := log_one_add_le7 ((25:ℝ)/64) (by norm_num)
  calc
    (7:ℝ) * Real.log 2 + Real.log (1 + ((25:ℝ)/64)) ≤ (7:ℝ) * ((108304247:ℝ)/156250000) + ((25:ℝ)/64) - ((25:ℝ)/64) ^ 2 / 2 + ((25:ℝ)/64) ^ 3 / 3 - ((25:ℝ)/64) ^ 4 / 4 + ((25:ℝ)/64) ^ 5 / 5 - ((25:ℝ)/64) ^ 6 / 6 + ((25:ℝ)/64) ^ 7 / 7 := by
      nlinarith
    _ = ((4673719492407519373571:ℝ)/901943132160000000000) := by norm_num

private lemma vlog_ub_m185 : Real.log (185:ℝ) ≤ ((200899802490351414496321:ℝ)/38482906972160000000000) := by
  have hdec : (185:ℝ) = (2:ℝ)^(7) * (1 + ((57:ℝ)/128)) := by norm_num
  have harg' : 1 + ((57:ℝ)/128) ≠ 0 := by norm_num
  rw [hdec]
  rw [Real.log_mul (by positivity : (2:ℝ)^(7) ≠ 0) harg']
  rw [Real.log_pow]
  have h1 : (7:ℝ) * Real.log 2 ≤ (7:ℝ) * ((108304247:ℝ)/156250000) := by
    have hb : Real.log 2 ≤ ((108304247:ℝ)/156250000) := by
      have h := log_two_lt_d9
      norm_num at h ⊢
      linarith
    exact mul_le_mul_of_nonneg_left hb (by norm_num)
  have h2 : Real.log (1 + ((57:ℝ)/128)) ≤ ((57:ℝ)/128) - ((57:ℝ)/128) ^ 2 / 2 + ((57:ℝ)/128) ^ 3 / 3 - ((57:ℝ)/128) ^ 4 / 4 + ((57:ℝ)/128) ^ 5 / 5 - ((57:ℝ)/128) ^ 6 / 6 + ((57:ℝ)/128) ^ 7 / 7 := log_one_add_le7 ((57:ℝ)/128) (by norm_num)
  calc
    (7:ℝ) * Real.log 2 + Real.log (1 + ((57:ℝ)/128)) ≤ (7:ℝ) * ((108304247:ℝ)/156250000) + ((57:ℝ)/128) - ((57:ℝ)/128) ^ 2 / 2 + ((57:ℝ)/128) ^ 3 / 3 - ((57:ℝ)/128) ^ 4 / 4 + ((57:ℝ)/128) ^ 5 / 5 - ((57:ℝ)/128) ^ 6 / 6 + ((57:ℝ)/128) ^ 7 / 7 := by
      nlinarith
    _ = ((200899802490351414496321:ℝ)/38482906972160000000000) := by norm_num

private lemma vlog_ub_m205 : Real.log (205:ℝ) ≤ ((29263568698756449409157:ℝ)/5497558138880000000000) := by
  have hdec : (205:ℝ) = (2:ℝ)^(8) * (1 - ((51:ℝ)/256)) := by norm_num
  have harg' : 1 - ((51:ℝ)/256) ≠ 0 := by norm_num
  rw [hdec]
  rw [Real.log_mul (by positivity : (2:ℝ)^(8) ≠ 0) harg']
  rw [Real.log_pow]
  have h1 : (8:ℝ) * Real.log 2 ≤ (8:ℝ) * ((108304247:ℝ)/156250000) := by
    have hb : Real.log 2 ≤ ((108304247:ℝ)/156250000) := by
      have h := log_two_lt_d9
      norm_num at h ⊢
      linarith
    exact mul_le_mul_of_nonneg_left hb (by norm_num)
  have h2 : Real.log (1 - ((51:ℝ)/256)) ≤ -( ((51:ℝ)/256) + ((51:ℝ)/256) ^ 2 / 2 + ((51:ℝ)/256) ^ 3 / 3 + ((51:ℝ)/256) ^ 4 / 4 + ((51:ℝ)/256) ^ 5 / 5 + ((51:ℝ)/256) ^ 6 / 6 ) := log_one_sub_le6 ((51:ℝ)/256) (by norm_num) (by norm_num : ((51:ℝ)/256) ≤ (1:ℝ)/2)
  calc
    (8:ℝ) * Real.log 2 + Real.log (1 - ((51:ℝ)/256)) ≤ (8:ℝ) * ((108304247:ℝ)/156250000) + -( ((51:ℝ)/256) + ((51:ℝ)/256) ^ 2 / 2 + ((51:ℝ)/256) ^ 3 / 3 + ((51:ℝ)/256) ^ 4 / 4 + ((51:ℝ)/256) ^ 5 / 5 + ((51:ℝ)/256) ^ 6 / 6 ) := by
      nlinarith
    _ = ((29263568698756449409157:ℝ)/5497558138880000000000) := by norm_num

private lemma vlog_ub_m5661_25 : Real.log ((5661:ℝ)/25) ≤ ((745259983925583903668173:ℝ)/137438953472000000000000) := by
  have hdec : ((5661:ℝ)/25) = (2:ℝ)^(8) * (1 - ((739:ℝ)/6400)) := by norm_num
  have harg' : 1 - ((739:ℝ)/6400) ≠ 0 := by norm_num
  rw [hdec]
  rw [Real.log_mul (by positivity : (2:ℝ)^(8) ≠ 0) harg']
  rw [Real.log_pow]
  have h1 : (8:ℝ) * Real.log 2 ≤ (8:ℝ) * ((108304247:ℝ)/156250000) := by
    have hb : Real.log 2 ≤ ((108304247:ℝ)/156250000) := by
      have h := log_two_lt_d9
      norm_num at h ⊢
      linarith
    exact mul_le_mul_of_nonneg_left hb (by norm_num)
  have h2 : Real.log (1 - ((739:ℝ)/6400)) ≤ -( ((739:ℝ)/6400) + ((739:ℝ)/6400) ^ 2 / 2 + ((739:ℝ)/6400) ^ 3 / 3 + ((739:ℝ)/6400) ^ 4 / 4 + ((739:ℝ)/6400) ^ 5 / 5 + ((739:ℝ)/6400) ^ 6 / 6 ) := log_one_sub_le6 ((739:ℝ)/6400) (by norm_num) (by norm_num : ((739:ℝ)/6400) ≤ (1:ℝ)/2)
  calc
    (8:ℝ) * Real.log 2 + Real.log (1 - ((739:ℝ)/6400)) ≤ (8:ℝ) * ((108304247:ℝ)/156250000) + -( ((739:ℝ)/6400) + ((739:ℝ)/6400) ^ 2 / 2 + ((739:ℝ)/6400) ^ 3 / 3 + ((739:ℝ)/6400) ^ 4 / 4 + ((739:ℝ)/6400) ^ 5 / 5 + ((739:ℝ)/6400) ^ 6 / 6 ) := by
      nlinarith
    _ = ((745259983925583903668173:ℝ)/137438953472000000000000) := by norm_num

private lemma vlog_ub_m909_4 : Real.log ((909:ℝ)/4) ≤ ((122183801144633946344360197:ℝ)/22517998136852480000000000) := by
  have hdec : ((909:ℝ)/4) = (2:ℝ)^(8) * (1 - ((115:ℝ)/1024)) := by norm_num
  have harg' : 1 - ((115:ℝ)/1024) ≠ 0 := by norm_num
  rw [hdec]
  rw [Real.log_mul (by positivity : (2:ℝ)^(8) ≠ 0) harg']
  rw [Real.log_pow]
  have h1 : (8:ℝ) * Real.log 2 ≤ (8:ℝ) * ((108304247:ℝ)/156250000) := by
    have hb : Real.log 2 ≤ ((108304247:ℝ)/156250000) := by
      have h := log_two_lt_d9
      norm_num at h ⊢
      linarith
    exact mul_le_mul_of_nonneg_left hb (by norm_num)
  have h2 : Real.log (1 - ((115:ℝ)/1024)) ≤ -( ((115:ℝ)/1024) + ((115:ℝ)/1024) ^ 2 / 2 + ((115:ℝ)/1024) ^ 3 / 3 + ((115:ℝ)/1024) ^ 4 / 4 + ((115:ℝ)/1024) ^ 5 / 5 + ((115:ℝ)/1024) ^ 6 / 6 ) := log_one_sub_le6 ((115:ℝ)/1024) (by norm_num) (by norm_num : ((115:ℝ)/1024) ≤ (1:ℝ)/2)
  calc
    (8:ℝ) * Real.log 2 + Real.log (1 - ((115:ℝ)/1024)) ≤ (8:ℝ) * ((108304247:ℝ)/156250000) + -( ((115:ℝ)/1024) + ((115:ℝ)/1024) ^ 2 / 2 + ((115:ℝ)/1024) ^ 3 / 3 + ((115:ℝ)/1024) ^ 4 / 4 + ((115:ℝ)/1024) ^ 5 / 5 + ((115:ℝ)/1024) ^ 6 / 6 ) := by
      nlinarith
    _ = ((122183801144633946344360197:ℝ)/22517998136852480000000000) := by norm_num

private lemma vlog_ub_m229 : Real.log (229:ℝ) ≤ ((29872202761228730659157:ℝ)/5497558138880000000000) := by
  have hdec : (229:ℝ) = (2:ℝ)^(8) * (1 - ((27:ℝ)/256)) := by norm_num
  have harg' : 1 - ((27:ℝ)/256) ≠ 0 := by norm_num
  rw [hdec]
  rw [Real.log_mul (by positivity : (2:ℝ)^(8) ≠ 0) harg']
  rw [Real.log_pow]
  have h1 : (8:ℝ) * Real.log 2 ≤ (8:ℝ) * ((108304247:ℝ)/156250000) := by
    have hb : Real.log 2 ≤ ((108304247:ℝ)/156250000) := by
      have h := log_two_lt_d9
      norm_num at h ⊢
      linarith
    exact mul_le_mul_of_nonneg_left hb (by norm_num)
  have h2 : Real.log (1 - ((27:ℝ)/256)) ≤ -( ((27:ℝ)/256) + ((27:ℝ)/256) ^ 2 / 2 + ((27:ℝ)/256) ^ 3 / 3 + ((27:ℝ)/256) ^ 4 / 4 + ((27:ℝ)/256) ^ 5 / 5 + ((27:ℝ)/256) ^ 6 / 6 ) := log_one_sub_le6 ((27:ℝ)/256) (by norm_num) (by norm_num : ((27:ℝ)/256) ≤ (1:ℝ)/2)
  calc
    (8:ℝ) * Real.log 2 + Real.log (1 - ((27:ℝ)/256)) ≤ (8:ℝ) * ((108304247:ℝ)/156250000) + -( ((27:ℝ)/256) + ((27:ℝ)/256) ^ 2 / 2 + ((27:ℝ)/256) ^ 3 / 3 + ((27:ℝ)/256) ^ 4 / 4 + ((27:ℝ)/256) ^ 5 / 5 + ((27:ℝ)/256) ^ 6 / 6 ) := by
      nlinarith
    _ = ((29872202761228730659157:ℝ)/5497558138880000000000) := by norm_num

private lemma vlog_ub_m925_4 : Real.log ((925:ℝ)/4) ≤ ((122576709136283568781860197:ℝ)/22517998136852480000000000) := by
  have hdec : ((925:ℝ)/4) = (2:ℝ)^(8) * (1 - ((99:ℝ)/1024)) := by norm_num
  have harg' : 1 - ((99:ℝ)/1024) ≠ 0 := by norm_num
  rw [hdec]
  rw [Real.log_mul (by positivity : (2:ℝ)^(8) ≠ 0) harg']
  rw [Real.log_pow]
  have h1 : (8:ℝ) * Real.log 2 ≤ (8:ℝ) * ((108304247:ℝ)/156250000) := by
    have hb : Real.log 2 ≤ ((108304247:ℝ)/156250000) := by
      have h := log_two_lt_d9
      norm_num at h ⊢
      linarith
    exact mul_le_mul_of_nonneg_left hb (by norm_num)
  have h2 : Real.log (1 - ((99:ℝ)/1024)) ≤ -( ((99:ℝ)/1024) + ((99:ℝ)/1024) ^ 2 / 2 + ((99:ℝ)/1024) ^ 3 / 3 + ((99:ℝ)/1024) ^ 4 / 4 + ((99:ℝ)/1024) ^ 5 / 5 + ((99:ℝ)/1024) ^ 6 / 6 ) := log_one_sub_le6 ((99:ℝ)/1024) (by norm_num) (by norm_num : ((99:ℝ)/1024) ≤ (1:ℝ)/2)
  calc
    (8:ℝ) * Real.log 2 + Real.log (1 - ((99:ℝ)/1024)) ≤ (8:ℝ) * ((108304247:ℝ)/156250000) + -( ((99:ℝ)/1024) + ((99:ℝ)/1024) ^ 2 / 2 + ((99:ℝ)/1024) ^ 3 / 3 + ((99:ℝ)/1024) ^ 4 / 4 + ((99:ℝ)/1024) ^ 5 / 5 + ((99:ℝ)/1024) ^ 6 / 6 ) := by
      nlinarith
    _ = ((122576709136283568781860197:ℝ)/22517998136852480000000000) := by norm_num

private lemma vlog_ub_m233 : Real.log (233:ℝ) ≤ ((89902202599758426352471:ℝ)/16492674416640000000000) := by
  have hdec : (233:ℝ) = (2:ℝ)^(8) * (1 - ((23:ℝ)/256)) := by norm_num
  have harg' : 1 - ((23:ℝ)/256) ≠ 0 := by norm_num
  rw [hdec]
  rw [Real.log_mul (by positivity : (2:ℝ)^(8) ≠ 0) harg']
  rw [Real.log_pow]
  have h1 : (8:ℝ) * Real.log 2 ≤ (8:ℝ) * ((108304247:ℝ)/156250000) := by
    have hb : Real.log 2 ≤ ((108304247:ℝ)/156250000) := by
      have h := log_two_lt_d9
      norm_num at h ⊢
      linarith
    exact mul_le_mul_of_nonneg_left hb (by norm_num)
  have h2 : Real.log (1 - ((23:ℝ)/256)) ≤ -( ((23:ℝ)/256) + ((23:ℝ)/256) ^ 2 / 2 + ((23:ℝ)/256) ^ 3 / 3 + ((23:ℝ)/256) ^ 4 / 4 + ((23:ℝ)/256) ^ 5 / 5 + ((23:ℝ)/256) ^ 6 / 6 ) := log_one_sub_le6 ((23:ℝ)/256) (by norm_num) (by norm_num : ((23:ℝ)/256) ≤ (1:ℝ)/2)
  calc
    (8:ℝ) * Real.log 2 + Real.log (1 - ((23:ℝ)/256)) ≤ (8:ℝ) * ((108304247:ℝ)/156250000) + -( ((23:ℝ)/256) + ((23:ℝ)/256) ^ 2 / 2 + ((23:ℝ)/256) ^ 3 / 3 + ((23:ℝ)/256) ^ 4 / 4 + ((23:ℝ)/256) ^ 5 / 5 + ((23:ℝ)/256) ^ 6 / 6 ) := by
      nlinarith
    _ = ((89902202599758426352471:ℝ)/16492674416640000000000) := by norm_num

private lemma vlog_ub_m234 : Real.log (234:ℝ) ≤ ((468608516217129061813:ℝ)/85899345920000000000) := by
  have hdec : (234:ℝ) = (2:ℝ)^(8) * (1 - ((11:ℝ)/128)) := by norm_num
  have harg' : 1 - ((11:ℝ)/128) ≠ 0 := by norm_num
  rw [hdec]
  rw [Real.log_mul (by positivity : (2:ℝ)^(8) ≠ 0) harg']
  rw [Real.log_pow]
  have h1 : (8:ℝ) * Real.log 2 ≤ (8:ℝ) * ((108304247:ℝ)/156250000) := by
    have hb : Real.log 2 ≤ ((108304247:ℝ)/156250000) := by
      have h := log_two_lt_d9
      norm_num at h ⊢
      linarith
    exact mul_le_mul_of_nonneg_left hb (by norm_num)
  have h2 : Real.log (1 - ((11:ℝ)/128)) ≤ -( ((11:ℝ)/128) + ((11:ℝ)/128) ^ 2 / 2 + ((11:ℝ)/128) ^ 3 / 3 + ((11:ℝ)/128) ^ 4 / 4 + ((11:ℝ)/128) ^ 5 / 5 + ((11:ℝ)/128) ^ 6 / 6 ) := log_one_sub_le6 ((11:ℝ)/128) (by norm_num) (by norm_num : ((11:ℝ)/128) ≤ (1:ℝ)/2)
  calc
    (8:ℝ) * Real.log 2 + Real.log (1 - ((11:ℝ)/128)) ≤ (8:ℝ) * ((108304247:ℝ)/156250000) + -( ((11:ℝ)/128) + ((11:ℝ)/128) ^ 2 / 2 + ((11:ℝ)/128) ^ 3 / 3 + ((11:ℝ)/128) ^ 4 / 4 + ((11:ℝ)/128) ^ 5 / 5 + ((11:ℝ)/128) ^ 6 / 6 ) := by
      nlinarith
    _ = ((468608516217129061813:ℝ)/85899345920000000000) := by norm_num

private lemma vlog_ub_m241 : Real.log (241:ℝ) ≤ ((30152990034336277534157:ℝ)/5497558138880000000000) := by
  have hdec : (241:ℝ) = (2:ℝ)^(8) * (1 - ((15:ℝ)/256)) := by norm_num
  have harg' : 1 - ((15:ℝ)/256) ≠ 0 := by norm_num
  rw [hdec]
  rw [Real.log_mul (by positivity : (2:ℝ)^(8) ≠ 0) harg']
  rw [Real.log_pow]
  have h1 : (8:ℝ) * Real.log 2 ≤ (8:ℝ) * ((108304247:ℝ)/156250000) := by
    have hb : Real.log 2 ≤ ((108304247:ℝ)/156250000) := by
      have h := log_two_lt_d9
      norm_num at h ⊢
      linarith
    exact mul_le_mul_of_nonneg_left hb (by norm_num)
  have h2 : Real.log (1 - ((15:ℝ)/256)) ≤ -( ((15:ℝ)/256) + ((15:ℝ)/256) ^ 2 / 2 + ((15:ℝ)/256) ^ 3 / 3 + ((15:ℝ)/256) ^ 4 / 4 + ((15:ℝ)/256) ^ 5 / 5 + ((15:ℝ)/256) ^ 6 / 6 ) := log_one_sub_le6 ((15:ℝ)/256) (by norm_num) (by norm_num : ((15:ℝ)/256) ≤ (1:ℝ)/2)
  calc
    (8:ℝ) * Real.log 2 + Real.log (1 - ((15:ℝ)/256)) ≤ (8:ℝ) * ((108304247:ℝ)/156250000) + -( ((15:ℝ)/256) + ((15:ℝ)/256) ^ 2 / 2 + ((15:ℝ)/256) ^ 3 / 3 + ((15:ℝ)/256) ^ 4 / 4 + ((15:ℝ)/256) ^ 5 / 5 + ((15:ℝ)/256) ^ 6 / 6 ) := by
      nlinarith
    _ = ((30152990034336277534157:ℝ)/5497558138880000000000) := by norm_num

private lemma vlog_ub_m261 : Real.log (261:ℝ) ≤ ((27409781920459417610057797:ℝ)/4925812092436480000000000) := by
  have hdec : (261:ℝ) = (2:ℝ)^(8) * (1 + ((5:ℝ)/256)) := by norm_num
  have harg' : 1 + ((5:ℝ)/256) ≠ 0 := by norm_num
  rw [hdec]
  rw [Real.log_mul (by positivity : (2:ℝ)^(8) ≠ 0) harg']
  rw [Real.log_pow]
  have h1 : (8:ℝ) * Real.log 2 ≤ (8:ℝ) * ((108304247:ℝ)/156250000) := by
    have hb : Real.log 2 ≤ ((108304247:ℝ)/156250000) := by
      have h := log_two_lt_d9
      norm_num at h ⊢
      linarith
    exact mul_le_mul_of_nonneg_left hb (by norm_num)
  have h2 : Real.log (1 + ((5:ℝ)/256)) ≤ ((5:ℝ)/256) - ((5:ℝ)/256) ^ 2 / 2 + ((5:ℝ)/256) ^ 3 / 3 - ((5:ℝ)/256) ^ 4 / 4 + ((5:ℝ)/256) ^ 5 / 5 - ((5:ℝ)/256) ^ 6 / 6 + ((5:ℝ)/256) ^ 7 / 7 := log_one_add_le7 ((5:ℝ)/256) (by norm_num)
  calc
    (8:ℝ) * Real.log 2 + Real.log (1 + ((5:ℝ)/256)) ≤ (8:ℝ) * ((108304247:ℝ)/156250000) + ((5:ℝ)/256) - ((5:ℝ)/256) ^ 2 / 2 + ((5:ℝ)/256) ^ 3 / 3 - ((5:ℝ)/256) ^ 4 / 4 + ((5:ℝ)/256) ^ 5 / 5 - ((5:ℝ)/256) ^ 6 / 6 + ((5:ℝ)/256) ^ 7 / 7 := by
      nlinarith
    _ = ((27409781920459417610057797:ℝ)/4925812092436480000000000) := by norm_num

private lemma vlog_ub_m289 : Real.log (289:ℝ) ≤ ((27911753152792324867870297:ℝ)/4925812092436480000000000) := by
  have hdec : (289:ℝ) = (2:ℝ)^(8) * (1 + ((33:ℝ)/256)) := by norm_num
  have harg' : 1 + ((33:ℝ)/256) ≠ 0 := by norm_num
  rw [hdec]
  rw [Real.log_mul (by positivity : (2:ℝ)^(8) ≠ 0) harg']
  rw [Real.log_pow]
  have h1 : (8:ℝ) * Real.log 2 ≤ (8:ℝ) * ((108304247:ℝ)/156250000) := by
    have hb : Real.log 2 ≤ ((108304247:ℝ)/156250000) := by
      have h := log_two_lt_d9
      norm_num at h ⊢
      linarith
    exact mul_le_mul_of_nonneg_left hb (by norm_num)
  have h2 : Real.log (1 + ((33:ℝ)/256)) ≤ ((33:ℝ)/256) - ((33:ℝ)/256) ^ 2 / 2 + ((33:ℝ)/256) ^ 3 / 3 - ((33:ℝ)/256) ^ 4 / 4 + ((33:ℝ)/256) ^ 5 / 5 - ((33:ℝ)/256) ^ 6 / 6 + ((33:ℝ)/256) ^ 7 / 7 := log_one_add_le7 ((33:ℝ)/256) (by norm_num)
  calc
    (8:ℝ) * Real.log 2 + Real.log (1 + ((33:ℝ)/256)) ≤ (8:ℝ) * ((108304247:ℝ)/156250000) + ((33:ℝ)/256) - ((33:ℝ)/256) ^ 2 / 2 + ((33:ℝ)/256) ^ 3 / 3 - ((33:ℝ)/256) ^ 4 / 4 + ((33:ℝ)/256) ^ 5 / 5 - ((33:ℝ)/256) ^ 6 / 6 + ((33:ℝ)/256) ^ 7 / 7 := by
      nlinarith
    _ = ((27911753152792324867870297:ℝ)/4925812092436480000000000) := by norm_num

private lemma box_0_0 (x t : ℝ) (hx1 : 1 ≤ x) (hx2 : x ≤ 8) (ht : 1 ≤ t)
    (hxl : (1:ℝ) ≤ x) (hxu : x ≤ ((6:ℝ)/5)) (htl : (1:ℝ) ≤ t) (htu : t ≤ ((3:ℝ)/2)) :
    Real.log (Real.sqrt (x ^ 2 + t ^ 2)) +
        (Real.arctan (t / x)) ^ 2 / (2 * Real.log (Real.sqrt (x ^ 2 + t ^ 2))) +
        (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) ≤
      Real.log (2 + t) + (3 : ℝ) / 2 := by
  have hxpos : 0 < x := by linarith
  have htpos : 0 < t := by linarith
  have hapos : 0 < x ^ 2 + t ^ 2 := by positivity
  -- upper square bound
  have hx2le : x ^ 2 ≤ (((6:ℝ)/5)) ^ 2 := sq_le_of_nonneg (le_of_lt hxpos) hxu
  have ht2le : t ^ 2 ≤ (((3:ℝ)/2)) ^ 2 := sq_le_of_nonneg (le_of_lt htpos) htu
  have ha_le : x ^ 2 + t ^ 2 ≤ ((369:ℝ)/100) := by
    have : (((6:ℝ)/5)) ^ 2 + (((3:ℝ)/2)) ^ 2 = ((369:ℝ)/100) := by norm_num
    nlinarith
  have hlogU : Real.log (x ^ 2 + t ^ 2) ≤ ((10695691969381813:ℝ)/8192000000000000) := by
    exact (Real.log_le_log hapos ha_le).trans vlog_ub_m369_100
  -- log(2+t) lower bound
  have hDmono : Real.log ((3:ℝ)) ≤ Real.log (2 + t) := by
    apply Real.log_le_log (by norm_num : 0 < (3:ℝ))
    linarith
  have hDL : ((153784745867:ℝ)/140000000000) ≤ Real.log (2 + t) := (vlog_lb_m3).trans hDmono
  -- lower square bound
  have hx2ge : ((1:ℝ)) ^ 2 ≤ x ^ 2 := sq_le_of_nonneg (by norm_num : 0 ≤ (1:ℝ)) hxl
  have ht2ge : ((1:ℝ)) ^ 2 ≤ t ^ 2 := sq_le_of_nonneg (by norm_num : 0 ≤ (1:ℝ)) htl
  have hQ3le : (2:ℝ) ≤ x ^ 2 + t ^ 2 := by
    have : ((1:ℝ)) ^ 2 + ((1:ℝ)) ^ 2 = (2:ℝ) := by norm_num
    nlinarith
  have hlogL : ((6931471803:ℝ)/10000000000) ≤ Real.log (x ^ 2 + t ^ 2) := by
    exact (vlog_lb_m2).trans (Real.log_le_log (by norm_num : 0 < (2:ℝ)) hQ3le)
  have hLDpos : 0 < ((6931471803:ℝ)/10000000000) := by norm_num
  -- arctan bound
  have htovx : t / x ≤ ((3:ℝ)/2) := by
    rw [div_le_iff₀ hxpos]
    have htu_le : ((3:ℝ)/2) ≤ ((3:ℝ)/2) * x := by
      calc
        ((3:ℝ)/2) = ((3:ℝ)/2) * (1:ℝ) := by norm_num
        _ ≤ ((3:ℝ)/2) * x := mul_le_mul_of_nonneg_left hxl (by norm_num : 0 ≤ ((3:ℝ)/2))
    nlinarith [htu_le]
  have hAT : Real.arctan (t / x) ≤ ((37695443:ℝ)/38272500) := (arctan_mono htovx).trans vatan_ub_m3_2
  have hθsq : (Real.arctan (t / x)) ^ 2 ≤ (((37695443:ℝ)/38272500)) ^ 2 := by
    have hθn : 0 ≤ Real.arctan (t / x) := Real.arctan_nonneg.mpr (div_nonneg (le_of_lt htpos) (le_of_lt hxpos))
    have hAn : 0 ≤ ((37695443:ℝ)/38272500) := by norm_num
    rw [sq_le_sq]
    rw [abs_of_nonneg hθn, abs_of_nonneg hAn]
    exact hAT
  have hQden : (Real.arctan (t / x)) ^ 2 / Real.log (x ^ 2 + t ^ 2) ≤
      (((37695443:ℝ)/38272500)) ^ 2 / (((6931471803:ℝ)/10000000000)) := by
    have h1 : (Real.arctan (t / x)) ^ 2 / Real.log (x ^ 2 + t ^ 2) ≤
        (Real.arctan (t / x)) ^ 2 / ((6931471803:ℝ)/10000000000) := by
      exact div_le_div_of_nonneg_left (sq_nonneg _) hLDpos (by linarith : ((6931471803:ℝ)/10000000000) ≤ Real.log (x ^ 2 + t ^ 2))
    have h2 : (Real.arctan (t / x)) ^ 2 / ((6931471803:ℝ)/10000000000) ≤ (((37695443:ℝ)/38272500)) ^ 2 / ((6931471803:ℝ)/10000000000) := by
      exact div_le_div_of_nonneg_right hθsq (le_of_lt hLDpos)
    exact h1.trans h2
  -- P bound
  have hP : (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) ≤ ((176777:ℝ)/500000) := by
    have hsqrt : Real.sqrt (2:ℝ) ≤ Real.sqrt (x ^ 2 + t ^ 2) := Real.sqrt_le_sqrt hQ3le
    have hd1 : (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) ≤ (1 : ℝ) / (2 * Real.sqrt (2:ℝ)) := by
      have hdenpos : 0 < 2 * Real.sqrt (2:ℝ) := by positivity
      exact div_le_div_of_nonneg_left (by norm_num : 0 ≤ (1 : ℝ)) hdenpos (by nlinarith)
    exact hd1.trans (inv_two_sqrt_le (2:ℝ) (by norm_num) ((176777:ℝ)/500000) (by norm_num) (by norm_num))
  -- S bound
  have hS : Real.log (x ^ 2 + t ^ 2) / 2 - Real.log (2 + t) ≤ (1 / 2) * ((10695691969381813:ℝ)/8192000000000000) - ((153784745867:ℝ)/140000000000) := by
    nlinarith [hlogU, hDL]
  exact combine x t hxpos htpos ((10695691969381813:ℝ)/8192000000000000) ((153784745867:ℝ)/140000000000) ((6931471803:ℝ)/10000000000) ((37695443:ℝ)/38272500) ((176777:ℝ)/500000) hLDpos hS hQden hP (by norm_num)

private lemma box_0_1 (x t : ℝ) (hx1 : 1 ≤ x) (hx2 : x ≤ 8) (ht : 1 ≤ t)
    (hxl : (1:ℝ) ≤ x) (hxu : x ≤ ((6:ℝ)/5)) (htl : ((3:ℝ)/2) ≤ t) (htu : t ≤ (2:ℝ)) :
    Real.log (Real.sqrt (x ^ 2 + t ^ 2)) +
        (Real.arctan (t / x)) ^ 2 / (2 * Real.log (Real.sqrt (x ^ 2 + t ^ 2))) +
        (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) ≤
      Real.log (2 + t) + (3 : ℝ) / 2 := by
  have hxpos : 0 < x := by linarith
  have htpos : 0 < t := by linarith
  have hapos : 0 < x ^ 2 + t ^ 2 := by positivity
  -- upper square bound
  have hx2le : x ^ 2 ≤ (((6:ℝ)/5)) ^ 2 := sq_le_of_nonneg (le_of_lt hxpos) hxu
  have ht2le : t ^ 2 ≤ ((2:ℝ)) ^ 2 := sq_le_of_nonneg (le_of_lt htpos) htu
  have ha_le : x ^ 2 + t ^ 2 ≤ ((136:ℝ)/25) := by
    have : (((6:ℝ)/5)) ^ 2 + ((2:ℝ)) ^ 2 = ((136:ℝ)/25) := by norm_num
    nlinarith
  have hlogU : Real.log (x ^ 2 + t ^ 2) ≤ ((578937528227:ℝ)/341796875000) := by
    exact (Real.log_le_log hapos ha_le).trans vlog_ub_m136_25
  -- log(2+t) lower bound
  have hDmono : Real.log (((7:ℝ)/2)) ≤ Real.log (2 + t) := by
    apply Real.log_le_log (by norm_num : 0 < ((7:ℝ)/2))
    linarith
  have hDL : ((269394135787799:ℝ)/215040000000000) ≤ Real.log (2 + t) := (vlog_lb_m7_2).trans hDmono
  -- lower square bound
  have hx2ge : ((1:ℝ)) ^ 2 ≤ x ^ 2 := sq_le_of_nonneg (by norm_num : 0 ≤ (1:ℝ)) hxl
  have ht2ge : (((3:ℝ)/2)) ^ 2 ≤ t ^ 2 := sq_le_of_nonneg (by norm_num : 0 ≤ ((3:ℝ)/2)) htl
  have hQ3le : ((13:ℝ)/4) ≤ x ^ 2 + t ^ 2 := by
    have : ((1:ℝ)) ^ 2 + (((3:ℝ)/2)) ^ 2 = ((13:ℝ)/4) := by norm_num
    nlinarith
  have hlogL : ((10814198157545049:ℝ)/9175040000000000) ≤ Real.log (x ^ 2 + t ^ 2) := by
    exact (vlog_lb_m13_4).trans (Real.log_le_log (by norm_num : 0 < ((13:ℝ)/4)) hQ3le)
  have hLDpos : 0 < ((10814198157545049:ℝ)/9175040000000000) := by norm_num
  -- arctan bound
  have htovx : t / x ≤ (2:ℝ) := by
    rw [div_le_iff₀ hxpos]
    have htu_le : (2:ℝ) ≤ (2:ℝ) * x := by
      calc
        (2:ℝ) = (2:ℝ) * (1:ℝ) := by norm_num
        _ ≤ (2:ℝ) * x := mul_le_mul_of_nonneg_left hxl (by norm_num : 0 ≤ (2:ℝ))
    nlinarith [htu_le]
  have hAT : Real.arctan (t / x) ≤ ((1860319:ℝ)/1680000) := (arctan_mono htovx).trans vatan_ub_m2
  have hθsq : (Real.arctan (t / x)) ^ 2 ≤ (((1860319:ℝ)/1680000)) ^ 2 := by
    have hθn : 0 ≤ Real.arctan (t / x) := Real.arctan_nonneg.mpr (div_nonneg (le_of_lt htpos) (le_of_lt hxpos))
    have hAn : 0 ≤ ((1860319:ℝ)/1680000) := by norm_num
    rw [sq_le_sq]
    rw [abs_of_nonneg hθn, abs_of_nonneg hAn]
    exact hAT
  have hQden : (Real.arctan (t / x)) ^ 2 / Real.log (x ^ 2 + t ^ 2) ≤
      (((1860319:ℝ)/1680000)) ^ 2 / (((10814198157545049:ℝ)/9175040000000000)) := by
    have h1 : (Real.arctan (t / x)) ^ 2 / Real.log (x ^ 2 + t ^ 2) ≤
        (Real.arctan (t / x)) ^ 2 / ((10814198157545049:ℝ)/9175040000000000) := by
      exact div_le_div_of_nonneg_left (sq_nonneg _) hLDpos (by linarith : ((10814198157545049:ℝ)/9175040000000000) ≤ Real.log (x ^ 2 + t ^ 2))
    have h2 : (Real.arctan (t / x)) ^ 2 / ((10814198157545049:ℝ)/9175040000000000) ≤ (((1860319:ℝ)/1680000)) ^ 2 / ((10814198157545049:ℝ)/9175040000000000) := by
      exact div_le_div_of_nonneg_right hθsq (le_of_lt hLDpos)
    exact h1.trans h2
  -- P bound
  have hP : (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) ≤ ((277351:ℝ)/1000000) := by
    have hsqrt : Real.sqrt ((13:ℝ)/4) ≤ Real.sqrt (x ^ 2 + t ^ 2) := Real.sqrt_le_sqrt hQ3le
    have hd1 : (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) ≤ (1 : ℝ) / (2 * Real.sqrt ((13:ℝ)/4)) := by
      have hdenpos : 0 < 2 * Real.sqrt ((13:ℝ)/4) := by positivity
      exact div_le_div_of_nonneg_left (by norm_num : 0 ≤ (1 : ℝ)) hdenpos (by nlinarith)
    exact hd1.trans (inv_two_sqrt_le ((13:ℝ)/4) (by norm_num) ((277351:ℝ)/1000000) (by norm_num) (by norm_num))
  -- S bound
  have hS : Real.log (x ^ 2 + t ^ 2) / 2 - Real.log (2 + t) ≤ (1 / 2) * ((578937528227:ℝ)/341796875000) - ((269394135787799:ℝ)/215040000000000) := by
    nlinarith [hlogU, hDL]
  exact combine x t hxpos htpos ((578937528227:ℝ)/341796875000) ((269394135787799:ℝ)/215040000000000) ((10814198157545049:ℝ)/9175040000000000) ((1860319:ℝ)/1680000) ((277351:ℝ)/1000000) hLDpos hS hQden hP (by norm_num)

private lemma box_0_2 (x t : ℝ) (hx1 : 1 ≤ x) (hx2 : x ≤ 8) (ht : 1 ≤ t)
    (hxl : (1:ℝ) ≤ x) (hxu : x ≤ ((6:ℝ)/5)) (htl : (2:ℝ) ≤ t) (htu : t ≤ (3:ℝ)) :
    Real.log (Real.sqrt (x ^ 2 + t ^ 2)) +
        (Real.arctan (t / x)) ^ 2 / (2 * Real.log (Real.sqrt (x ^ 2 + t ^ 2))) +
        (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) ≤
      Real.log (2 + t) + (3 : ℝ) / 2 := by
  have hxpos : 0 < x := by linarith
  have htpos : 0 < t := by linarith
  have hapos : 0 < x ^ 2 + t ^ 2 := by positivity
  -- upper square bound
  have hx2le : x ^ 2 ≤ (((6:ℝ)/5)) ^ 2 := sq_le_of_nonneg (le_of_lt hxpos) hxu
  have ht2le : t ^ 2 ≤ ((3:ℝ)) ^ 2 := sq_le_of_nonneg (le_of_lt htpos) htu
  have ha_le : x ^ 2 + t ^ 2 ≤ ((261:ℝ)/25) := by
    have : (((6:ℝ)/5)) ^ 2 + ((3:ℝ)) ^ 2 = ((261:ℝ)/25) := by norm_num
    nlinarith
  have hlogU : Real.log (x ^ 2 + t ^ 2) ≤ ((210170414873381121:ℝ)/89600000000000000) := by
    exact (Real.log_le_log hapos ha_le).trans vlog_ub_m261_25
  -- log(2+t) lower bound
  have hDmono : Real.log ((4:ℝ)) ≤ Real.log (2 + t) := by
    apply Real.log_le_log (by norm_num : 0 < (4:ℝ))
    linarith
  have hDL : ((6931471803:ℝ)/5000000000) ≤ Real.log (2 + t) := (vlog_lb_m4).trans hDmono
  -- lower square bound
  have hx2ge : ((1:ℝ)) ^ 2 ≤ x ^ 2 := sq_le_of_nonneg (by norm_num : 0 ≤ (1:ℝ)) hxl
  have ht2ge : ((2:ℝ)) ^ 2 ≤ t ^ 2 := sq_le_of_nonneg (by norm_num : 0 ≤ (2:ℝ)) htl
  have hQ3le : (5:ℝ) ≤ x ^ 2 + t ^ 2 := by
    have : ((1:ℝ)) ^ 2 + ((2:ℝ)) ^ 2 = (5:ℝ) := by norm_num
    nlinarith
  have hlogL : ((173046727073587:ℝ)/107520000000000) ≤ Real.log (x ^ 2 + t ^ 2) := by
    exact (vlog_lb_m5).trans (Real.log_le_log (by norm_num : 0 < (5:ℝ)) hQ3le)
  have hLDpos : 0 < ((173046727073587:ℝ)/107520000000000) := by norm_num
  -- arctan bound
  have htovx : t / x ≤ (3:ℝ) := by
    rw [div_le_iff₀ hxpos]
    have htu_le : (3:ℝ) ≤ (3:ℝ) * x := by
      calc
        (3:ℝ) = (3:ℝ) * (1:ℝ) := by norm_num
        _ ≤ (3:ℝ) * x := mul_le_mul_of_nonneg_left hxl (by norm_num : 0 ≤ (3:ℝ))
    nlinarith [htu_le]
  have hAT : Real.arctan (t / x) ≤ ((47804443:ℝ)/38272500) := (arctan_mono htovx).trans vatan_ub_m3
  have hθsq : (Real.arctan (t / x)) ^ 2 ≤ (((47804443:ℝ)/38272500)) ^ 2 := by
    have hθn : 0 ≤ Real.arctan (t / x) := Real.arctan_nonneg.mpr (div_nonneg (le_of_lt htpos) (le_of_lt hxpos))
    have hAn : 0 ≤ ((47804443:ℝ)/38272500) := by norm_num
    rw [sq_le_sq]
    rw [abs_of_nonneg hθn, abs_of_nonneg hAn]
    exact hAT
  have hQden : (Real.arctan (t / x)) ^ 2 / Real.log (x ^ 2 + t ^ 2) ≤
      (((47804443:ℝ)/38272500)) ^ 2 / (((173046727073587:ℝ)/107520000000000)) := by
    have h1 : (Real.arctan (t / x)) ^ 2 / Real.log (x ^ 2 + t ^ 2) ≤
        (Real.arctan (t / x)) ^ 2 / ((173046727073587:ℝ)/107520000000000) := by
      exact div_le_div_of_nonneg_left (sq_nonneg _) hLDpos (by linarith : ((173046727073587:ℝ)/107520000000000) ≤ Real.log (x ^ 2 + t ^ 2))
    have h2 : (Real.arctan (t / x)) ^ 2 / ((173046727073587:ℝ)/107520000000000) ≤ (((47804443:ℝ)/38272500)) ^ 2 / ((173046727073587:ℝ)/107520000000000) := by
      exact div_le_div_of_nonneg_right hθsq (le_of_lt hLDpos)
    exact h1.trans h2
  -- P bound
  have hP : (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) ≤ ((223607:ℝ)/1000000) := by
    have hsqrt : Real.sqrt (5:ℝ) ≤ Real.sqrt (x ^ 2 + t ^ 2) := Real.sqrt_le_sqrt hQ3le
    have hd1 : (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) ≤ (1 : ℝ) / (2 * Real.sqrt (5:ℝ)) := by
      have hdenpos : 0 < 2 * Real.sqrt (5:ℝ) := by positivity
      exact div_le_div_of_nonneg_left (by norm_num : 0 ≤ (1 : ℝ)) hdenpos (by nlinarith)
    exact hd1.trans (inv_two_sqrt_le (5:ℝ) (by norm_num) ((223607:ℝ)/1000000) (by norm_num) (by norm_num))
  -- S bound
  have hS : Real.log (x ^ 2 + t ^ 2) / 2 - Real.log (2 + t) ≤ (1 / 2) * ((210170414873381121:ℝ)/89600000000000000) - ((6931471803:ℝ)/5000000000) := by
    nlinarith [hlogU, hDL]
  exact combine x t hxpos htpos ((210170414873381121:ℝ)/89600000000000000) ((6931471803:ℝ)/5000000000) ((173046727073587:ℝ)/107520000000000) ((47804443:ℝ)/38272500) ((223607:ℝ)/1000000) hLDpos hS hQden hP (by norm_num)

private lemma box_0_3 (x t : ℝ) (hx1 : 1 ≤ x) (hx2 : x ≤ 8) (ht : 1 ≤ t)
    (hxl : (1:ℝ) ≤ x) (hxu : x ≤ ((6:ℝ)/5)) (htl : (3:ℝ) ≤ t) (htu : t ≤ (4:ℝ)) :
    Real.log (Real.sqrt (x ^ 2 + t ^ 2)) +
        (Real.arctan (t / x)) ^ 2 / (2 * Real.log (Real.sqrt (x ^ 2 + t ^ 2))) +
        (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) ≤
      Real.log (2 + t) + (3 : ℝ) / 2 := by
  have hxpos : 0 < x := by linarith
  have htpos : 0 < t := by linarith
  have hapos : 0 < x ^ 2 + t ^ 2 := by positivity
  -- upper square bound
  have hx2le : x ^ 2 ≤ (((6:ℝ)/5)) ^ 2 := sq_le_of_nonneg (le_of_lt hxpos) hxu
  have ht2le : t ^ 2 ≤ ((4:ℝ)) ^ 2 := sq_le_of_nonneg (le_of_lt htpos) htu
  have ha_le : x ^ 2 + t ^ 2 ≤ ((436:ℝ)/25) := by
    have : (((6:ℝ)/5)) ^ 2 + ((4:ℝ)) ^ 2 = ((436:ℝ)/25) := by norm_num
    nlinarith
  have hlogU : Real.log (x ^ 2 + t ^ 2) ≤ ((2001136493957519:ℝ)/700000000000000) := by
    exact (Real.log_le_log hapos ha_le).trans vlog_ub_m436_25
  -- log(2+t) lower bound
  have hDmono : Real.log ((5:ℝ)) ≤ Real.log (2 + t) := by
    apply Real.log_le_log (by norm_num : 0 < (5:ℝ))
    linarith
  have hDL : ((173046727073587:ℝ)/107520000000000) ≤ Real.log (2 + t) := (vlog_lb_m5).trans hDmono
  -- lower square bound
  have hx2ge : ((1:ℝ)) ^ 2 ≤ x ^ 2 := sq_le_of_nonneg (by norm_num : 0 ≤ (1:ℝ)) hxl
  have ht2ge : ((3:ℝ)) ^ 2 ≤ t ^ 2 := sq_le_of_nonneg (by norm_num : 0 ≤ (3:ℝ)) htl
  have hQ3le : (10:ℝ) ≤ x ^ 2 + t ^ 2 := by
    have : ((1:ℝ)) ^ 2 + ((3:ℝ)) ^ 2 = (10:ℝ) := by norm_num
    nlinarith
  have hlogL : ((247573911899443:ℝ)/107520000000000) ≤ Real.log (x ^ 2 + t ^ 2) := by
    exact (vlog_lb_m10).trans (Real.log_le_log (by norm_num : 0 < (10:ℝ)) hQ3le)
  have hLDpos : 0 < ((247573911899443:ℝ)/107520000000000) := by norm_num
  -- arctan bound
  have htovx : t / x ≤ (4:ℝ) := by
    rw [div_le_iff₀ hxpos]
    have htu_le : (4:ℝ) ≤ (4:ℝ) * x := by
      calc
        (4:ℝ) = (4:ℝ) * (1:ℝ) := by norm_num
        _ ≤ (4:ℝ) * x := mul_le_mul_of_nonneg_left hxl (by norm_num : 0 ≤ (4:ℝ))
    nlinarith [htu_le]
  have hAT : Real.arctan (t / x) ≤ ((285104707:ℝ)/215040000) := (arctan_mono htovx).trans vatan_ub_m4
  have hθsq : (Real.arctan (t / x)) ^ 2 ≤ (((285104707:ℝ)/215040000)) ^ 2 := by
    have hθn : 0 ≤ Real.arctan (t / x) := Real.arctan_nonneg.mpr (div_nonneg (le_of_lt htpos) (le_of_lt hxpos))
    have hAn : 0 ≤ ((285104707:ℝ)/215040000) := by norm_num
    rw [sq_le_sq]
    rw [abs_of_nonneg hθn, abs_of_nonneg hAn]
    exact hAT
  have hQden : (Real.arctan (t / x)) ^ 2 / Real.log (x ^ 2 + t ^ 2) ≤
      (((285104707:ℝ)/215040000)) ^ 2 / (((247573911899443:ℝ)/107520000000000)) := by
    have h1 : (Real.arctan (t / x)) ^ 2 / Real.log (x ^ 2 + t ^ 2) ≤
        (Real.arctan (t / x)) ^ 2 / ((247573911899443:ℝ)/107520000000000) := by
      exact div_le_div_of_nonneg_left (sq_nonneg _) hLDpos (by linarith : ((247573911899443:ℝ)/107520000000000) ≤ Real.log (x ^ 2 + t ^ 2))
    have h2 : (Real.arctan (t / x)) ^ 2 / ((247573911899443:ℝ)/107520000000000) ≤ (((285104707:ℝ)/215040000)) ^ 2 / ((247573911899443:ℝ)/107520000000000) := by
      exact div_le_div_of_nonneg_right hθsq (le_of_lt hLDpos)
    exact h1.trans h2
  -- P bound
  have hP : (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) ≤ ((79057:ℝ)/500000) := by
    have hsqrt : Real.sqrt (10:ℝ) ≤ Real.sqrt (x ^ 2 + t ^ 2) := Real.sqrt_le_sqrt hQ3le
    have hd1 : (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) ≤ (1 : ℝ) / (2 * Real.sqrt (10:ℝ)) := by
      have hdenpos : 0 < 2 * Real.sqrt (10:ℝ) := by positivity
      exact div_le_div_of_nonneg_left (by norm_num : 0 ≤ (1 : ℝ)) hdenpos (by nlinarith)
    exact hd1.trans (inv_two_sqrt_le (10:ℝ) (by norm_num) ((79057:ℝ)/500000) (by norm_num) (by norm_num))
  -- S bound
  have hS : Real.log (x ^ 2 + t ^ 2) / 2 - Real.log (2 + t) ≤ (1 / 2) * ((2001136493957519:ℝ)/700000000000000) - ((173046727073587:ℝ)/107520000000000) := by
    nlinarith [hlogU, hDL]
  exact combine x t hxpos htpos ((2001136493957519:ℝ)/700000000000000) ((173046727073587:ℝ)/107520000000000) ((247573911899443:ℝ)/107520000000000) ((285104707:ℝ)/215040000) ((79057:ℝ)/500000) hLDpos hS hQden hP (by norm_num)

private lemma box_0_4 (x t : ℝ) (hx1 : 1 ≤ x) (hx2 : x ≤ 8) (ht : 1 ≤ t)
    (hxl : (1:ℝ) ≤ x) (hxu : x ≤ ((6:ℝ)/5)) (htl : (4:ℝ) ≤ t) (htu : t ≤ (6:ℝ)) :
    Real.log (Real.sqrt (x ^ 2 + t ^ 2)) +
        (Real.arctan (t / x)) ^ 2 / (2 * Real.log (Real.sqrt (x ^ 2 + t ^ 2))) +
        (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) ≤
      Real.log (2 + t) + (3 : ℝ) / 2 := by
  have hxpos : 0 < x := by linarith
  have htpos : 0 < t := by linarith
  have hapos : 0 < x ^ 2 + t ^ 2 := by positivity
  -- upper square bound
  have hx2le : x ^ 2 ≤ (((6:ℝ)/5)) ^ 2 := sq_le_of_nonneg (le_of_lt hxpos) hxu
  have ht2le : t ^ 2 ≤ ((6:ℝ)) ^ 2 := sq_le_of_nonneg (le_of_lt htpos) htu
  have ha_le : x ^ 2 + t ^ 2 ≤ ((936:ℝ)/25) := by
    have : (((6:ℝ)/5)) ^ 2 + ((6:ℝ)) ^ 2 = ((936:ℝ)/25) := by norm_num
    nlinarith
  have hlogU : Real.log (x ^ 2 + t ^ 2) ≤ ((2535917810003623:ℝ)/700000000000000) := by
    exact (Real.log_le_log hapos ha_le).trans vlog_ub_m936_25
  -- log(2+t) lower bound
  have hDmono : Real.log ((6:ℝ)) ≤ Real.log (2 + t) := by
    apply Real.log_le_log (by norm_num : 0 < (6:ℝ))
    linarith
  have hDL : ((250825351109:ℝ)/140000000000) ≤ Real.log (2 + t) := (vlog_lb_m6).trans hDmono
  -- lower square bound
  have hx2ge : ((1:ℝ)) ^ 2 ≤ x ^ 2 := sq_le_of_nonneg (by norm_num : 0 ≤ (1:ℝ)) hxl
  have ht2ge : ((4:ℝ)) ^ 2 ≤ t ^ 2 := sq_le_of_nonneg (by norm_num : 0 ≤ (4:ℝ)) htl
  have hQ3le : (17:ℝ) ≤ x ^ 2 + t ^ 2 := by
    have : ((1:ℝ)) ^ 2 + ((4:ℝ)) ^ 2 = (17:ℝ) := by norm_num
    nlinarith
  have hlogL : ((19964041536534117139:ℝ)/7046430720000000000) ≤ Real.log (x ^ 2 + t ^ 2) := by
    exact (vlog_lb_m17).trans (Real.log_le_log (by norm_num : 0 < (17:ℝ)) hQ3le)
  have hLDpos : 0 < ((19964041536534117139:ℝ)/7046430720000000000) := by norm_num
  -- arctan bound
  have htovx : t / x ≤ (6:ℝ) := by
    rw [div_le_iff₀ hxpos]
    have htu_le : (6:ℝ) ≤ (6:ℝ) * x := by
      calc
        (6:ℝ) = (6:ℝ) * (1:ℝ) := by norm_num
        _ ≤ (6:ℝ) * x := mul_le_mul_of_nonneg_left hxl (by norm_num : 0 ≤ (6:ℝ))
    nlinarith [htu_le]
  have hAT : Real.arctan (t / x) ≤ ((1721529301:ℝ)/1224720000) := (arctan_mono htovx).trans vatan_ub_m6
  have hθsq : (Real.arctan (t / x)) ^ 2 ≤ (((1721529301:ℝ)/1224720000)) ^ 2 := by
    have hθn : 0 ≤ Real.arctan (t / x) := Real.arctan_nonneg.mpr (div_nonneg (le_of_lt htpos) (le_of_lt hxpos))
    have hAn : 0 ≤ ((1721529301:ℝ)/1224720000) := by norm_num
    rw [sq_le_sq]
    rw [abs_of_nonneg hθn, abs_of_nonneg hAn]
    exact hAT
  have hQden : (Real.arctan (t / x)) ^ 2 / Real.log (x ^ 2 + t ^ 2) ≤
      (((1721529301:ℝ)/1224720000)) ^ 2 / (((19964041536534117139:ℝ)/7046430720000000000)) := by
    have h1 : (Real.arctan (t / x)) ^ 2 / Real.log (x ^ 2 + t ^ 2) ≤
        (Real.arctan (t / x)) ^ 2 / ((19964041536534117139:ℝ)/7046430720000000000) := by
      exact div_le_div_of_nonneg_left (sq_nonneg _) hLDpos (by linarith : ((19964041536534117139:ℝ)/7046430720000000000) ≤ Real.log (x ^ 2 + t ^ 2))
    have h2 : (Real.arctan (t / x)) ^ 2 / ((19964041536534117139:ℝ)/7046430720000000000) ≤ (((1721529301:ℝ)/1224720000)) ^ 2 / ((19964041536534117139:ℝ)/7046430720000000000) := by
      exact div_le_div_of_nonneg_right hθsq (le_of_lt hLDpos)
    exact h1.trans h2
  -- P bound
  have hP : (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) ≤ ((30317:ℝ)/250000) := by
    have hsqrt : Real.sqrt (17:ℝ) ≤ Real.sqrt (x ^ 2 + t ^ 2) := Real.sqrt_le_sqrt hQ3le
    have hd1 : (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) ≤ (1 : ℝ) / (2 * Real.sqrt (17:ℝ)) := by
      have hdenpos : 0 < 2 * Real.sqrt (17:ℝ) := by positivity
      exact div_le_div_of_nonneg_left (by norm_num : 0 ≤ (1 : ℝ)) hdenpos (by nlinarith)
    exact hd1.trans (inv_two_sqrt_le (17:ℝ) (by norm_num) ((30317:ℝ)/250000) (by norm_num) (by norm_num))
  -- S bound
  have hS : Real.log (x ^ 2 + t ^ 2) / 2 - Real.log (2 + t) ≤ (1 / 2) * ((2535917810003623:ℝ)/700000000000000) - ((250825351109:ℝ)/140000000000) := by
    nlinarith [hlogU, hDL]
  exact combine x t hxpos htpos ((2535917810003623:ℝ)/700000000000000) ((250825351109:ℝ)/140000000000) ((19964041536534117139:ℝ)/7046430720000000000) ((1721529301:ℝ)/1224720000) ((30317:ℝ)/250000) hLDpos hS hQden hP (by norm_num)

private lemma box_0_5 (x t : ℝ) (hx1 : 1 ≤ x) (hx2 : x ≤ 8) (ht : 1 ≤ t)
    (hxl : (1:ℝ) ≤ x) (hxu : x ≤ ((6:ℝ)/5)) (htl : (6:ℝ) ≤ t) (htu : t ≤ (9:ℝ)) :
    Real.log (Real.sqrt (x ^ 2 + t ^ 2)) +
        (Real.arctan (t / x)) ^ 2 / (2 * Real.log (Real.sqrt (x ^ 2 + t ^ 2))) +
        (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) ≤
      Real.log (2 + t) + (3 : ℝ) / 2 := by
  have hxpos : 0 < x := by linarith
  have htpos : 0 < t := by linarith
  have hapos : 0 < x ^ 2 + t ^ 2 := by positivity
  -- upper square bound
  have hx2le : x ^ 2 ≤ (((6:ℝ)/5)) ^ 2 := sq_le_of_nonneg (le_of_lt hxpos) hxu
  have ht2le : t ^ 2 ≤ ((9:ℝ)) ^ 2 := sq_le_of_nonneg (le_of_lt htpos) htu
  have ha_le : x ^ 2 + t ^ 2 ≤ ((2061:ℝ)/25) := by
    have : (((6:ℝ)/5)) ^ 2 + ((9:ℝ)) ^ 2 = ((2061:ℝ)/25) := by norm_num
    nlinarith
  have hlogU : Real.log (x ^ 2 + t ^ 2) ≤ ((829050246567802806063621:ℝ)/187904819200000000000000) := by
    exact (Real.log_le_log hapos ha_le).trans vlog_ub_m2061_25
  -- log(2+t) lower bound
  have hDmono : Real.log ((8:ℝ)) ≤ Real.log (2 + t) := by
    apply Real.log_le_log (by norm_num : 0 < (8:ℝ))
    linarith
  have hDL : ((20794415409:ℝ)/10000000000) ≤ Real.log (2 + t) := (vlog_lb_m8).trans hDmono
  -- lower square bound
  have hx2ge : ((1:ℝ)) ^ 2 ≤ x ^ 2 := sq_le_of_nonneg (by norm_num : 0 ≤ (1:ℝ)) hxl
  have ht2ge : ((6:ℝ)) ^ 2 ≤ t ^ 2 := sq_le_of_nonneg (by norm_num : 0 ≤ (6:ℝ)) htl
  have hQ3le : (37:ℝ) ≤ x ^ 2 + t ^ 2 := by
    have : ((1:ℝ)) ^ 2 + ((6:ℝ)) ^ 2 = (37:ℝ) := by norm_num
    nlinarith
  have hlogL : ((1302737042421079981271:ℝ)/360777252864000000000) ≤ Real.log (x ^ 2 + t ^ 2) := by
    exact (vlog_lb_m37).trans (Real.log_le_log (by norm_num : 0 < (37:ℝ)) hQ3le)
  have hLDpos : 0 < ((1302737042421079981271:ℝ)/360777252864000000000) := by norm_num
  -- arctan bound
  have htovx : t / x ≤ (9:ℝ) := by
    rw [div_le_iff₀ hxpos]
    have htu_le : (9:ℝ) ≤ (9:ℝ) * x := by
      calc
        (9:ℝ) = (9:ℝ) * (1:ℝ) := by norm_num
        _ ≤ (9:ℝ) * x := mul_le_mul_of_nonneg_left hxl (by norm_num : 0 ≤ (9:ℝ))
    nlinarith [htu_le]
  have hAT : Real.arctan (t / x) ≤ ((122216808841:ℝ)/83701957500) := (arctan_mono htovx).trans vatan_ub_m9
  have hθsq : (Real.arctan (t / x)) ^ 2 ≤ (((122216808841:ℝ)/83701957500)) ^ 2 := by
    have hθn : 0 ≤ Real.arctan (t / x) := Real.arctan_nonneg.mpr (div_nonneg (le_of_lt htpos) (le_of_lt hxpos))
    have hAn : 0 ≤ ((122216808841:ℝ)/83701957500) := by norm_num
    rw [sq_le_sq]
    rw [abs_of_nonneg hθn, abs_of_nonneg hAn]
    exact hAT
  have hQden : (Real.arctan (t / x)) ^ 2 / Real.log (x ^ 2 + t ^ 2) ≤
      (((122216808841:ℝ)/83701957500)) ^ 2 / (((1302737042421079981271:ℝ)/360777252864000000000)) := by
    have h1 : (Real.arctan (t / x)) ^ 2 / Real.log (x ^ 2 + t ^ 2) ≤
        (Real.arctan (t / x)) ^ 2 / ((1302737042421079981271:ℝ)/360777252864000000000) := by
      exact div_le_div_of_nonneg_left (sq_nonneg _) hLDpos (by linarith : ((1302737042421079981271:ℝ)/360777252864000000000) ≤ Real.log (x ^ 2 + t ^ 2))
    have h2 : (Real.arctan (t / x)) ^ 2 / ((1302737042421079981271:ℝ)/360777252864000000000) ≤ (((122216808841:ℝ)/83701957500)) ^ 2 / ((1302737042421079981271:ℝ)/360777252864000000000) := by
      exact div_le_div_of_nonneg_right hθsq (le_of_lt hLDpos)
    exact h1.trans h2
  -- P bound
  have hP : (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) ≤ ((411:ℝ)/5000) := by
    have hsqrt : Real.sqrt (37:ℝ) ≤ Real.sqrt (x ^ 2 + t ^ 2) := Real.sqrt_le_sqrt hQ3le
    have hd1 : (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) ≤ (1 : ℝ) / (2 * Real.sqrt (37:ℝ)) := by
      have hdenpos : 0 < 2 * Real.sqrt (37:ℝ) := by positivity
      exact div_le_div_of_nonneg_left (by norm_num : 0 ≤ (1 : ℝ)) hdenpos (by nlinarith)
    exact hd1.trans (inv_two_sqrt_le (37:ℝ) (by norm_num) ((411:ℝ)/5000) (by norm_num) (by norm_num))
  -- S bound
  have hS : Real.log (x ^ 2 + t ^ 2) / 2 - Real.log (2 + t) ≤ (1 / 2) * ((829050246567802806063621:ℝ)/187904819200000000000000) - ((20794415409:ℝ)/10000000000) := by
    nlinarith [hlogU, hDL]
  exact combine x t hxpos htpos ((829050246567802806063621:ℝ)/187904819200000000000000) ((20794415409:ℝ)/10000000000) ((1302737042421079981271:ℝ)/360777252864000000000) ((122216808841:ℝ)/83701957500) ((411:ℝ)/5000) hLDpos hS hQden hP (by norm_num)

private lemma box_0_6 (x t : ℝ) (hx1 : 1 ≤ x) (hx2 : x ≤ 8) (ht : 1 ≤ t)
    (hxl : (1:ℝ) ≤ x) (hxu : x ≤ ((6:ℝ)/5)) (htl : (9:ℝ) ≤ t) (htu : t ≤ (13:ℝ)) :
    Real.log (Real.sqrt (x ^ 2 + t ^ 2)) +
        (Real.arctan (t / x)) ^ 2 / (2 * Real.log (Real.sqrt (x ^ 2 + t ^ 2))) +
        (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) ≤
      Real.log (2 + t) + (3 : ℝ) / 2 := by
  have hxpos : 0 < x := by linarith
  have htpos : 0 < t := by linarith
  have hapos : 0 < x ^ 2 + t ^ 2 := by positivity
  -- upper square bound
  have hx2le : x ^ 2 ≤ (((6:ℝ)/5)) ^ 2 := sq_le_of_nonneg (le_of_lt hxpos) hxu
  have ht2le : t ^ 2 ≤ ((13:ℝ)) ^ 2 := sq_le_of_nonneg (le_of_lt htpos) htu
  have ha_le : x ^ 2 + t ^ 2 ≤ ((4261:ℝ)/25) := by
    have : (((6:ℝ)/5)) ^ 2 + ((13:ℝ)) ^ 2 = ((4261:ℝ)/25) := by norm_num
    nlinarith
  have hlogU : Real.log (x ^ 2 + t ^ 2) ≤ ((370763382579603115210133863:ℝ)/72155450572800000000000000) := by
    exact (Real.log_le_log hapos ha_le).trans vlog_ub_m4261_25
  -- log(2+t) lower bound
  have hDmono : Real.log ((11:ℝ)) ≤ Real.log (2 + t) := by
    apply Real.log_le_log (by norm_num : 0 < (11:ℝ))
    linarith
  have hDL : ((22000673184559761:ℝ)/9175040000000000) ≤ Real.log (2 + t) := (vlog_lb_m11).trans hDmono
  -- lower square bound
  have hx2ge : ((1:ℝ)) ^ 2 ≤ x ^ 2 := sq_le_of_nonneg (by norm_num : 0 ≤ (1:ℝ)) hxl
  have ht2ge : ((9:ℝ)) ^ 2 ≤ t ^ 2 := sq_le_of_nonneg (by norm_num : 0 ≤ (9:ℝ)) htl
  have hQ3le : (82:ℝ) ≤ x ^ 2 + t ^ 2 := by
    have : ((1:ℝ)) ^ 2 + ((9:ℝ)) ^ 2 = (82:ℝ) := by norm_num
    nlinarith
  have hlogL : ((2649739518702173634417:ℝ)/601295421440000000000) ≤ Real.log (x ^ 2 + t ^ 2) := by
    exact (vlog_lb_m82).trans (Real.log_le_log (by norm_num : 0 < (82:ℝ)) hQ3le)
  have hLDpos : 0 < ((2649739518702173634417:ℝ)/601295421440000000000) := by norm_num
  -- arctan bound
  have htovx : t / x ≤ (13:ℝ) := by
    rw [div_le_iff₀ hxpos]
    have htu_le : (13:ℝ) ≤ (13:ℝ) * x := by
      calc
        (13:ℝ) = (13:ℝ) * (1:ℝ) := by norm_num
        _ ≤ (13:ℝ) * x := mul_le_mul_of_nonneg_left hxl (by norm_num : 0 ≤ (13:ℝ))
    nlinarith [htu_le]
  have hAT : Real.arctan (t / x) ≤ ((4921772529439:ℝ)/3294297142500) := (arctan_mono htovx).trans vatan_ub_m13
  have hθsq : (Real.arctan (t / x)) ^ 2 ≤ (((4921772529439:ℝ)/3294297142500)) ^ 2 := by
    have hθn : 0 ≤ Real.arctan (t / x) := Real.arctan_nonneg.mpr (div_nonneg (le_of_lt htpos) (le_of_lt hxpos))
    have hAn : 0 ≤ ((4921772529439:ℝ)/3294297142500) := by norm_num
    rw [sq_le_sq]
    rw [abs_of_nonneg hθn, abs_of_nonneg hAn]
    exact hAT
  have hQden : (Real.arctan (t / x)) ^ 2 / Real.log (x ^ 2 + t ^ 2) ≤
      (((4921772529439:ℝ)/3294297142500)) ^ 2 / (((2649739518702173634417:ℝ)/601295421440000000000)) := by
    have h1 : (Real.arctan (t / x)) ^ 2 / Real.log (x ^ 2 + t ^ 2) ≤
        (Real.arctan (t / x)) ^ 2 / ((2649739518702173634417:ℝ)/601295421440000000000) := by
      exact div_le_div_of_nonneg_left (sq_nonneg _) hLDpos (by linarith : ((2649739518702173634417:ℝ)/601295421440000000000) ≤ Real.log (x ^ 2 + t ^ 2))
    have h2 : (Real.arctan (t / x)) ^ 2 / ((2649739518702173634417:ℝ)/601295421440000000000) ≤ (((4921772529439:ℝ)/3294297142500)) ^ 2 / ((2649739518702173634417:ℝ)/601295421440000000000) := by
      exact div_le_div_of_nonneg_right hθsq (le_of_lt hLDpos)
    exact h1.trans h2
  -- P bound
  have hP : (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) ≤ ((3451:ℝ)/62500) := by
    have hsqrt : Real.sqrt (82:ℝ) ≤ Real.sqrt (x ^ 2 + t ^ 2) := Real.sqrt_le_sqrt hQ3le
    have hd1 : (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) ≤ (1 : ℝ) / (2 * Real.sqrt (82:ℝ)) := by
      have hdenpos : 0 < 2 * Real.sqrt (82:ℝ) := by positivity
      exact div_le_div_of_nonneg_left (by norm_num : 0 ≤ (1 : ℝ)) hdenpos (by nlinarith)
    exact hd1.trans (inv_two_sqrt_le (82:ℝ) (by norm_num) ((3451:ℝ)/62500) (by norm_num) (by norm_num))
  -- S bound
  have hS : Real.log (x ^ 2 + t ^ 2) / 2 - Real.log (2 + t) ≤ (1 / 2) * ((370763382579603115210133863:ℝ)/72155450572800000000000000) - ((22000673184559761:ℝ)/9175040000000000) := by
    nlinarith [hlogU, hDL]
  exact combine x t hxpos htpos ((370763382579603115210133863:ℝ)/72155450572800000000000000) ((22000673184559761:ℝ)/9175040000000000) ((2649739518702173634417:ℝ)/601295421440000000000) ((4921772529439:ℝ)/3294297142500) ((3451:ℝ)/62500) hLDpos hS hQden hP (by norm_num)

private lemma box_0_7 (x t : ℝ) (hx1 : 1 ≤ x) (hx2 : x ≤ 8) (ht : 1 ≤ t)
    (hxl : (1:ℝ) ≤ x) (hxu : x ≤ ((6:ℝ)/5)) (htl : (13:ℝ) ≤ t) (htu : t ≤ (15:ℝ)) :
    Real.log (Real.sqrt (x ^ 2 + t ^ 2)) +
        (Real.arctan (t / x)) ^ 2 / (2 * Real.log (Real.sqrt (x ^ 2 + t ^ 2))) +
        (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) ≤
      Real.log (2 + t) + (3 : ℝ) / 2 := by
  have hxpos : 0 < x := by linarith
  have htpos : 0 < t := by linarith
  have hapos : 0 < x ^ 2 + t ^ 2 := by positivity
  -- upper square bound
  have hx2le : x ^ 2 ≤ (((6:ℝ)/5)) ^ 2 := sq_le_of_nonneg (le_of_lt hxpos) hxu
  have ht2le : t ^ 2 ≤ ((15:ℝ)) ^ 2 := sq_le_of_nonneg (le_of_lt htpos) htu
  have ha_le : x ^ 2 + t ^ 2 ≤ ((5661:ℝ)/25) := by
    have : (((6:ℝ)/5)) ^ 2 + ((15:ℝ)) ^ 2 = ((5661:ℝ)/25) := by norm_num
    nlinarith
  have hlogU : Real.log (x ^ 2 + t ^ 2) ≤ ((745259983925583903668173:ℝ)/137438953472000000000000) := by
    exact (Real.log_le_log hapos ha_le).trans vlog_ub_m5661_25
  -- log(2+t) lower bound
  have hDmono : Real.log ((15:ℝ)) ≤ Real.log (2 + t) := by
    apply Real.log_le_log (by norm_num : 0 < (15:ℝ))
    linarith
  have hDL : ((24846468902980723:ℝ)/9175040000000000) ≤ Real.log (2 + t) := (vlog_lb_m15).trans hDmono
  -- lower square bound
  have hx2ge : ((1:ℝ)) ^ 2 ≤ x ^ 2 := sq_le_of_nonneg (by norm_num : 0 ≤ (1:ℝ)) hxl
  have ht2ge : ((13:ℝ)) ^ 2 ≤ t ^ 2 := sq_le_of_nonneg (by norm_num : 0 ≤ (13:ℝ)) htl
  have hQ3le : (170:ℝ) ≤ x ^ 2 + t ^ 2 := by
    have : ((1:ℝ)) ^ 2 + ((13:ℝ)) ^ 2 = (170:ℝ) := by norm_num
    nlinarith
  have hlogL : ((112937318733729711136167:ℝ)/21990232555520000000000) ≤ Real.log (x ^ 2 + t ^ 2) := by
    exact (vlog_lb_m170).trans (Real.log_le_log (by norm_num : 0 < (170:ℝ)) hQ3le)
  have hLDpos : 0 < ((112937318733729711136167:ℝ)/21990232555520000000000) := by norm_num
  -- arctan bound
  have htovx : t / x ≤ (15:ℝ) := by
    rw [div_le_iff₀ hxpos]
    have htu_le : (15:ℝ) ≤ (15:ℝ) * x := by
      calc
        (15:ℝ) = (15:ℝ) * (1:ℝ) := by norm_num
        _ ≤ (15:ℝ) * x := mul_le_mul_of_nonneg_left hxl (by norm_num : 0 ≤ (15:ℝ))
    nlinarith [htu_le]
  have hAT : Real.arctan (t / x) ≤ ((7196339119:ℝ)/4784062500) := (arctan_mono htovx).trans vatan_ub_m15
  have hθsq : (Real.arctan (t / x)) ^ 2 ≤ (((7196339119:ℝ)/4784062500)) ^ 2 := by
    have hθn : 0 ≤ Real.arctan (t / x) := Real.arctan_nonneg.mpr (div_nonneg (le_of_lt htpos) (le_of_lt hxpos))
    have hAn : 0 ≤ ((7196339119:ℝ)/4784062500) := by norm_num
    rw [sq_le_sq]
    rw [abs_of_nonneg hθn, abs_of_nonneg hAn]
    exact hAT
  have hQden : (Real.arctan (t / x)) ^ 2 / Real.log (x ^ 2 + t ^ 2) ≤
      (((7196339119:ℝ)/4784062500)) ^ 2 / (((112937318733729711136167:ℝ)/21990232555520000000000)) := by
    have h1 : (Real.arctan (t / x)) ^ 2 / Real.log (x ^ 2 + t ^ 2) ≤
        (Real.arctan (t / x)) ^ 2 / ((112937318733729711136167:ℝ)/21990232555520000000000) := by
      exact div_le_div_of_nonneg_left (sq_nonneg _) hLDpos (by linarith : ((112937318733729711136167:ℝ)/21990232555520000000000) ≤ Real.log (x ^ 2 + t ^ 2))
    have h2 : (Real.arctan (t / x)) ^ 2 / ((112937318733729711136167:ℝ)/21990232555520000000000) ≤ (((7196339119:ℝ)/4784062500)) ^ 2 / ((112937318733729711136167:ℝ)/21990232555520000000000) := by
      exact div_le_div_of_nonneg_right hθsq (le_of_lt hLDpos)
    exact h1.trans h2
  -- P bound
  have hP : (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) ≤ ((38349:ℝ)/1000000) := by
    have hsqrt : Real.sqrt (170:ℝ) ≤ Real.sqrt (x ^ 2 + t ^ 2) := Real.sqrt_le_sqrt hQ3le
    have hd1 : (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) ≤ (1 : ℝ) / (2 * Real.sqrt (170:ℝ)) := by
      have hdenpos : 0 < 2 * Real.sqrt (170:ℝ) := by positivity
      exact div_le_div_of_nonneg_left (by norm_num : 0 ≤ (1 : ℝ)) hdenpos (by nlinarith)
    exact hd1.trans (inv_two_sqrt_le (170:ℝ) (by norm_num) ((38349:ℝ)/1000000) (by norm_num) (by norm_num))
  -- S bound
  have hS : Real.log (x ^ 2 + t ^ 2) / 2 - Real.log (2 + t) ≤ (1 / 2) * ((745259983925583903668173:ℝ)/137438953472000000000000) - ((24846468902980723:ℝ)/9175040000000000) := by
    nlinarith [hlogU, hDL]
  exact combine x t hxpos htpos ((745259983925583903668173:ℝ)/137438953472000000000000) ((24846468902980723:ℝ)/9175040000000000) ((112937318733729711136167:ℝ)/21990232555520000000000) ((7196339119:ℝ)/4784062500) ((38349:ℝ)/1000000) hLDpos hS hQden hP (by norm_num)

private lemma box_1_0 (x t : ℝ) (hx1 : 1 ≤ x) (hx2 : x ≤ 8) (ht : 1 ≤ t)
    (hxl : ((6:ℝ)/5) ≤ x) (hxu : x ≤ ((3:ℝ)/2)) (htl : (1:ℝ) ≤ t) (htu : t ≤ ((3:ℝ)/2)) :
    Real.log (Real.sqrt (x ^ 2 + t ^ 2)) +
        (Real.arctan (t / x)) ^ 2 / (2 * Real.log (Real.sqrt (x ^ 2 + t ^ 2))) +
        (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) ≤
      Real.log (2 + t) + (3 : ℝ) / 2 := by
  have hxpos : 0 < x := by linarith
  have htpos : 0 < t := by linarith
  have hapos : 0 < x ^ 2 + t ^ 2 := by positivity
  -- upper square bound
  have hx2le : x ^ 2 ≤ (((3:ℝ)/2)) ^ 2 := sq_le_of_nonneg (le_of_lt hxpos) hxu
  have ht2le : t ^ 2 ≤ (((3:ℝ)/2)) ^ 2 := sq_le_of_nonneg (le_of_lt htpos) htu
  have ha_le : x ^ 2 + t ^ 2 ≤ ((9:ℝ)/2) := by
    have : (((3:ℝ)/2)) ^ 2 + (((3:ℝ)/2)) ^ 2 = ((9:ℝ)/2) := by norm_num
    nlinarith
  have hlogU : Real.log (x ^ 2 + t ^ 2) ≤ ((215624536632101:ℝ)/143360000000000) := by
    exact (Real.log_le_log hapos ha_le).trans vlog_ub_m9_2
  -- log(2+t) lower bound
  have hDmono : Real.log ((3:ℝ)) ≤ Real.log (2 + t) := by
    apply Real.log_le_log (by norm_num : 0 < (3:ℝ))
    linarith
  have hDL : ((153784745867:ℝ)/140000000000) ≤ Real.log (2 + t) := (vlog_lb_m3).trans hDmono
  -- lower square bound
  have hx2ge : (((6:ℝ)/5)) ^ 2 ≤ x ^ 2 := sq_le_of_nonneg (by norm_num : 0 ≤ ((6:ℝ)/5)) hxl
  have ht2ge : ((1:ℝ)) ^ 2 ≤ t ^ 2 := sq_le_of_nonneg (by norm_num : 0 ≤ (1:ℝ)) htl
  have hQ3le : ((61:ℝ)/25) ≤ x ^ 2 + t ^ 2 := by
    have : (((6:ℝ)/5)) ^ 2 + ((1:ℝ)) ^ 2 = ((61:ℝ)/25) := by norm_num
    nlinarith
  have hlogL : ((5853736396217449:ℝ)/6562500000000000) ≤ Real.log (x ^ 2 + t ^ 2) := by
    exact (vlog_lb_m61_25).trans (Real.log_le_log (by norm_num : 0 < ((61:ℝ)/25)) hQ3le)
  have hLDpos : 0 < ((5853736396217449:ℝ)/6562500000000000) := by norm_num
  -- arctan bound
  have htovx : t / x ≤ ((5:ℝ)/4) := by
    rw [div_le_iff₀ hxpos]
    have htu_le : ((3:ℝ)/2) ≤ ((5:ℝ)/4) * x := by
      calc
        ((3:ℝ)/2) = ((5:ℝ)/4) * ((6:ℝ)/5) := by norm_num
        _ ≤ ((5:ℝ)/4) * x := mul_le_mul_of_nonneg_left hxl (by norm_num : 0 ≤ ((5:ℝ)/4))
    nlinarith [htu_le]
  have hAT : Real.arctan (t / x) ≤ ((5944903:ℝ)/6562500) := (arctan_mono htovx).trans vatan_ub_m5_4
  have hθsq : (Real.arctan (t / x)) ^ 2 ≤ (((5944903:ℝ)/6562500)) ^ 2 := by
    have hθn : 0 ≤ Real.arctan (t / x) := Real.arctan_nonneg.mpr (div_nonneg (le_of_lt htpos) (le_of_lt hxpos))
    have hAn : 0 ≤ ((5944903:ℝ)/6562500) := by norm_num
    rw [sq_le_sq]
    rw [abs_of_nonneg hθn, abs_of_nonneg hAn]
    exact hAT
  have hQden : (Real.arctan (t / x)) ^ 2 / Real.log (x ^ 2 + t ^ 2) ≤
      (((5944903:ℝ)/6562500)) ^ 2 / (((5853736396217449:ℝ)/6562500000000000)) := by
    have h1 : (Real.arctan (t / x)) ^ 2 / Real.log (x ^ 2 + t ^ 2) ≤
        (Real.arctan (t / x)) ^ 2 / ((5853736396217449:ℝ)/6562500000000000) := by
      exact div_le_div_of_nonneg_left (sq_nonneg _) hLDpos (by linarith : ((5853736396217449:ℝ)/6562500000000000) ≤ Real.log (x ^ 2 + t ^ 2))
    have h2 : (Real.arctan (t / x)) ^ 2 / ((5853736396217449:ℝ)/6562500000000000) ≤ (((5944903:ℝ)/6562500)) ^ 2 / ((5853736396217449:ℝ)/6562500000000000) := by
      exact div_le_div_of_nonneg_right hθsq (le_of_lt hLDpos)
    exact h1.trans h2
  -- P bound
  have hP : (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) ≤ ((320093:ℝ)/1000000) := by
    have hsqrt : Real.sqrt ((61:ℝ)/25) ≤ Real.sqrt (x ^ 2 + t ^ 2) := Real.sqrt_le_sqrt hQ3le
    have hd1 : (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) ≤ (1 : ℝ) / (2 * Real.sqrt ((61:ℝ)/25)) := by
      have hdenpos : 0 < 2 * Real.sqrt ((61:ℝ)/25) := by positivity
      exact div_le_div_of_nonneg_left (by norm_num : 0 ≤ (1 : ℝ)) hdenpos (by nlinarith)
    exact hd1.trans (inv_two_sqrt_le ((61:ℝ)/25) (by norm_num) ((320093:ℝ)/1000000) (by norm_num) (by norm_num))
  -- S bound
  have hS : Real.log (x ^ 2 + t ^ 2) / 2 - Real.log (2 + t) ≤ (1 / 2) * ((215624536632101:ℝ)/143360000000000) - ((153784745867:ℝ)/140000000000) := by
    nlinarith [hlogU, hDL]
  exact combine x t hxpos htpos ((215624536632101:ℝ)/143360000000000) ((153784745867:ℝ)/140000000000) ((5853736396217449:ℝ)/6562500000000000) ((5944903:ℝ)/6562500) ((320093:ℝ)/1000000) hLDpos hS hQden hP (by norm_num)

private lemma box_1_1 (x t : ℝ) (hx1 : 1 ≤ x) (hx2 : x ≤ 8) (ht : 1 ≤ t)
    (hxl : ((6:ℝ)/5) ≤ x) (hxu : x ≤ ((3:ℝ)/2)) (htl : ((3:ℝ)/2) ≤ t) (htu : t ≤ (2:ℝ)) :
    Real.log (Real.sqrt (x ^ 2 + t ^ 2)) +
        (Real.arctan (t / x)) ^ 2 / (2 * Real.log (Real.sqrt (x ^ 2 + t ^ 2))) +
        (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) ≤
      Real.log (2 + t) + (3 : ℝ) / 2 := by
  have hxpos : 0 < x := by linarith
  have htpos : 0 < t := by linarith
  have hapos : 0 < x ^ 2 + t ^ 2 := by positivity
  -- upper square bound
  have hx2le : x ^ 2 ≤ (((3:ℝ)/2)) ^ 2 := sq_le_of_nonneg (le_of_lt hxpos) hxu
  have ht2le : t ^ 2 ≤ ((2:ℝ)) ^ 2 := sq_le_of_nonneg (le_of_lt htpos) htu
  have ha_le : x ^ 2 + t ^ 2 ≤ ((25:ℝ)/4) := by
    have : (((3:ℝ)/2)) ^ 2 + ((2:ℝ)) ^ 2 = ((25:ℝ)/4) := by norm_num
    nlinarith
  have hlogU : Real.log (x ^ 2 + t ^ 2) ≤ ((115296323144801719:ℝ)/62914560000000000) := by
    exact (Real.log_le_log hapos ha_le).trans vlog_ub_m25_4
  -- log(2+t) lower bound
  have hDmono : Real.log (((7:ℝ)/2)) ≤ Real.log (2 + t) := by
    apply Real.log_le_log (by norm_num : 0 < ((7:ℝ)/2))
    linarith
  have hDL : ((269394135787799:ℝ)/215040000000000) ≤ Real.log (2 + t) := (vlog_lb_m7_2).trans hDmono
  -- lower square bound
  have hx2ge : (((6:ℝ)/5)) ^ 2 ≤ x ^ 2 := sq_le_of_nonneg (by norm_num : 0 ≤ ((6:ℝ)/5)) hxl
  have ht2ge : (((3:ℝ)/2)) ^ 2 ≤ t ^ 2 := sq_le_of_nonneg (by norm_num : 0 ≤ ((3:ℝ)/2)) htl
  have hQ3le : ((369:ℝ)/100) ≤ x ^ 2 + t ^ 2 := by
    have : (((6:ℝ)/5)) ^ 2 + (((3:ℝ)/2)) ^ 2 = ((369:ℝ)/100) := by norm_num
    nlinarith
  have hlogL : ((7486984345320254989:ℝ)/5734400000000000000) ≤ Real.log (x ^ 2 + t ^ 2) := by
    exact (vlog_lb_m369_100).trans (Real.log_le_log (by norm_num : 0 < ((369:ℝ)/100)) hQ3le)
  have hLDpos : 0 < ((7486984345320254989:ℝ)/5734400000000000000) := by norm_num
  -- arctan bound
  have htovx : t / x ≤ ((5:ℝ)/3) := by
    rw [div_le_iff₀ hxpos]
    have htu_le : (2:ℝ) ≤ ((5:ℝ)/3) * x := by
      calc
        (2:ℝ) = ((5:ℝ)/3) * ((6:ℝ)/5) := by norm_num
        _ ≤ ((5:ℝ)/3) * x := mul_le_mul_of_nonneg_left hxl (by norm_num : 0 ≤ ((5:ℝ)/3))
    nlinarith [htu_le]
  have hAT : Real.arctan (t / x) ≤ ((2255853:ℝ)/2187500) := (arctan_mono htovx).trans vatan_ub_m5_3
  have hθsq : (Real.arctan (t / x)) ^ 2 ≤ (((2255853:ℝ)/2187500)) ^ 2 := by
    have hθn : 0 ≤ Real.arctan (t / x) := Real.arctan_nonneg.mpr (div_nonneg (le_of_lt htpos) (le_of_lt hxpos))
    have hAn : 0 ≤ ((2255853:ℝ)/2187500) := by norm_num
    rw [sq_le_sq]
    rw [abs_of_nonneg hθn, abs_of_nonneg hAn]
    exact hAT
  have hQden : (Real.arctan (t / x)) ^ 2 / Real.log (x ^ 2 + t ^ 2) ≤
      (((2255853:ℝ)/2187500)) ^ 2 / (((7486984345320254989:ℝ)/5734400000000000000)) := by
    have h1 : (Real.arctan (t / x)) ^ 2 / Real.log (x ^ 2 + t ^ 2) ≤
        (Real.arctan (t / x)) ^ 2 / ((7486984345320254989:ℝ)/5734400000000000000) := by
      exact div_le_div_of_nonneg_left (sq_nonneg _) hLDpos (by linarith : ((7486984345320254989:ℝ)/5734400000000000000) ≤ Real.log (x ^ 2 + t ^ 2))
    have h2 : (Real.arctan (t / x)) ^ 2 / ((7486984345320254989:ℝ)/5734400000000000000) ≤ (((2255853:ℝ)/2187500)) ^ 2 / ((7486984345320254989:ℝ)/5734400000000000000) := by
      exact div_le_div_of_nonneg_right hθsq (le_of_lt hLDpos)
    exact h1.trans h2
  -- P bound
  have hP : (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) ≤ ((26029:ℝ)/100000) := by
    have hsqrt : Real.sqrt ((369:ℝ)/100) ≤ Real.sqrt (x ^ 2 + t ^ 2) := Real.sqrt_le_sqrt hQ3le
    have hd1 : (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) ≤ (1 : ℝ) / (2 * Real.sqrt ((369:ℝ)/100)) := by
      have hdenpos : 0 < 2 * Real.sqrt ((369:ℝ)/100) := by positivity
      exact div_le_div_of_nonneg_left (by norm_num : 0 ≤ (1 : ℝ)) hdenpos (by nlinarith)
    exact hd1.trans (inv_two_sqrt_le ((369:ℝ)/100) (by norm_num) ((26029:ℝ)/100000) (by norm_num) (by norm_num))
  -- S bound
  have hS : Real.log (x ^ 2 + t ^ 2) / 2 - Real.log (2 + t) ≤ (1 / 2) * ((115296323144801719:ℝ)/62914560000000000) - ((269394135787799:ℝ)/215040000000000) := by
    nlinarith [hlogU, hDL]
  exact combine x t hxpos htpos ((115296323144801719:ℝ)/62914560000000000) ((269394135787799:ℝ)/215040000000000) ((7486984345320254989:ℝ)/5734400000000000000) ((2255853:ℝ)/2187500) ((26029:ℝ)/100000) hLDpos hS hQden hP (by norm_num)

private lemma box_1_2 (x t : ℝ) (hx1 : 1 ≤ x) (hx2 : x ≤ 8) (ht : 1 ≤ t)
    (hxl : ((6:ℝ)/5) ≤ x) (hxu : x ≤ ((3:ℝ)/2)) (htl : (2:ℝ) ≤ t) (htu : t ≤ (3:ℝ)) :
    Real.log (Real.sqrt (x ^ 2 + t ^ 2)) +
        (Real.arctan (t / x)) ^ 2 / (2 * Real.log (Real.sqrt (x ^ 2 + t ^ 2))) +
        (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) ≤
      Real.log (2 + t) + (3 : ℝ) / 2 := by
  have hxpos : 0 < x := by linarith
  have htpos : 0 < t := by linarith
  have hapos : 0 < x ^ 2 + t ^ 2 := by positivity
  -- upper square bound
  have hx2le : x ^ 2 ≤ (((3:ℝ)/2)) ^ 2 := sq_le_of_nonneg (le_of_lt hxpos) hxu
  have ht2le : t ^ 2 ≤ ((3:ℝ)) ^ 2 := sq_le_of_nonneg (le_of_lt htpos) htu
  have ha_le : x ^ 2 + t ^ 2 ≤ ((45:ℝ)/4) := by
    have : (((3:ℝ)/2)) ^ 2 + ((3:ℝ)) ^ 2 = ((45:ℝ)/4) := by norm_num
    nlinarith
  have hlogU : Real.log (x ^ 2 + t ^ 2) ≤ ((5685145627975592301:ℝ)/2348810240000000000) := by
    exact (Real.log_le_log hapos ha_le).trans vlog_ub_m45_4
  -- log(2+t) lower bound
  have hDmono : Real.log ((4:ℝ)) ≤ Real.log (2 + t) := by
    apply Real.log_le_log (by norm_num : 0 < (4:ℝ))
    linarith
  have hDL : ((6931471803:ℝ)/5000000000) ≤ Real.log (2 + t) := (vlog_lb_m4).trans hDmono
  -- lower square bound
  have hx2ge : (((6:ℝ)/5)) ^ 2 ≤ x ^ 2 := sq_le_of_nonneg (by norm_num : 0 ≤ ((6:ℝ)/5)) hxl
  have ht2ge : ((2:ℝ)) ^ 2 ≤ t ^ 2 := sq_le_of_nonneg (by norm_num : 0 ≤ (2:ℝ)) htl
  have hQ3le : ((136:ℝ)/25) ≤ x ^ 2 + t ^ 2 := by
    have : (((6:ℝ)/5)) ^ 2 + ((2:ℝ)) ^ 2 = ((136:ℝ)/25) := by norm_num
    nlinarith
  have hlogL : ((926280759685317:ℝ)/546875000000000) ≤ Real.log (x ^ 2 + t ^ 2) := by
    exact (vlog_lb_m136_25).trans (Real.log_le_log (by norm_num : 0 < ((136:ℝ)/25)) hQ3le)
  have hLDpos : 0 < ((926280759685317:ℝ)/546875000000000) := by norm_num
  -- arctan bound
  have htovx : t / x ≤ ((5:ℝ)/2) := by
    rw [div_le_iff₀ hxpos]
    have htu_le : (3:ℝ) ≤ ((5:ℝ)/2) * x := by
      calc
        (3:ℝ) = ((5:ℝ)/2) * ((6:ℝ)/5) := by norm_num
        _ ≤ ((5:ℝ)/2) * x := mul_le_mul_of_nonneg_left hxl (by norm_num : 0 ≤ ((5:ℝ)/2))
    nlinarith [htu_le]
  have hAT : Real.arctan (t / x) ≤ ((7811471:ℝ)/6562500) := (arctan_mono htovx).trans vatan_ub_m5_2
  have hθsq : (Real.arctan (t / x)) ^ 2 ≤ (((7811471:ℝ)/6562500)) ^ 2 := by
    have hθn : 0 ≤ Real.arctan (t / x) := Real.arctan_nonneg.mpr (div_nonneg (le_of_lt htpos) (le_of_lt hxpos))
    have hAn : 0 ≤ ((7811471:ℝ)/6562500) := by norm_num
    rw [sq_le_sq]
    rw [abs_of_nonneg hθn, abs_of_nonneg hAn]
    exact hAT
  have hQden : (Real.arctan (t / x)) ^ 2 / Real.log (x ^ 2 + t ^ 2) ≤
      (((7811471:ℝ)/6562500)) ^ 2 / (((926280759685317:ℝ)/546875000000000)) := by
    have h1 : (Real.arctan (t / x)) ^ 2 / Real.log (x ^ 2 + t ^ 2) ≤
        (Real.arctan (t / x)) ^ 2 / ((926280759685317:ℝ)/546875000000000) := by
      exact div_le_div_of_nonneg_left (sq_nonneg _) hLDpos (by linarith : ((926280759685317:ℝ)/546875000000000) ≤ Real.log (x ^ 2 + t ^ 2))
    have h2 : (Real.arctan (t / x)) ^ 2 / ((926280759685317:ℝ)/546875000000000) ≤ (((7811471:ℝ)/6562500)) ^ 2 / ((926280759685317:ℝ)/546875000000000) := by
      exact div_le_div_of_nonneg_right hθsq (le_of_lt hLDpos)
    exact h1.trans h2
  -- P bound
  have hP : (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) ≤ ((107187:ℝ)/500000) := by
    have hsqrt : Real.sqrt ((136:ℝ)/25) ≤ Real.sqrt (x ^ 2 + t ^ 2) := Real.sqrt_le_sqrt hQ3le
    have hd1 : (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) ≤ (1 : ℝ) / (2 * Real.sqrt ((136:ℝ)/25)) := by
      have hdenpos : 0 < 2 * Real.sqrt ((136:ℝ)/25) := by positivity
      exact div_le_div_of_nonneg_left (by norm_num : 0 ≤ (1 : ℝ)) hdenpos (by nlinarith)
    exact hd1.trans (inv_two_sqrt_le ((136:ℝ)/25) (by norm_num) ((107187:ℝ)/500000) (by norm_num) (by norm_num))
  -- S bound
  have hS : Real.log (x ^ 2 + t ^ 2) / 2 - Real.log (2 + t) ≤ (1 / 2) * ((5685145627975592301:ℝ)/2348810240000000000) - ((6931471803:ℝ)/5000000000) := by
    nlinarith [hlogU, hDL]
  exact combine x t hxpos htpos ((5685145627975592301:ℝ)/2348810240000000000) ((6931471803:ℝ)/5000000000) ((926280759685317:ℝ)/546875000000000) ((7811471:ℝ)/6562500) ((107187:ℝ)/500000) hLDpos hS hQden hP (by norm_num)

private lemma box_1_3 (x t : ℝ) (hx1 : 1 ≤ x) (hx2 : x ≤ 8) (ht : 1 ≤ t)
    (hxl : ((6:ℝ)/5) ≤ x) (hxu : x ≤ ((3:ℝ)/2)) (htl : (3:ℝ) ≤ t) (htu : t ≤ (4:ℝ)) :
    Real.log (Real.sqrt (x ^ 2 + t ^ 2)) +
        (Real.arctan (t / x)) ^ 2 / (2 * Real.log (Real.sqrt (x ^ 2 + t ^ 2))) +
        (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) ≤
      Real.log (2 + t) + (3 : ℝ) / 2 := by
  have hxpos : 0 < x := by linarith
  have htpos : 0 < t := by linarith
  have hapos : 0 < x ^ 2 + t ^ 2 := by positivity
  -- upper square bound
  have hx2le : x ^ 2 ≤ (((3:ℝ)/2)) ^ 2 := sq_le_of_nonneg (le_of_lt hxpos) hxu
  have ht2le : t ^ 2 ≤ ((4:ℝ)) ^ 2 := sq_le_of_nonneg (le_of_lt htpos) htu
  have ha_le : x ^ 2 + t ^ 2 ≤ ((73:ℝ)/4) := by
    have : (((3:ℝ)/2)) ^ 2 + ((4:ℝ)) ^ 2 = ((73:ℝ)/4) := by norm_num
    nlinarith
  have hlogU : Real.log (x ^ 2 + t ^ 2) ≤ ((873130588261786893329:ℝ)/300647710720000000000) := by
    exact (Real.log_le_log hapos ha_le).trans vlog_ub_m73_4
  -- log(2+t) lower bound
  have hDmono : Real.log ((5:ℝ)) ≤ Real.log (2 + t) := by
    apply Real.log_le_log (by norm_num : 0 < (5:ℝ))
    linarith
  have hDL : ((173046727073587:ℝ)/107520000000000) ≤ Real.log (2 + t) := (vlog_lb_m5).trans hDmono
  -- lower square bound
  have hx2ge : (((6:ℝ)/5)) ^ 2 ≤ x ^ 2 := sq_le_of_nonneg (by norm_num : 0 ≤ ((6:ℝ)/5)) hxl
  have ht2ge : ((3:ℝ)) ^ 2 ≤ t ^ 2 := sq_le_of_nonneg (by norm_num : 0 ≤ (3:ℝ)) htl
  have hQ3le : ((261:ℝ)/25) ≤ x ^ 2 + t ^ 2 := by
    have : (((6:ℝ)/5)) ^ 2 + ((3:ℝ)) ^ 2 = ((261:ℝ)/25) := by norm_num
    nlinarith
  have hlogL : ((336271321631178812633:ℝ)/143360000000000000000) ≤ Real.log (x ^ 2 + t ^ 2) := by
    exact (vlog_lb_m261_25).trans (Real.log_le_log (by norm_num : 0 < ((261:ℝ)/25)) hQ3le)
  have hLDpos : 0 < ((336271321631178812633:ℝ)/143360000000000000000) := by norm_num
  -- arctan bound
  have htovx : t / x ≤ ((10:ℝ)/3) := by
    rw [div_le_iff₀ hxpos]
    have htu_le : (4:ℝ) ≤ ((10:ℝ)/3) * x := by
      calc
        (4:ℝ) = ((10:ℝ)/3) * ((6:ℝ)/5) := by norm_num
        _ ≤ ((10:ℝ)/3) * x := mul_le_mul_of_nonneg_left hxl (by norm_num : 0 ≤ ((10:ℝ)/3))
    nlinarith [htu_le]
  have hAT : Real.arctan (t / x) ≤ ((89554167:ℝ)/70000000) := (arctan_mono htovx).trans vatan_ub_m10_3
  have hθsq : (Real.arctan (t / x)) ^ 2 ≤ (((89554167:ℝ)/70000000)) ^ 2 := by
    have hθn : 0 ≤ Real.arctan (t / x) := Real.arctan_nonneg.mpr (div_nonneg (le_of_lt htpos) (le_of_lt hxpos))
    have hAn : 0 ≤ ((89554167:ℝ)/70000000) := by norm_num
    rw [sq_le_sq]
    rw [abs_of_nonneg hθn, abs_of_nonneg hAn]
    exact hAT
  have hQden : (Real.arctan (t / x)) ^ 2 / Real.log (x ^ 2 + t ^ 2) ≤
      (((89554167:ℝ)/70000000)) ^ 2 / (((336271321631178812633:ℝ)/143360000000000000000)) := by
    have h1 : (Real.arctan (t / x)) ^ 2 / Real.log (x ^ 2 + t ^ 2) ≤
        (Real.arctan (t / x)) ^ 2 / ((336271321631178812633:ℝ)/143360000000000000000) := by
      exact div_le_div_of_nonneg_left (sq_nonneg _) hLDpos (by linarith : ((336271321631178812633:ℝ)/143360000000000000000) ≤ Real.log (x ^ 2 + t ^ 2))
    have h2 : (Real.arctan (t / x)) ^ 2 / ((336271321631178812633:ℝ)/143360000000000000000) ≤ (((89554167:ℝ)/70000000)) ^ 2 / ((336271321631178812633:ℝ)/143360000000000000000) := by
      exact div_le_div_of_nonneg_right hθsq (le_of_lt hLDpos)
    exact h1.trans h2
  -- P bound
  have hP : (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) ≤ ((154747:ℝ)/1000000) := by
    have hsqrt : Real.sqrt ((261:ℝ)/25) ≤ Real.sqrt (x ^ 2 + t ^ 2) := Real.sqrt_le_sqrt hQ3le
    have hd1 : (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) ≤ (1 : ℝ) / (2 * Real.sqrt ((261:ℝ)/25)) := by
      have hdenpos : 0 < 2 * Real.sqrt ((261:ℝ)/25) := by positivity
      exact div_le_div_of_nonneg_left (by norm_num : 0 ≤ (1 : ℝ)) hdenpos (by nlinarith)
    exact hd1.trans (inv_two_sqrt_le ((261:ℝ)/25) (by norm_num) ((154747:ℝ)/1000000) (by norm_num) (by norm_num))
  -- S bound
  have hS : Real.log (x ^ 2 + t ^ 2) / 2 - Real.log (2 + t) ≤ (1 / 2) * ((873130588261786893329:ℝ)/300647710720000000000) - ((173046727073587:ℝ)/107520000000000) := by
    nlinarith [hlogU, hDL]
  exact combine x t hxpos htpos ((873130588261786893329:ℝ)/300647710720000000000) ((173046727073587:ℝ)/107520000000000) ((336271321631178812633:ℝ)/143360000000000000000) ((89554167:ℝ)/70000000) ((154747:ℝ)/1000000) hLDpos hS hQden hP (by norm_num)

private lemma box_1_4 (x t : ℝ) (hx1 : 1 ≤ x) (hx2 : x ≤ 8) (ht : 1 ≤ t)
    (hxl : ((6:ℝ)/5) ≤ x) (hxu : x ≤ ((3:ℝ)/2)) (htl : (4:ℝ) ≤ t) (htu : t ≤ (6:ℝ)) :
    Real.log (Real.sqrt (x ^ 2 + t ^ 2)) +
        (Real.arctan (t / x)) ^ 2 / (2 * Real.log (Real.sqrt (x ^ 2 + t ^ 2))) +
        (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) ≤
      Real.log (2 + t) + (3 : ℝ) / 2 := by
  have hxpos : 0 < x := by linarith
  have htpos : 0 < t := by linarith
  have hapos : 0 < x ^ 2 + t ^ 2 := by positivity
  -- upper square bound
  have hx2le : x ^ 2 ≤ (((3:ℝ)/2)) ^ 2 := sq_le_of_nonneg (le_of_lt hxpos) hxu
  have ht2le : t ^ 2 ≤ ((6:ℝ)) ^ 2 := sq_le_of_nonneg (le_of_lt htpos) htu
  have ha_le : x ^ 2 + t ^ 2 ≤ ((153:ℝ)/4) := by
    have : (((3:ℝ)/2)) ^ 2 + ((6:ℝ)) ^ 2 = ((153:ℝ)/4) := by norm_num
    nlinarith
  have hlogU : Real.log (x ^ 2 + t ^ 2) ≤ ((28047449270254698164653:ℝ)/7696581394432000000000) := by
    exact (Real.log_le_log hapos ha_le).trans vlog_ub_m153_4
  -- log(2+t) lower bound
  have hDmono : Real.log ((6:ℝ)) ≤ Real.log (2 + t) := by
    apply Real.log_le_log (by norm_num : 0 < (6:ℝ))
    linarith
  have hDL : ((250825351109:ℝ)/140000000000) ≤ Real.log (2 + t) := (vlog_lb_m6).trans hDmono
  -- lower square bound
  have hx2ge : (((6:ℝ)/5)) ^ 2 ≤ x ^ 2 := sq_le_of_nonneg (by norm_num : 0 ≤ ((6:ℝ)/5)) hxl
  have ht2ge : ((4:ℝ)) ^ 2 ≤ t ^ 2 := sq_le_of_nonneg (by norm_num : 0 ≤ (4:ℝ)) htl
  have hQ3le : ((436:ℝ)/25) ≤ x ^ 2 + t ^ 2 := by
    have : (((6:ℝ)/5)) ^ 2 + ((4:ℝ)) ^ 2 = ((436:ℝ)/25) := by norm_num
    nlinarith
  have hlogL : ((1600909193744688153:ℝ)/560000000000000000) ≤ Real.log (x ^ 2 + t ^ 2) := by
    exact (vlog_lb_m436_25).trans (Real.log_le_log (by norm_num : 0 < ((436:ℝ)/25)) hQ3le)
  have hLDpos : 0 < ((1600909193744688153:ℝ)/560000000000000000) := by norm_num
  -- arctan bound
  have htovx : t / x ≤ (5:ℝ) := by
    rw [div_le_iff₀ hxpos]
    have htu_le : (6:ℝ) ≤ (5:ℝ) * x := by
      calc
        (6:ℝ) = (5:ℝ) * ((6:ℝ)/5) := by norm_num
        _ ≤ (5:ℝ) * x := mul_le_mul_of_nonneg_left hxl (by norm_num : 0 ≤ (5:ℝ))
    nlinarith [htu_le]
  have hAT : Real.arctan (t / x) ≤ ((9012967:ℝ)/6562500) := (arctan_mono htovx).trans vatan_ub_m5
  have hθsq : (Real.arctan (t / x)) ^ 2 ≤ (((9012967:ℝ)/6562500)) ^ 2 := by
    have hθn : 0 ≤ Real.arctan (t / x) := Real.arctan_nonneg.mpr (div_nonneg (le_of_lt htpos) (le_of_lt hxpos))
    have hAn : 0 ≤ ((9012967:ℝ)/6562500) := by norm_num
    rw [sq_le_sq]
    rw [abs_of_nonneg hθn, abs_of_nonneg hAn]
    exact hAT
  have hQden : (Real.arctan (t / x)) ^ 2 / Real.log (x ^ 2 + t ^ 2) ≤
      (((9012967:ℝ)/6562500)) ^ 2 / (((1600909193744688153:ℝ)/560000000000000000)) := by
    have h1 : (Real.arctan (t / x)) ^ 2 / Real.log (x ^ 2 + t ^ 2) ≤
        (Real.arctan (t / x)) ^ 2 / ((1600909193744688153:ℝ)/560000000000000000) := by
      exact div_le_div_of_nonneg_left (sq_nonneg _) hLDpos (by linarith : ((1600909193744688153:ℝ)/560000000000000000) ≤ Real.log (x ^ 2 + t ^ 2))
    have h2 : (Real.arctan (t / x)) ^ 2 / ((1600909193744688153:ℝ)/560000000000000000) ≤ (((9012967:ℝ)/6562500)) ^ 2 / ((1600909193744688153:ℝ)/560000000000000000) := by
      exact div_le_div_of_nonneg_right hθsq (le_of_lt hLDpos)
    exact h1.trans h2
  -- P bound
  have hP : (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) ≤ ((119729:ℝ)/1000000) := by
    have hsqrt : Real.sqrt ((436:ℝ)/25) ≤ Real.sqrt (x ^ 2 + t ^ 2) := Real.sqrt_le_sqrt hQ3le
    have hd1 : (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) ≤ (1 : ℝ) / (2 * Real.sqrt ((436:ℝ)/25)) := by
      have hdenpos : 0 < 2 * Real.sqrt ((436:ℝ)/25) := by positivity
      exact div_le_div_of_nonneg_left (by norm_num : 0 ≤ (1 : ℝ)) hdenpos (by nlinarith)
    exact hd1.trans (inv_two_sqrt_le ((436:ℝ)/25) (by norm_num) ((119729:ℝ)/1000000) (by norm_num) (by norm_num))
  -- S bound
  have hS : Real.log (x ^ 2 + t ^ 2) / 2 - Real.log (2 + t) ≤ (1 / 2) * ((28047449270254698164653:ℝ)/7696581394432000000000) - ((250825351109:ℝ)/140000000000) := by
    nlinarith [hlogU, hDL]
  exact combine x t hxpos htpos ((28047449270254698164653:ℝ)/7696581394432000000000) ((250825351109:ℝ)/140000000000) ((1600909193744688153:ℝ)/560000000000000000) ((9012967:ℝ)/6562500) ((119729:ℝ)/1000000) hLDpos hS hQden hP (by norm_num)

private lemma box_1_5 (x t : ℝ) (hx1 : 1 ≤ x) (hx2 : x ≤ 8) (ht : 1 ≤ t)
    (hxl : ((6:ℝ)/5) ≤ x) (hxu : x ≤ ((3:ℝ)/2)) (htl : (6:ℝ) ≤ t) (htu : t ≤ (9:ℝ)) :
    Real.log (Real.sqrt (x ^ 2 + t ^ 2)) +
        (Real.arctan (t / x)) ^ 2 / (2 * Real.log (Real.sqrt (x ^ 2 + t ^ 2))) +
        (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) ≤
      Real.log (2 + t) + (3 : ℝ) / 2 := by
  have hxpos : 0 < x := by linarith
  have htpos : 0 < t := by linarith
  have hapos : 0 < x ^ 2 + t ^ 2 := by positivity
  -- upper square bound
  have hx2le : x ^ 2 ≤ (((3:ℝ)/2)) ^ 2 := sq_le_of_nonneg (le_of_lt hxpos) hxu
  have ht2le : t ^ 2 ≤ ((9:ℝ)) ^ 2 := sq_le_of_nonneg (le_of_lt htpos) htu
  have ha_le : x ^ 2 + t ^ 2 ≤ ((333:ℝ)/4) := by
    have : (((3:ℝ)/2)) ^ 2 + ((9:ℝ)) ^ 2 = ((333:ℝ)/4) := by norm_num
    nlinarith
  have hlogU : Real.log (x ^ 2 + t ^ 2) ≤ ((3111603650802786328825947:ℝ)/703687441776640000000000) := by
    exact (Real.log_le_log hapos ha_le).trans vlog_ub_m333_4
  -- log(2+t) lower bound
  have hDmono : Real.log ((8:ℝ)) ≤ Real.log (2 + t) := by
    apply Real.log_le_log (by norm_num : 0 < (8:ℝ))
    linarith
  have hDL : ((20794415409:ℝ)/10000000000) ≤ Real.log (2 + t) := (vlog_lb_m8).trans hDmono
  -- lower square bound
  have hx2ge : (((6:ℝ)/5)) ^ 2 ≤ x ^ 2 := sq_le_of_nonneg (by norm_num : 0 ≤ ((6:ℝ)/5)) hxl
  have ht2ge : ((6:ℝ)) ^ 2 ≤ t ^ 2 := sq_le_of_nonneg (by norm_num : 0 ≤ (6:ℝ)) htl
  have hQ3le : ((936:ℝ)/25) ≤ x ^ 2 + t ^ 2 := by
    have : (((6:ℝ)/5)) ^ 2 + ((6:ℝ)) ^ 2 = ((936:ℝ)/25) := by norm_num
    nlinarith
  have hlogL : ((2028734197772596313:ℝ)/560000000000000000) ≤ Real.log (x ^ 2 + t ^ 2) := by
    exact (vlog_lb_m936_25).trans (Real.log_le_log (by norm_num : 0 < ((936:ℝ)/25)) hQ3le)
  have hLDpos : 0 < ((2028734197772596313:ℝ)/560000000000000000) := by norm_num
  -- arctan bound
  have htovx : t / x ≤ ((15:ℝ)/2) := by
    rw [div_le_iff₀ hxpos]
    have htu_le : (9:ℝ) ≤ ((15:ℝ)/2) * x := by
      calc
        (9:ℝ) = ((15:ℝ)/2) * ((6:ℝ)/5) := by norm_num
        _ ≤ ((15:ℝ)/2) * x := mul_le_mul_of_nonneg_left hxl (by norm_num : 0 ≤ ((15:ℝ)/2))
    nlinarith [htu_le]
  have hAT : Real.arctan (t / x) ≤ ((6880670567:ℝ)/4784062500) := (arctan_mono htovx).trans vatan_ub_m15_2
  have hθsq : (Real.arctan (t / x)) ^ 2 ≤ (((6880670567:ℝ)/4784062500)) ^ 2 := by
    have hθn : 0 ≤ Real.arctan (t / x) := Real.arctan_nonneg.mpr (div_nonneg (le_of_lt htpos) (le_of_lt hxpos))
    have hAn : 0 ≤ ((6880670567:ℝ)/4784062500) := by norm_num
    rw [sq_le_sq]
    rw [abs_of_nonneg hθn, abs_of_nonneg hAn]
    exact hAT
  have hQden : (Real.arctan (t / x)) ^ 2 / Real.log (x ^ 2 + t ^ 2) ≤
      (((6880670567:ℝ)/4784062500)) ^ 2 / (((2028734197772596313:ℝ)/560000000000000000)) := by
    have h1 : (Real.arctan (t / x)) ^ 2 / Real.log (x ^ 2 + t ^ 2) ≤
        (Real.arctan (t / x)) ^ 2 / ((2028734197772596313:ℝ)/560000000000000000) := by
      exact div_le_div_of_nonneg_left (sq_nonneg _) hLDpos (by linarith : ((2028734197772596313:ℝ)/560000000000000000) ≤ Real.log (x ^ 2 + t ^ 2))
    have h2 : (Real.arctan (t / x)) ^ 2 / ((2028734197772596313:ℝ)/560000000000000000) ≤ (((6880670567:ℝ)/4784062500)) ^ 2 / ((2028734197772596313:ℝ)/560000000000000000) := by
      exact div_le_div_of_nonneg_right hθsq (le_of_lt hLDpos)
    exact h1.trans h2
  -- P bound
  have hP : (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) ≤ ((20429:ℝ)/250000) := by
    have hsqrt : Real.sqrt ((936:ℝ)/25) ≤ Real.sqrt (x ^ 2 + t ^ 2) := Real.sqrt_le_sqrt hQ3le
    have hd1 : (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) ≤ (1 : ℝ) / (2 * Real.sqrt ((936:ℝ)/25)) := by
      have hdenpos : 0 < 2 * Real.sqrt ((936:ℝ)/25) := by positivity
      exact div_le_div_of_nonneg_left (by norm_num : 0 ≤ (1 : ℝ)) hdenpos (by nlinarith)
    exact hd1.trans (inv_two_sqrt_le ((936:ℝ)/25) (by norm_num) ((20429:ℝ)/250000) (by norm_num) (by norm_num))
  -- S bound
  have hS : Real.log (x ^ 2 + t ^ 2) / 2 - Real.log (2 + t) ≤ (1 / 2) * ((3111603650802786328825947:ℝ)/703687441776640000000000) - ((20794415409:ℝ)/10000000000) := by
    nlinarith [hlogU, hDL]
  exact combine x t hxpos htpos ((3111603650802786328825947:ℝ)/703687441776640000000000) ((20794415409:ℝ)/10000000000) ((2028734197772596313:ℝ)/560000000000000000) ((6880670567:ℝ)/4784062500) ((20429:ℝ)/250000) hLDpos hS hQden hP (by norm_num)

private lemma box_1_6 (x t : ℝ) (hx1 : 1 ≤ x) (hx2 : x ≤ 8) (ht : 1 ≤ t)
    (hxl : ((6:ℝ)/5) ≤ x) (hxu : x ≤ ((3:ℝ)/2)) (htl : (9:ℝ) ≤ t) (htu : t ≤ (13:ℝ)) :
    Real.log (Real.sqrt (x ^ 2 + t ^ 2)) +
        (Real.arctan (t / x)) ^ 2 / (2 * Real.log (Real.sqrt (x ^ 2 + t ^ 2))) +
        (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) ≤
      Real.log (2 + t) + (3 : ℝ) / 2 := by
  have hxpos : 0 < x := by linarith
  have htpos : 0 < t := by linarith
  have hapos : 0 < x ^ 2 + t ^ 2 := by positivity
  -- upper square bound
  have hx2le : x ^ 2 ≤ (((3:ℝ)/2)) ^ 2 := sq_le_of_nonneg (le_of_lt hxpos) hxu
  have ht2le : t ^ 2 ≤ ((13:ℝ)) ^ 2 := sq_le_of_nonneg (le_of_lt htpos) htu
  have ha_le : x ^ 2 + t ^ 2 ≤ ((685:ℝ)/4) := by
    have : (((3:ℝ)/2)) ^ 2 + ((13:ℝ)) ^ 2 = ((685:ℝ)/4) := by norm_num
    nlinarith
  have hlogU : Real.log (x ^ 2 + t ^ 2) ≤ ((9728311779329375603594654167:ℝ)/1891511843495608320000000000) := by
    exact (Real.log_le_log hapos ha_le).trans vlog_ub_m685_4
  -- log(2+t) lower bound
  have hDmono : Real.log ((11:ℝ)) ≤ Real.log (2 + t) := by
    apply Real.log_le_log (by norm_num : 0 < (11:ℝ))
    linarith
  have hDL : ((22000673184559761:ℝ)/9175040000000000) ≤ Real.log (2 + t) := (vlog_lb_m11).trans hDmono
  -- lower square bound
  have hx2ge : (((6:ℝ)/5)) ^ 2 ≤ x ^ 2 := sq_le_of_nonneg (by norm_num : 0 ≤ ((6:ℝ)/5)) hxl
  have ht2ge : ((9:ℝ)) ^ 2 ≤ t ^ 2 := sq_le_of_nonneg (by norm_num : 0 ≤ (9:ℝ)) htl
  have hQ3le : ((2061:ℝ)/25) ≤ x ^ 2 + t ^ 2 := by
    have : (((6:ℝ)/5)) ^ 2 + ((9:ℝ)) ^ 2 = ((2061:ℝ)/25) := by norm_num
    nlinarith
  have hlogL : ((10611828869600822546167537433:ℝ)/2405181685760000000000000000) ≤ Real.log (x ^ 2 + t ^ 2) := by
    exact (vlog_lb_m2061_25).trans (Real.log_le_log (by norm_num : 0 < ((2061:ℝ)/25)) hQ3le)
  have hLDpos : 0 < ((10611828869600822546167537433:ℝ)/2405181685760000000000000000) := by norm_num
  -- arctan bound
  have htovx : t / x ≤ ((65:ℝ)/6) := by
    rw [div_le_iff₀ hxpos]
    have htu_le : (13:ℝ) ≤ ((65:ℝ)/6) * x := by
      calc
        (13:ℝ) = ((65:ℝ)/6) * ((6:ℝ)/5) := by norm_num
        _ ≤ ((65:ℝ)/6) * x := mul_le_mul_of_nonneg_left hxl (by norm_num : 0 ≤ ((65:ℝ)/6))
    nlinarith [htu_le]
  have hAT : Real.arctan (t / x) ≤ ((202977178351209:ℝ)/137262380937500) := (arctan_mono htovx).trans vatan_ub_m65_6
  have hθsq : (Real.arctan (t / x)) ^ 2 ≤ (((202977178351209:ℝ)/137262380937500)) ^ 2 := by
    have hθn : 0 ≤ Real.arctan (t / x) := Real.arctan_nonneg.mpr (div_nonneg (le_of_lt htpos) (le_of_lt hxpos))
    have hAn : 0 ≤ ((202977178351209:ℝ)/137262380937500) := by norm_num
    rw [sq_le_sq]
    rw [abs_of_nonneg hθn, abs_of_nonneg hAn]
    exact hAT
  have hQden : (Real.arctan (t / x)) ^ 2 / Real.log (x ^ 2 + t ^ 2) ≤
      (((202977178351209:ℝ)/137262380937500)) ^ 2 / (((10611828869600822546167537433:ℝ)/2405181685760000000000000000)) := by
    have h1 : (Real.arctan (t / x)) ^ 2 / Real.log (x ^ 2 + t ^ 2) ≤
        (Real.arctan (t / x)) ^ 2 / ((10611828869600822546167537433:ℝ)/2405181685760000000000000000) := by
      exact div_le_div_of_nonneg_left (sq_nonneg _) hLDpos (by linarith : ((10611828869600822546167537433:ℝ)/2405181685760000000000000000) ≤ Real.log (x ^ 2 + t ^ 2))
    have h2 : (Real.arctan (t / x)) ^ 2 / ((10611828869600822546167537433:ℝ)/2405181685760000000000000000) ≤ (((202977178351209:ℝ)/137262380937500)) ^ 2 / ((10611828869600822546167537433:ℝ)/2405181685760000000000000000) := by
      exact div_le_div_of_nonneg_right hθsq (le_of_lt hLDpos)
    exact h1.trans h2
  -- P bound
  have hP : (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) ≤ ((55069:ℝ)/1000000) := by
    have hsqrt : Real.sqrt ((2061:ℝ)/25) ≤ Real.sqrt (x ^ 2 + t ^ 2) := Real.sqrt_le_sqrt hQ3le
    have hd1 : (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) ≤ (1 : ℝ) / (2 * Real.sqrt ((2061:ℝ)/25)) := by
      have hdenpos : 0 < 2 * Real.sqrt ((2061:ℝ)/25) := by positivity
      exact div_le_div_of_nonneg_left (by norm_num : 0 ≤ (1 : ℝ)) hdenpos (by nlinarith)
    exact hd1.trans (inv_two_sqrt_le ((2061:ℝ)/25) (by norm_num) ((55069:ℝ)/1000000) (by norm_num) (by norm_num))
  -- S bound
  have hS : Real.log (x ^ 2 + t ^ 2) / 2 - Real.log (2 + t) ≤ (1 / 2) * ((9728311779329375603594654167:ℝ)/1891511843495608320000000000) - ((22000673184559761:ℝ)/9175040000000000) := by
    nlinarith [hlogU, hDL]
  exact combine x t hxpos htpos ((9728311779329375603594654167:ℝ)/1891511843495608320000000000) ((22000673184559761:ℝ)/9175040000000000) ((10611828869600822546167537433:ℝ)/2405181685760000000000000000) ((202977178351209:ℝ)/137262380937500) ((55069:ℝ)/1000000) hLDpos hS hQden hP (by norm_num)

private lemma box_1_7 (x t : ℝ) (hx1 : 1 ≤ x) (hx2 : x ≤ 8) (ht : 1 ≤ t)
    (hxl : ((6:ℝ)/5) ≤ x) (hxu : x ≤ ((3:ℝ)/2)) (htl : (13:ℝ) ≤ t) (htu : t ≤ (15:ℝ)) :
    Real.log (Real.sqrt (x ^ 2 + t ^ 2)) +
        (Real.arctan (t / x)) ^ 2 / (2 * Real.log (Real.sqrt (x ^ 2 + t ^ 2))) +
        (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) ≤
      Real.log (2 + t) + (3 : ℝ) / 2 := by
  have hxpos : 0 < x := by linarith
  have htpos : 0 < t := by linarith
  have hapos : 0 < x ^ 2 + t ^ 2 := by positivity
  -- upper square bound
  have hx2le : x ^ 2 ≤ (((3:ℝ)/2)) ^ 2 := sq_le_of_nonneg (le_of_lt hxpos) hxu
  have ht2le : t ^ 2 ≤ ((15:ℝ)) ^ 2 := sq_le_of_nonneg (le_of_lt htpos) htu
  have ha_le : x ^ 2 + t ^ 2 ≤ ((909:ℝ)/4) := by
    have : (((3:ℝ)/2)) ^ 2 + ((15:ℝ)) ^ 2 = ((909:ℝ)/4) := by norm_num
    nlinarith
  have hlogU : Real.log (x ^ 2 + t ^ 2) ≤ ((122183801144633946344360197:ℝ)/22517998136852480000000000) := by
    exact (Real.log_le_log hapos ha_le).trans vlog_ub_m909_4
  -- log(2+t) lower bound
  have hDmono : Real.log ((15:ℝ)) ≤ Real.log (2 + t) := by
    apply Real.log_le_log (by norm_num : 0 < (15:ℝ))
    linarith
  have hDL : ((24846468902980723:ℝ)/9175040000000000) ≤ Real.log (2 + t) := (vlog_lb_m15).trans hDmono
  -- lower square bound
  have hx2ge : (((6:ℝ)/5)) ^ 2 ≤ x ^ 2 := sq_le_of_nonneg (by norm_num : 0 ≤ ((6:ℝ)/5)) hxl
  have ht2ge : ((13:ℝ)) ^ 2 ≤ t ^ 2 := sq_le_of_nonneg (by norm_num : 0 ≤ (13:ℝ)) htl
  have hQ3le : ((4261:ℝ)/25) ≤ x ^ 2 + t ^ 2 := by
    have : (((6:ℝ)/5)) ^ 2 + ((13:ℝ)) ^ 2 = ((4261:ℝ)/25) := by norm_num
    nlinarith
  have hlogL : ((9491508863317597871306254421899:ℝ)/1847179534663680000000000000000) ≤ Real.log (x ^ 2 + t ^ 2) := by
    exact (vlog_lb_m4261_25).trans (Real.log_le_log (by norm_num : 0 < ((4261:ℝ)/25)) hQ3le)
  have hLDpos : 0 < ((9491508863317597871306254421899:ℝ)/1847179534663680000000000000000) := by norm_num
  -- arctan bound
  have htovx : t / x ≤ ((25:ℝ)/2) := by
    rw [div_le_iff₀ hxpos]
    have htu_le : (15:ℝ) ≤ ((25:ℝ)/2) * x := by
      calc
        (15:ℝ) = ((25:ℝ)/2) * ((6:ℝ)/5) := by norm_num
        _ ≤ ((25:ℝ)/2) * x := mul_le_mul_of_nonneg_left hxl (by norm_num : 0 ≤ ((25:ℝ)/2))
    nlinarith [htu_le]
  have hAT : Real.arctan (t / x) ≤ ((764413337411:ℝ)/512695312500) := (arctan_mono htovx).trans vatan_ub_m25_2
  have hθsq : (Real.arctan (t / x)) ^ 2 ≤ (((764413337411:ℝ)/512695312500)) ^ 2 := by
    have hθn : 0 ≤ Real.arctan (t / x) := Real.arctan_nonneg.mpr (div_nonneg (le_of_lt htpos) (le_of_lt hxpos))
    have hAn : 0 ≤ ((764413337411:ℝ)/512695312500) := by norm_num
    rw [sq_le_sq]
    rw [abs_of_nonneg hθn, abs_of_nonneg hAn]
    exact hAT
  have hQden : (Real.arctan (t / x)) ^ 2 / Real.log (x ^ 2 + t ^ 2) ≤
      (((764413337411:ℝ)/512695312500)) ^ 2 / (((9491508863317597871306254421899:ℝ)/1847179534663680000000000000000)) := by
    have h1 : (Real.arctan (t / x)) ^ 2 / Real.log (x ^ 2 + t ^ 2) ≤
        (Real.arctan (t / x)) ^ 2 / ((9491508863317597871306254421899:ℝ)/1847179534663680000000000000000) := by
      exact div_le_div_of_nonneg_left (sq_nonneg _) hLDpos (by linarith : ((9491508863317597871306254421899:ℝ)/1847179534663680000000000000000) ≤ Real.log (x ^ 2 + t ^ 2))
    have h2 : (Real.arctan (t / x)) ^ 2 / ((9491508863317597871306254421899:ℝ)/1847179534663680000000000000000) ≤ (((764413337411:ℝ)/512695312500)) ^ 2 / ((9491508863317597871306254421899:ℝ)/1847179534663680000000000000000) := by
      exact div_le_div_of_nonneg_right hθsq (le_of_lt hLDpos)
    exact h1.trans h2
  -- P bound
  have hP : (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) ≤ ((38299:ℝ)/1000000) := by
    have hsqrt : Real.sqrt ((4261:ℝ)/25) ≤ Real.sqrt (x ^ 2 + t ^ 2) := Real.sqrt_le_sqrt hQ3le
    have hd1 : (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) ≤ (1 : ℝ) / (2 * Real.sqrt ((4261:ℝ)/25)) := by
      have hdenpos : 0 < 2 * Real.sqrt ((4261:ℝ)/25) := by positivity
      exact div_le_div_of_nonneg_left (by norm_num : 0 ≤ (1 : ℝ)) hdenpos (by nlinarith)
    exact hd1.trans (inv_two_sqrt_le ((4261:ℝ)/25) (by norm_num) ((38299:ℝ)/1000000) (by norm_num) (by norm_num))
  -- S bound
  have hS : Real.log (x ^ 2 + t ^ 2) / 2 - Real.log (2 + t) ≤ (1 / 2) * ((122183801144633946344360197:ℝ)/22517998136852480000000000) - ((24846468902980723:ℝ)/9175040000000000) := by
    nlinarith [hlogU, hDL]
  exact combine x t hxpos htpos ((122183801144633946344360197:ℝ)/22517998136852480000000000) ((24846468902980723:ℝ)/9175040000000000) ((9491508863317597871306254421899:ℝ)/1847179534663680000000000000000) ((764413337411:ℝ)/512695312500) ((38299:ℝ)/1000000) hLDpos hS hQden hP (by norm_num)

private lemma box_2_0 (x t : ℝ) (hx1 : 1 ≤ x) (hx2 : x ≤ 8) (ht : 1 ≤ t)
    (hxl : ((3:ℝ)/2) ≤ x) (hxu : x ≤ (2:ℝ)) (htl : (1:ℝ) ≤ t) (htu : t ≤ ((3:ℝ)/2)) :
    Real.log (Real.sqrt (x ^ 2 + t ^ 2)) +
        (Real.arctan (t / x)) ^ 2 / (2 * Real.log (Real.sqrt (x ^ 2 + t ^ 2))) +
        (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) ≤
      Real.log (2 + t) + (3 : ℝ) / 2 := by
  have hxpos : 0 < x := by linarith
  have htpos : 0 < t := by linarith
  have hapos : 0 < x ^ 2 + t ^ 2 := by positivity
  -- upper square bound
  have hx2le : x ^ 2 ≤ ((2:ℝ)) ^ 2 := sq_le_of_nonneg (le_of_lt hxpos) hxu
  have ht2le : t ^ 2 ≤ (((3:ℝ)/2)) ^ 2 := sq_le_of_nonneg (le_of_lt htpos) htu
  have ha_le : x ^ 2 + t ^ 2 ≤ ((25:ℝ)/4) := by
    have : ((2:ℝ)) ^ 2 + (((3:ℝ)/2)) ^ 2 = ((25:ℝ)/4) := by norm_num
    nlinarith
  have hlogU : Real.log (x ^ 2 + t ^ 2) ≤ ((115296323144801719:ℝ)/62914560000000000) := by
    exact (Real.log_le_log hapos ha_le).trans vlog_ub_m25_4
  -- log(2+t) lower bound
  have hDmono : Real.log ((3:ℝ)) ≤ Real.log (2 + t) := by
    apply Real.log_le_log (by norm_num : 0 < (3:ℝ))
    linarith
  have hDL : ((153784745867:ℝ)/140000000000) ≤ Real.log (2 + t) := (vlog_lb_m3).trans hDmono
  -- lower square bound
  have hx2ge : (((3:ℝ)/2)) ^ 2 ≤ x ^ 2 := sq_le_of_nonneg (by norm_num : 0 ≤ ((3:ℝ)/2)) hxl
  have ht2ge : ((1:ℝ)) ^ 2 ≤ t ^ 2 := sq_le_of_nonneg (by norm_num : 0 ≤ (1:ℝ)) htl
  have hQ3le : ((13:ℝ)/4) ≤ x ^ 2 + t ^ 2 := by
    have : (((3:ℝ)/2)) ^ 2 + ((1:ℝ)) ^ 2 = ((13:ℝ)/4) := by norm_num
    nlinarith
  have hlogL : ((10814198157545049:ℝ)/9175040000000000) ≤ Real.log (x ^ 2 + t ^ 2) := by
    exact (vlog_lb_m13_4).trans (Real.log_le_log (by norm_num : 0 < ((13:ℝ)/4)) hQ3le)
  have hLDpos : 0 < ((10814198157545049:ℝ)/9175040000000000) := by norm_num
  -- arctan bound
  have htovx : t / x ≤ (1:ℝ) := by
    rw [div_le_iff₀ hxpos]
    have htu_le : ((3:ℝ)/2) ≤ (1:ℝ) * x := by
      calc
        ((3:ℝ)/2) = (1:ℝ) * ((3:ℝ)/2) := by norm_num
        _ ≤ (1:ℝ) * x := mul_le_mul_of_nonneg_left hxl (by norm_num : 0 ≤ (1:ℝ))
    nlinarith [htu_le]
  have hAT : Real.arctan (t / x) ≤ ((263:ℝ)/315) := (arctan_mono htovx).trans vatan_ub_m1
  have hθsq : (Real.arctan (t / x)) ^ 2 ≤ (((263:ℝ)/315)) ^ 2 := by
    have hθn : 0 ≤ Real.arctan (t / x) := Real.arctan_nonneg.mpr (div_nonneg (le_of_lt htpos) (le_of_lt hxpos))
    have hAn : 0 ≤ ((263:ℝ)/315) := by norm_num
    rw [sq_le_sq]
    rw [abs_of_nonneg hθn, abs_of_nonneg hAn]
    exact hAT
  have hQden : (Real.arctan (t / x)) ^ 2 / Real.log (x ^ 2 + t ^ 2) ≤
      (((263:ℝ)/315)) ^ 2 / (((10814198157545049:ℝ)/9175040000000000)) := by
    have h1 : (Real.arctan (t / x)) ^ 2 / Real.log (x ^ 2 + t ^ 2) ≤
        (Real.arctan (t / x)) ^ 2 / ((10814198157545049:ℝ)/9175040000000000) := by
      exact div_le_div_of_nonneg_left (sq_nonneg _) hLDpos (by linarith : ((10814198157545049:ℝ)/9175040000000000) ≤ Real.log (x ^ 2 + t ^ 2))
    have h2 : (Real.arctan (t / x)) ^ 2 / ((10814198157545049:ℝ)/9175040000000000) ≤ (((263:ℝ)/315)) ^ 2 / ((10814198157545049:ℝ)/9175040000000000) := by
      exact div_le_div_of_nonneg_right hθsq (le_of_lt hLDpos)
    exact h1.trans h2
  -- P bound
  have hP : (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) ≤ ((277351:ℝ)/1000000) := by
    have hsqrt : Real.sqrt ((13:ℝ)/4) ≤ Real.sqrt (x ^ 2 + t ^ 2) := Real.sqrt_le_sqrt hQ3le
    have hd1 : (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) ≤ (1 : ℝ) / (2 * Real.sqrt ((13:ℝ)/4)) := by
      have hdenpos : 0 < 2 * Real.sqrt ((13:ℝ)/4) := by positivity
      exact div_le_div_of_nonneg_left (by norm_num : 0 ≤ (1 : ℝ)) hdenpos (by nlinarith)
    exact hd1.trans (inv_two_sqrt_le ((13:ℝ)/4) (by norm_num) ((277351:ℝ)/1000000) (by norm_num) (by norm_num))
  -- S bound
  have hS : Real.log (x ^ 2 + t ^ 2) / 2 - Real.log (2 + t) ≤ (1 / 2) * ((115296323144801719:ℝ)/62914560000000000) - ((153784745867:ℝ)/140000000000) := by
    nlinarith [hlogU, hDL]
  exact combine x t hxpos htpos ((115296323144801719:ℝ)/62914560000000000) ((153784745867:ℝ)/140000000000) ((10814198157545049:ℝ)/9175040000000000) ((263:ℝ)/315) ((277351:ℝ)/1000000) hLDpos hS hQden hP (by norm_num)

private lemma box_2_1 (x t : ℝ) (hx1 : 1 ≤ x) (hx2 : x ≤ 8) (ht : 1 ≤ t)
    (hxl : ((3:ℝ)/2) ≤ x) (hxu : x ≤ (2:ℝ)) (htl : ((3:ℝ)/2) ≤ t) (htu : t ≤ (2:ℝ)) :
    Real.log (Real.sqrt (x ^ 2 + t ^ 2)) +
        (Real.arctan (t / x)) ^ 2 / (2 * Real.log (Real.sqrt (x ^ 2 + t ^ 2))) +
        (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) ≤
      Real.log (2 + t) + (3 : ℝ) / 2 := by
  have hxpos : 0 < x := by linarith
  have htpos : 0 < t := by linarith
  have hapos : 0 < x ^ 2 + t ^ 2 := by positivity
  -- upper square bound
  have hx2le : x ^ 2 ≤ ((2:ℝ)) ^ 2 := sq_le_of_nonneg (le_of_lt hxpos) hxu
  have ht2le : t ^ 2 ≤ ((2:ℝ)) ^ 2 := sq_le_of_nonneg (le_of_lt htpos) htu
  have ha_le : x ^ 2 + t ^ 2 ≤ (8:ℝ) := by
    have : ((2:ℝ)) ^ 2 + ((2:ℝ)) ^ 2 = (8:ℝ) := by norm_num
    nlinarith
  have hlogU : Real.log (x ^ 2 + t ^ 2) ≤ ((324912741:ℝ)/156250000) := by
    exact (Real.log_le_log hapos ha_le).trans vlog_ub_m8
  -- log(2+t) lower bound
  have hDmono : Real.log (((7:ℝ)/2)) ≤ Real.log (2 + t) := by
    apply Real.log_le_log (by norm_num : 0 < ((7:ℝ)/2))
    linarith
  have hDL : ((269394135787799:ℝ)/215040000000000) ≤ Real.log (2 + t) := (vlog_lb_m7_2).trans hDmono
  -- lower square bound
  have hx2ge : (((3:ℝ)/2)) ^ 2 ≤ x ^ 2 := sq_le_of_nonneg (by norm_num : 0 ≤ ((3:ℝ)/2)) hxl
  have ht2ge : (((3:ℝ)/2)) ^ 2 ≤ t ^ 2 := sq_le_of_nonneg (by norm_num : 0 ≤ ((3:ℝ)/2)) htl
  have hQ3le : ((9:ℝ)/2) ≤ x ^ 2 + t ^ 2 := by
    have : (((3:ℝ)/2)) ^ 2 + (((3:ℝ)/2)) ^ 2 = ((9:ℝ)/2) := by norm_num
    nlinarith
  have hlogL : ((13799970266920049:ℝ)/9175040000000000) ≤ Real.log (x ^ 2 + t ^ 2) := by
    exact (vlog_lb_m9_2).trans (Real.log_le_log (by norm_num : 0 < ((9:ℝ)/2)) hQ3le)
  have hLDpos : 0 < ((13799970266920049:ℝ)/9175040000000000) := by norm_num
  -- arctan bound
  have htovx : t / x ≤ ((4:ℝ)/3) := by
    rw [div_le_iff₀ hxpos]
    have htu_le : (2:ℝ) ≤ ((4:ℝ)/3) * x := by
      calc
        (2:ℝ) = ((4:ℝ)/3) * ((3:ℝ)/2) := by norm_num
        _ ≤ ((4:ℝ)/3) * x := mul_le_mul_of_nonneg_left hxl (by norm_num : 0 ≤ ((4:ℝ)/3))
    nlinarith [htu_le]
  have hAT : Real.arctan (t / x) ≤ ((66879819:ℝ)/71680000) := (arctan_mono htovx).trans vatan_ub_m4_3
  have hθsq : (Real.arctan (t / x)) ^ 2 ≤ (((66879819:ℝ)/71680000)) ^ 2 := by
    have hθn : 0 ≤ Real.arctan (t / x) := Real.arctan_nonneg.mpr (div_nonneg (le_of_lt htpos) (le_of_lt hxpos))
    have hAn : 0 ≤ ((66879819:ℝ)/71680000) := by norm_num
    rw [sq_le_sq]
    rw [abs_of_nonneg hθn, abs_of_nonneg hAn]
    exact hAT
  have hQden : (Real.arctan (t / x)) ^ 2 / Real.log (x ^ 2 + t ^ 2) ≤
      (((66879819:ℝ)/71680000)) ^ 2 / (((13799970266920049:ℝ)/9175040000000000)) := by
    have h1 : (Real.arctan (t / x)) ^ 2 / Real.log (x ^ 2 + t ^ 2) ≤
        (Real.arctan (t / x)) ^ 2 / ((13799970266920049:ℝ)/9175040000000000) := by
      exact div_le_div_of_nonneg_left (sq_nonneg _) hLDpos (by linarith : ((13799970266920049:ℝ)/9175040000000000) ≤ Real.log (x ^ 2 + t ^ 2))
    have h2 : (Real.arctan (t / x)) ^ 2 / ((13799970266920049:ℝ)/9175040000000000) ≤ (((66879819:ℝ)/71680000)) ^ 2 / ((13799970266920049:ℝ)/9175040000000000) := by
      exact div_le_div_of_nonneg_right hθsq (le_of_lt hLDpos)
    exact h1.trans h2
  -- P bound
  have hP : (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) ≤ ((235703:ℝ)/1000000) := by
    have hsqrt : Real.sqrt ((9:ℝ)/2) ≤ Real.sqrt (x ^ 2 + t ^ 2) := Real.sqrt_le_sqrt hQ3le
    have hd1 : (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) ≤ (1 : ℝ) / (2 * Real.sqrt ((9:ℝ)/2)) := by
      have hdenpos : 0 < 2 * Real.sqrt ((9:ℝ)/2) := by positivity
      exact div_le_div_of_nonneg_left (by norm_num : 0 ≤ (1 : ℝ)) hdenpos (by nlinarith)
    exact hd1.trans (inv_two_sqrt_le ((9:ℝ)/2) (by norm_num) ((235703:ℝ)/1000000) (by norm_num) (by norm_num))
  -- S bound
  have hS : Real.log (x ^ 2 + t ^ 2) / 2 - Real.log (2 + t) ≤ (1 / 2) * ((324912741:ℝ)/156250000) - ((269394135787799:ℝ)/215040000000000) := by
    nlinarith [hlogU, hDL]
  exact combine x t hxpos htpos ((324912741:ℝ)/156250000) ((269394135787799:ℝ)/215040000000000) ((13799970266920049:ℝ)/9175040000000000) ((66879819:ℝ)/71680000) ((235703:ℝ)/1000000) hLDpos hS hQden hP (by norm_num)

private lemma box_2_2 (x t : ℝ) (hx1 : 1 ≤ x) (hx2 : x ≤ 8) (ht : 1 ≤ t)
    (hxl : ((3:ℝ)/2) ≤ x) (hxu : x ≤ (2:ℝ)) (htl : (2:ℝ) ≤ t) (htu : t ≤ (3:ℝ)) :
    Real.log (Real.sqrt (x ^ 2 + t ^ 2)) +
        (Real.arctan (t / x)) ^ 2 / (2 * Real.log (Real.sqrt (x ^ 2 + t ^ 2))) +
        (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) ≤
      Real.log (2 + t) + (3 : ℝ) / 2 := by
  have hxpos : 0 < x := by linarith
  have htpos : 0 < t := by linarith
  have hapos : 0 < x ^ 2 + t ^ 2 := by positivity
  -- upper square bound
  have hx2le : x ^ 2 ≤ ((2:ℝ)) ^ 2 := sq_le_of_nonneg (le_of_lt hxpos) hxu
  have ht2le : t ^ 2 ≤ ((3:ℝ)) ^ 2 := sq_le_of_nonneg (le_of_lt htpos) htu
  have ha_le : x ^ 2 + t ^ 2 ≤ (13:ℝ) := by
    have : ((2:ℝ)) ^ 2 + ((3:ℝ)) ^ 2 = (13:ℝ) := by norm_num
    nlinarith
  have hlogU : Real.log (x ^ 2 + t ^ 2) ≤ ((840483062271301:ℝ)/327680000000000) := by
    exact (Real.log_le_log hapos ha_le).trans vlog_ub_m13
  -- log(2+t) lower bound
  have hDmono : Real.log ((4:ℝ)) ≤ Real.log (2 + t) := by
    apply Real.log_le_log (by norm_num : 0 < (4:ℝ))
    linarith
  have hDL : ((6931471803:ℝ)/5000000000) ≤ Real.log (2 + t) := (vlog_lb_m4).trans hDmono
  -- lower square bound
  have hx2ge : (((3:ℝ)/2)) ^ 2 ≤ x ^ 2 := sq_le_of_nonneg (by norm_num : 0 ≤ ((3:ℝ)/2)) hxl
  have ht2ge : ((2:ℝ)) ^ 2 ≤ t ^ 2 := sq_le_of_nonneg (by norm_num : 0 ≤ (2:ℝ)) htl
  have hQ3le : ((25:ℝ)/4) ≤ x ^ 2 + t ^ 2 := by
    have : (((3:ℝ)/2)) ^ 2 + ((2:ℝ)) ^ 2 = ((25:ℝ)/4) := by norm_num
    nlinarith
  have hlogL : ((922367137655392157:ℝ)/503316480000000000) ≤ Real.log (x ^ 2 + t ^ 2) := by
    exact (vlog_lb_m25_4).trans (Real.log_le_log (by norm_num : 0 < ((25:ℝ)/4)) hQ3le)
  have hLDpos : 0 < ((922367137655392157:ℝ)/503316480000000000) := by norm_num
  -- arctan bound
  have htovx : t / x ≤ (2:ℝ) := by
    rw [div_le_iff₀ hxpos]
    have htu_le : (3:ℝ) ≤ (2:ℝ) * x := by
      calc
        (3:ℝ) = (2:ℝ) * ((3:ℝ)/2) := by norm_num
        _ ≤ (2:ℝ) * x := mul_le_mul_of_nonneg_left hxl (by norm_num : 0 ≤ (2:ℝ))
    nlinarith [htu_le]
  have hAT : Real.arctan (t / x) ≤ ((1860319:ℝ)/1680000) := (arctan_mono htovx).trans vatan_ub_m2
  have hθsq : (Real.arctan (t / x)) ^ 2 ≤ (((1860319:ℝ)/1680000)) ^ 2 := by
    have hθn : 0 ≤ Real.arctan (t / x) := Real.arctan_nonneg.mpr (div_nonneg (le_of_lt htpos) (le_of_lt hxpos))
    have hAn : 0 ≤ ((1860319:ℝ)/1680000) := by norm_num
    rw [sq_le_sq]
    rw [abs_of_nonneg hθn, abs_of_nonneg hAn]
    exact hAT
  have hQden : (Real.arctan (t / x)) ^ 2 / Real.log (x ^ 2 + t ^ 2) ≤
      (((1860319:ℝ)/1680000)) ^ 2 / (((922367137655392157:ℝ)/503316480000000000)) := by
    have h1 : (Real.arctan (t / x)) ^ 2 / Real.log (x ^ 2 + t ^ 2) ≤
        (Real.arctan (t / x)) ^ 2 / ((922367137655392157:ℝ)/503316480000000000) := by
      exact div_le_div_of_nonneg_left (sq_nonneg _) hLDpos (by linarith : ((922367137655392157:ℝ)/503316480000000000) ≤ Real.log (x ^ 2 + t ^ 2))
    have h2 : (Real.arctan (t / x)) ^ 2 / ((922367137655392157:ℝ)/503316480000000000) ≤ (((1860319:ℝ)/1680000)) ^ 2 / ((922367137655392157:ℝ)/503316480000000000) := by
      exact div_le_div_of_nonneg_right hθsq (le_of_lt hLDpos)
    exact h1.trans h2
  -- P bound
  have hP : (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) ≤ ((200001:ℝ)/1000000) := by
    have hsqrt : Real.sqrt ((25:ℝ)/4) ≤ Real.sqrt (x ^ 2 + t ^ 2) := Real.sqrt_le_sqrt hQ3le
    have hd1 : (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) ≤ (1 : ℝ) / (2 * Real.sqrt ((25:ℝ)/4)) := by
      have hdenpos : 0 < 2 * Real.sqrt ((25:ℝ)/4) := by positivity
      exact div_le_div_of_nonneg_left (by norm_num : 0 ≤ (1 : ℝ)) hdenpos (by nlinarith)
    exact hd1.trans (inv_two_sqrt_le ((25:ℝ)/4) (by norm_num) ((200001:ℝ)/1000000) (by norm_num) (by norm_num))
  -- S bound
  have hS : Real.log (x ^ 2 + t ^ 2) / 2 - Real.log (2 + t) ≤ (1 / 2) * ((840483062271301:ℝ)/327680000000000) - ((6931471803:ℝ)/5000000000) := by
    nlinarith [hlogU, hDL]
  exact combine x t hxpos htpos ((840483062271301:ℝ)/327680000000000) ((6931471803:ℝ)/5000000000) ((922367137655392157:ℝ)/503316480000000000) ((1860319:ℝ)/1680000) ((200001:ℝ)/1000000) hLDpos hS hQden hP (by norm_num)

private lemma box_2_3 (x t : ℝ) (hx1 : 1 ≤ x) (hx2 : x ≤ 8) (ht : 1 ≤ t)
    (hxl : ((3:ℝ)/2) ≤ x) (hxu : x ≤ (2:ℝ)) (htl : (3:ℝ) ≤ t) (htu : t ≤ (4:ℝ)) :
    Real.log (Real.sqrt (x ^ 2 + t ^ 2)) +
        (Real.arctan (t / x)) ^ 2 / (2 * Real.log (Real.sqrt (x ^ 2 + t ^ 2))) +
        (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) ≤
      Real.log (2 + t) + (3 : ℝ) / 2 := by
  have hxpos : 0 < x := by linarith
  have htpos : 0 < t := by linarith
  have hapos : 0 < x ^ 2 + t ^ 2 := by positivity
  -- upper square bound
  have hx2le : x ^ 2 ≤ ((2:ℝ)) ^ 2 := sq_le_of_nonneg (le_of_lt hxpos) hxu
  have ht2le : t ^ 2 ≤ ((4:ℝ)) ^ 2 := sq_le_of_nonneg (le_of_lt htpos) htu
  have ha_le : x ^ 2 + t ^ 2 ≤ (20:ℝ) := by
    have : ((2:ℝ)) ^ 2 + ((4:ℝ)) ^ 2 = (20:ℝ) := by norm_num
    nlinarith
  have hlogU : Real.log (x ^ 2 + t ^ 2) ≤ ((10065665688077:ℝ)/3360000000000) := by
    exact (Real.log_le_log hapos ha_le).trans vlog_ub_m20
  -- log(2+t) lower bound
  have hDmono : Real.log ((5:ℝ)) ≤ Real.log (2 + t) := by
    apply Real.log_le_log (by norm_num : 0 < (5:ℝ))
    linarith
  have hDL : ((173046727073587:ℝ)/107520000000000) ≤ Real.log (2 + t) := (vlog_lb_m5).trans hDmono
  -- lower square bound
  have hx2ge : (((3:ℝ)/2)) ^ 2 ≤ x ^ 2 := sq_le_of_nonneg (by norm_num : 0 ≤ ((3:ℝ)/2)) hxl
  have ht2ge : ((3:ℝ)) ^ 2 ≤ t ^ 2 := sq_le_of_nonneg (by norm_num : 0 ≤ (3:ℝ)) htl
  have hQ3le : ((45:ℝ)/4) ≤ x ^ 2 + t ^ 2 := by
    have : (((3:ℝ)/2)) ^ 2 + ((3:ℝ)) ^ 2 = ((45:ℝ)/4) := by norm_num
    nlinarith
  have hlogL : ((1455341517017552637521:ℝ)/601295421440000000000) ≤ Real.log (x ^ 2 + t ^ 2) := by
    exact (vlog_lb_m45_4).trans (Real.log_le_log (by norm_num : 0 < ((45:ℝ)/4)) hQ3le)
  have hLDpos : 0 < ((1455341517017552637521:ℝ)/601295421440000000000) := by norm_num
  -- arctan bound
  have htovx : t / x ≤ ((8:ℝ)/3) := by
    rw [div_le_iff₀ hxpos]
    have htu_le : (4:ℝ) ≤ ((8:ℝ)/3) * x := by
      calc
        (4:ℝ) = ((8:ℝ)/3) * ((3:ℝ)/2) := by norm_num
        _ ≤ ((8:ℝ)/3) * x := mul_le_mul_of_nonneg_left hxl (by norm_num : 0 ≤ ((8:ℝ)/3))
    nlinarith [htu_le]
  have hAT : Real.arctan (t / x) ≤ ((11120551707:ℝ)/9175040000) := (arctan_mono htovx).trans vatan_ub_m8_3
  have hθsq : (Real.arctan (t / x)) ^ 2 ≤ (((11120551707:ℝ)/9175040000)) ^ 2 := by
    have hθn : 0 ≤ Real.arctan (t / x) := Real.arctan_nonneg.mpr (div_nonneg (le_of_lt htpos) (le_of_lt hxpos))
    have hAn : 0 ≤ ((11120551707:ℝ)/9175040000) := by norm_num
    rw [sq_le_sq]
    rw [abs_of_nonneg hθn, abs_of_nonneg hAn]
    exact hAT
  have hQden : (Real.arctan (t / x)) ^ 2 / Real.log (x ^ 2 + t ^ 2) ≤
      (((11120551707:ℝ)/9175040000)) ^ 2 / (((1455341517017552637521:ℝ)/601295421440000000000)) := by
    have h1 : (Real.arctan (t / x)) ^ 2 / Real.log (x ^ 2 + t ^ 2) ≤
        (Real.arctan (t / x)) ^ 2 / ((1455341517017552637521:ℝ)/601295421440000000000) := by
      exact div_le_div_of_nonneg_left (sq_nonneg _) hLDpos (by linarith : ((1455341517017552637521:ℝ)/601295421440000000000) ≤ Real.log (x ^ 2 + t ^ 2))
    have h2 : (Real.arctan (t / x)) ^ 2 / ((1455341517017552637521:ℝ)/601295421440000000000) ≤ (((11120551707:ℝ)/9175040000)) ^ 2 / ((1455341517017552637521:ℝ)/601295421440000000000) := by
      exact div_le_div_of_nonneg_right hθsq (le_of_lt hLDpos)
    exact h1.trans h2
  -- P bound
  have hP : (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) ≤ ((9317:ℝ)/62500) := by
    have hsqrt : Real.sqrt ((45:ℝ)/4) ≤ Real.sqrt (x ^ 2 + t ^ 2) := Real.sqrt_le_sqrt hQ3le
    have hd1 : (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) ≤ (1 : ℝ) / (2 * Real.sqrt ((45:ℝ)/4)) := by
      have hdenpos : 0 < 2 * Real.sqrt ((45:ℝ)/4) := by positivity
      exact div_le_div_of_nonneg_left (by norm_num : 0 ≤ (1 : ℝ)) hdenpos (by nlinarith)
    exact hd1.trans (inv_two_sqrt_le ((45:ℝ)/4) (by norm_num) ((9317:ℝ)/62500) (by norm_num) (by norm_num))
  -- S bound
  have hS : Real.log (x ^ 2 + t ^ 2) / 2 - Real.log (2 + t) ≤ (1 / 2) * ((10065665688077:ℝ)/3360000000000) - ((173046727073587:ℝ)/107520000000000) := by
    nlinarith [hlogU, hDL]
  exact combine x t hxpos htpos ((10065665688077:ℝ)/3360000000000) ((173046727073587:ℝ)/107520000000000) ((1455341517017552637521:ℝ)/601295421440000000000) ((11120551707:ℝ)/9175040000) ((9317:ℝ)/62500) hLDpos hS hQden hP (by norm_num)

private lemma box_2_4 (x t : ℝ) (hx1 : 1 ≤ x) (hx2 : x ≤ 8) (ht : 1 ≤ t)
    (hxl : ((3:ℝ)/2) ≤ x) (hxu : x ≤ (2:ℝ)) (htl : (4:ℝ) ≤ t) (htu : t ≤ (6:ℝ)) :
    Real.log (Real.sqrt (x ^ 2 + t ^ 2)) +
        (Real.arctan (t / x)) ^ 2 / (2 * Real.log (Real.sqrt (x ^ 2 + t ^ 2))) +
        (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) ≤
      Real.log (2 + t) + (3 : ℝ) / 2 := by
  have hxpos : 0 < x := by linarith
  have htpos : 0 < t := by linarith
  have hapos : 0 < x ^ 2 + t ^ 2 := by positivity
  -- upper square bound
  have hx2le : x ^ 2 ≤ ((2:ℝ)) ^ 2 := sq_le_of_nonneg (le_of_lt hxpos) hxu
  have ht2le : t ^ 2 ≤ ((6:ℝ)) ^ 2 := sq_le_of_nonneg (le_of_lt htpos) htu
  have ha_le : x ^ 2 + t ^ 2 ≤ (40:ℝ) := by
    have : ((2:ℝ)) ^ 2 + ((6:ℝ)) ^ 2 = (40:ℝ) := by norm_num
    nlinarith
  have hlogU : Real.log (x ^ 2 + t ^ 2) ≤ ((2478928043113:ℝ)/672000000000) := by
    exact (Real.log_le_log hapos ha_le).trans vlog_ub_m40
  -- log(2+t) lower bound
  have hDmono : Real.log ((6:ℝ)) ≤ Real.log (2 + t) := by
    apply Real.log_le_log (by norm_num : 0 < (6:ℝ))
    linarith
  have hDL : ((250825351109:ℝ)/140000000000) ≤ Real.log (2 + t) := (vlog_lb_m6).trans hDmono
  -- lower square bound
  have hx2ge : (((3:ℝ)/2)) ^ 2 ≤ x ^ 2 := sq_le_of_nonneg (by norm_num : 0 ≤ ((3:ℝ)/2)) hxl
  have ht2ge : ((4:ℝ)) ^ 2 ≤ t ^ 2 := sq_le_of_nonneg (by norm_num : 0 ≤ (4:ℝ)) htl
  have hQ3le : ((73:ℝ)/4) ≤ x ^ 2 + t ^ 2 := by
    have : (((3:ℝ)/2)) ^ 2 + ((4:ℝ)) ^ 2 = ((73:ℝ)/4) := by norm_num
    nlinarith
  have hlogL : ((447042857939524690247793:ℝ)/153931627888640000000000) ≤ Real.log (x ^ 2 + t ^ 2) := by
    exact (vlog_lb_m73_4).trans (Real.log_le_log (by norm_num : 0 < ((73:ℝ)/4)) hQ3le)
  have hLDpos : 0 < ((447042857939524690247793:ℝ)/153931627888640000000000) := by norm_num
  -- arctan bound
  have htovx : t / x ≤ (4:ℝ) := by
    rw [div_le_iff₀ hxpos]
    have htu_le : (6:ℝ) ≤ (4:ℝ) * x := by
      calc
        (6:ℝ) = (4:ℝ) * ((3:ℝ)/2) := by norm_num
        _ ≤ (4:ℝ) * x := mul_le_mul_of_nonneg_left hxl (by norm_num : 0 ≤ (4:ℝ))
    nlinarith [htu_le]
  have hAT : Real.arctan (t / x) ≤ ((285104707:ℝ)/215040000) := (arctan_mono htovx).trans vatan_ub_m4
  have hθsq : (Real.arctan (t / x)) ^ 2 ≤ (((285104707:ℝ)/215040000)) ^ 2 := by
    have hθn : 0 ≤ Real.arctan (t / x) := Real.arctan_nonneg.mpr (div_nonneg (le_of_lt htpos) (le_of_lt hxpos))
    have hAn : 0 ≤ ((285104707:ℝ)/215040000) := by norm_num
    rw [sq_le_sq]
    rw [abs_of_nonneg hθn, abs_of_nonneg hAn]
    exact hAT
  have hQden : (Real.arctan (t / x)) ^ 2 / Real.log (x ^ 2 + t ^ 2) ≤
      (((285104707:ℝ)/215040000)) ^ 2 / (((447042857939524690247793:ℝ)/153931627888640000000000)) := by
    have h1 : (Real.arctan (t / x)) ^ 2 / Real.log (x ^ 2 + t ^ 2) ≤
        (Real.arctan (t / x)) ^ 2 / ((447042857939524690247793:ℝ)/153931627888640000000000) := by
      exact div_le_div_of_nonneg_left (sq_nonneg _) hLDpos (by linarith : ((447042857939524690247793:ℝ)/153931627888640000000000) ≤ Real.log (x ^ 2 + t ^ 2))
    have h2 : (Real.arctan (t / x)) ^ 2 / ((447042857939524690247793:ℝ)/153931627888640000000000) ≤ (((285104707:ℝ)/215040000)) ^ 2 / ((447042857939524690247793:ℝ)/153931627888640000000000) := by
      exact div_le_div_of_nonneg_right hθsq (le_of_lt hLDpos)
    exact h1.trans h2
  -- P bound
  have hP : (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) ≤ ((58521:ℝ)/500000) := by
    have hsqrt : Real.sqrt ((73:ℝ)/4) ≤ Real.sqrt (x ^ 2 + t ^ 2) := Real.sqrt_le_sqrt hQ3le
    have hd1 : (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) ≤ (1 : ℝ) / (2 * Real.sqrt ((73:ℝ)/4)) := by
      have hdenpos : 0 < 2 * Real.sqrt ((73:ℝ)/4) := by positivity
      exact div_le_div_of_nonneg_left (by norm_num : 0 ≤ (1 : ℝ)) hdenpos (by nlinarith)
    exact hd1.trans (inv_two_sqrt_le ((73:ℝ)/4) (by norm_num) ((58521:ℝ)/500000) (by norm_num) (by norm_num))
  -- S bound
  have hS : Real.log (x ^ 2 + t ^ 2) / 2 - Real.log (2 + t) ≤ (1 / 2) * ((2478928043113:ℝ)/672000000000) - ((250825351109:ℝ)/140000000000) := by
    nlinarith [hlogU, hDL]
  exact combine x t hxpos htpos ((2478928043113:ℝ)/672000000000) ((250825351109:ℝ)/140000000000) ((447042857939524690247793:ℝ)/153931627888640000000000) ((285104707:ℝ)/215040000) ((58521:ℝ)/500000) hLDpos hS hQden hP (by norm_num)

private lemma box_2_5 (x t : ℝ) (hx1 : 1 ≤ x) (hx2 : x ≤ 8) (ht : 1 ≤ t)
    (hxl : ((3:ℝ)/2) ≤ x) (hxu : x ≤ (2:ℝ)) (htl : (6:ℝ) ≤ t) (htu : t ≤ (9:ℝ)) :
    Real.log (Real.sqrt (x ^ 2 + t ^ 2)) +
        (Real.arctan (t / x)) ^ 2 / (2 * Real.log (Real.sqrt (x ^ 2 + t ^ 2))) +
        (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) ≤
      Real.log (2 + t) + (3 : ℝ) / 2 := by
  have hxpos : 0 < x := by linarith
  have htpos : 0 < t := by linarith
  have hapos : 0 < x ^ 2 + t ^ 2 := by positivity
  -- upper square bound
  have hx2le : x ^ 2 ≤ ((2:ℝ)) ^ 2 := sq_le_of_nonneg (le_of_lt hxpos) hxu
  have ht2le : t ^ 2 ≤ ((9:ℝ)) ^ 2 := sq_le_of_nonneg (le_of_lt htpos) htu
  have ha_le : x ^ 2 + t ^ 2 ≤ (85:ℝ) := by
    have : ((2:ℝ)) ^ 2 + ((9:ℝ)) ^ 2 = (85:ℝ) := by norm_num
    nlinarith
  have hlogU : Real.log (x ^ 2 + t ^ 2) ≤ ((190810977487424618883:ℝ)/42949672960000000000) := by
    exact (Real.log_le_log hapos ha_le).trans vlog_ub_m85
  -- log(2+t) lower bound
  have hDmono : Real.log ((8:ℝ)) ≤ Real.log (2 + t) := by
    apply Real.log_le_log (by norm_num : 0 < (8:ℝ))
    linarith
  have hDL : ((20794415409:ℝ)/10000000000) ≤ Real.log (2 + t) := (vlog_lb_m8).trans hDmono
  -- lower square bound
  have hx2ge : (((3:ℝ)/2)) ^ 2 ≤ x ^ 2 := sq_le_of_nonneg (by norm_num : 0 ≤ ((3:ℝ)/2)) hxl
  have ht2ge : ((6:ℝ)) ^ 2 ≤ t ^ 2 := sq_le_of_nonneg (by norm_num : 0 ≤ (6:ℝ)) htl
  have hQ3le : ((153:ℝ)/4) ≤ x ^ 2 + t ^ 2 := by
    have : (((3:ℝ)/2)) ^ 2 + ((6:ℝ)) ^ 2 = ((153:ℝ)/4) := by norm_num
    nlinarith
  have hlogL : ((28720585946874995412186877:ℝ)/7881299347898368000000000) ≤ Real.log (x ^ 2 + t ^ 2) := by
    exact (vlog_lb_m153_4).trans (Real.log_le_log (by norm_num : 0 < ((153:ℝ)/4)) hQ3le)
  have hLDpos : 0 < ((28720585946874995412186877:ℝ)/7881299347898368000000000) := by norm_num
  -- arctan bound
  have htovx : t / x ≤ (6:ℝ) := by
    rw [div_le_iff₀ hxpos]
    have htu_le : (9:ℝ) ≤ (6:ℝ) * x := by
      calc
        (9:ℝ) = (6:ℝ) * ((3:ℝ)/2) := by norm_num
        _ ≤ (6:ℝ) * x := mul_le_mul_of_nonneg_left hxl (by norm_num : 0 ≤ (6:ℝ))
    nlinarith [htu_le]
  have hAT : Real.arctan (t / x) ≤ ((1721529301:ℝ)/1224720000) := (arctan_mono htovx).trans vatan_ub_m6
  have hθsq : (Real.arctan (t / x)) ^ 2 ≤ (((1721529301:ℝ)/1224720000)) ^ 2 := by
    have hθn : 0 ≤ Real.arctan (t / x) := Real.arctan_nonneg.mpr (div_nonneg (le_of_lt htpos) (le_of_lt hxpos))
    have hAn : 0 ≤ ((1721529301:ℝ)/1224720000) := by norm_num
    rw [sq_le_sq]
    rw [abs_of_nonneg hθn, abs_of_nonneg hAn]
    exact hAT
  have hQden : (Real.arctan (t / x)) ^ 2 / Real.log (x ^ 2 + t ^ 2) ≤
      (((1721529301:ℝ)/1224720000)) ^ 2 / (((28720585946874995412186877:ℝ)/7881299347898368000000000)) := by
    have h1 : (Real.arctan (t / x)) ^ 2 / Real.log (x ^ 2 + t ^ 2) ≤
        (Real.arctan (t / x)) ^ 2 / ((28720585946874995412186877:ℝ)/7881299347898368000000000) := by
      exact div_le_div_of_nonneg_left (sq_nonneg _) hLDpos (by linarith : ((28720585946874995412186877:ℝ)/7881299347898368000000000) ≤ Real.log (x ^ 2 + t ^ 2))
    have h2 : (Real.arctan (t / x)) ^ 2 / ((28720585946874995412186877:ℝ)/7881299347898368000000000) ≤ (((1721529301:ℝ)/1224720000)) ^ 2 / ((28720585946874995412186877:ℝ)/7881299347898368000000000) := by
      exact div_le_div_of_nonneg_right hθsq (le_of_lt hLDpos)
    exact h1.trans h2
  -- P bound
  have hP : (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) ≤ ((40423:ℝ)/500000) := by
    have hsqrt : Real.sqrt ((153:ℝ)/4) ≤ Real.sqrt (x ^ 2 + t ^ 2) := Real.sqrt_le_sqrt hQ3le
    have hd1 : (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) ≤ (1 : ℝ) / (2 * Real.sqrt ((153:ℝ)/4)) := by
      have hdenpos : 0 < 2 * Real.sqrt ((153:ℝ)/4) := by positivity
      exact div_le_div_of_nonneg_left (by norm_num : 0 ≤ (1 : ℝ)) hdenpos (by nlinarith)
    exact hd1.trans (inv_two_sqrt_le ((153:ℝ)/4) (by norm_num) ((40423:ℝ)/500000) (by norm_num) (by norm_num))
  -- S bound
  have hS : Real.log (x ^ 2 + t ^ 2) / 2 - Real.log (2 + t) ≤ (1 / 2) * ((190810977487424618883:ℝ)/42949672960000000000) - ((20794415409:ℝ)/10000000000) := by
    nlinarith [hlogU, hDL]
  exact combine x t hxpos htpos ((190810977487424618883:ℝ)/42949672960000000000) ((20794415409:ℝ)/10000000000) ((28720585946874995412186877:ℝ)/7881299347898368000000000) ((1721529301:ℝ)/1224720000) ((40423:ℝ)/500000) hLDpos hS hQden hP (by norm_num)

private lemma box_2_6 (x t : ℝ) (hx1 : 1 ≤ x) (hx2 : x ≤ 8) (ht : 1 ≤ t)
    (hxl : ((3:ℝ)/2) ≤ x) (hxu : x ≤ (2:ℝ)) (htl : (9:ℝ) ≤ t) (htu : t ≤ (13:ℝ)) :
    Real.log (Real.sqrt (x ^ 2 + t ^ 2)) +
        (Real.arctan (t / x)) ^ 2 / (2 * Real.log (Real.sqrt (x ^ 2 + t ^ 2))) +
        (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) ≤
      Real.log (2 + t) + (3 : ℝ) / 2 := by
  have hxpos : 0 < x := by linarith
  have htpos : 0 < t := by linarith
  have hapos : 0 < x ^ 2 + t ^ 2 := by positivity
  -- upper square bound
  have hx2le : x ^ 2 ≤ ((2:ℝ)) ^ 2 := sq_le_of_nonneg (le_of_lt hxpos) hxu
  have ht2le : t ^ 2 ≤ ((13:ℝ)) ^ 2 := sq_le_of_nonneg (le_of_lt htpos) htu
  have ha_le : x ^ 2 + t ^ 2 ≤ (173:ℝ) := by
    have : ((2:ℝ)) ^ 2 + ((13:ℝ)) ^ 2 = (173:ℝ) := by norm_num
    nlinarith
  have hlogU : Real.log (x ^ 2 + t ^ 2) ≤ ((198314496989139625433821:ℝ)/38482906972160000000000) := by
    exact (Real.log_le_log hapos ha_le).trans vlog_ub_m173
  -- log(2+t) lower bound
  have hDmono : Real.log ((11:ℝ)) ≤ Real.log (2 + t) := by
    apply Real.log_le_log (by norm_num : 0 < (11:ℝ))
    linarith
  have hDL : ((22000673184559761:ℝ)/9175040000000000) ≤ Real.log (2 + t) := (vlog_lb_m11).trans hDmono
  -- lower square bound
  have hx2ge : (((3:ℝ)/2)) ^ 2 ≤ x ^ 2 := sq_le_of_nonneg (by norm_num : 0 ≤ ((3:ℝ)/2)) hxl
  have ht2ge : ((9:ℝ)) ^ 2 ≤ t ^ 2 := sq_le_of_nonneg (by norm_num : 0 ≤ (9:ℝ)) htl
  have hQ3le : ((333:ℝ)/4) ≤ x ^ 2 + t ^ 2 := by
    have : (((3:ℝ)/2)) ^ 2 + ((9:ℝ)) ^ 2 = ((333:ℝ)/4) := by norm_num
    nlinarith
  have hlogL : ((6372552204783428613837597671:ℝ)/1441151880758558720000000000) ≤ Real.log (x ^ 2 + t ^ 2) := by
    exact (vlog_lb_m333_4).trans (Real.log_le_log (by norm_num : 0 < ((333:ℝ)/4)) hQ3le)
  have hLDpos : 0 < ((6372552204783428613837597671:ℝ)/1441151880758558720000000000) := by norm_num
  -- arctan bound
  have htovx : t / x ≤ ((26:ℝ)/3) := by
    rw [div_le_iff₀ hxpos]
    have htu_le : (13:ℝ) ≤ ((26:ℝ)/3) * x := by
      calc
        (13:ℝ) = ((26:ℝ)/3) * ((3:ℝ)/2) := by norm_num
        _ ≤ ((26:ℝ)/3) * x := mul_le_mul_of_nonneg_left hxl (by norm_num : 0 ≤ ((26:ℝ)/3))
    nlinarith [htu_le]
  have hAT : Real.arctan (t / x) ≤ ((51159938984391:ℝ)/35139169520000) := (arctan_mono htovx).trans vatan_ub_m26_3
  have hθsq : (Real.arctan (t / x)) ^ 2 ≤ (((51159938984391:ℝ)/35139169520000)) ^ 2 := by
    have hθn : 0 ≤ Real.arctan (t / x) := Real.arctan_nonneg.mpr (div_nonneg (le_of_lt htpos) (le_of_lt hxpos))
    have hAn : 0 ≤ ((51159938984391:ℝ)/35139169520000) := by norm_num
    rw [sq_le_sq]
    rw [abs_of_nonneg hθn, abs_of_nonneg hAn]
    exact hAT
  have hQden : (Real.arctan (t / x)) ^ 2 / Real.log (x ^ 2 + t ^ 2) ≤
      (((51159938984391:ℝ)/35139169520000)) ^ 2 / (((6372552204783428613837597671:ℝ)/1441151880758558720000000000)) := by
    have h1 : (Real.arctan (t / x)) ^ 2 / Real.log (x ^ 2 + t ^ 2) ≤
        (Real.arctan (t / x)) ^ 2 / ((6372552204783428613837597671:ℝ)/1441151880758558720000000000) := by
      exact div_le_div_of_nonneg_left (sq_nonneg _) hLDpos (by linarith : ((6372552204783428613837597671:ℝ)/1441151880758558720000000000) ≤ Real.log (x ^ 2 + t ^ 2))
    have h2 : (Real.arctan (t / x)) ^ 2 / ((6372552204783428613837597671:ℝ)/1441151880758558720000000000) ≤ (((51159938984391:ℝ)/35139169520000)) ^ 2 / ((6372552204783428613837597671:ℝ)/1441151880758558720000000000) := by
      exact div_le_div_of_nonneg_right hθsq (le_of_lt hLDpos)
    exact h1.trans h2
  -- P bound
  have hP : (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) ≤ ((137:ℝ)/2500) := by
    have hsqrt : Real.sqrt ((333:ℝ)/4) ≤ Real.sqrt (x ^ 2 + t ^ 2) := Real.sqrt_le_sqrt hQ3le
    have hd1 : (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) ≤ (1 : ℝ) / (2 * Real.sqrt ((333:ℝ)/4)) := by
      have hdenpos : 0 < 2 * Real.sqrt ((333:ℝ)/4) := by positivity
      exact div_le_div_of_nonneg_left (by norm_num : 0 ≤ (1 : ℝ)) hdenpos (by nlinarith)
    exact hd1.trans (inv_two_sqrt_le ((333:ℝ)/4) (by norm_num) ((137:ℝ)/2500) (by norm_num) (by norm_num))
  -- S bound
  have hS : Real.log (x ^ 2 + t ^ 2) / 2 - Real.log (2 + t) ≤ (1 / 2) * ((198314496989139625433821:ℝ)/38482906972160000000000) - ((22000673184559761:ℝ)/9175040000000000) := by
    nlinarith [hlogU, hDL]
  exact combine x t hxpos htpos ((198314496989139625433821:ℝ)/38482906972160000000000) ((22000673184559761:ℝ)/9175040000000000) ((6372552204783428613837597671:ℝ)/1441151880758558720000000000) ((51159938984391:ℝ)/35139169520000) ((137:ℝ)/2500) hLDpos hS hQden hP (by norm_num)

private lemma box_2_7 (x t : ℝ) (hx1 : 1 ≤ x) (hx2 : x ≤ 8) (ht : 1 ≤ t)
    (hxl : ((3:ℝ)/2) ≤ x) (hxu : x ≤ (2:ℝ)) (htl : (13:ℝ) ≤ t) (htu : t ≤ (15:ℝ)) :
    Real.log (Real.sqrt (x ^ 2 + t ^ 2)) +
        (Real.arctan (t / x)) ^ 2 / (2 * Real.log (Real.sqrt (x ^ 2 + t ^ 2))) +
        (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) ≤
      Real.log (2 + t) + (3 : ℝ) / 2 := by
  have hxpos : 0 < x := by linarith
  have htpos : 0 < t := by linarith
  have hapos : 0 < x ^ 2 + t ^ 2 := by positivity
  -- upper square bound
  have hx2le : x ^ 2 ≤ ((2:ℝ)) ^ 2 := sq_le_of_nonneg (le_of_lt hxpos) hxu
  have ht2le : t ^ 2 ≤ ((15:ℝ)) ^ 2 := sq_le_of_nonneg (le_of_lt htpos) htu
  have ha_le : x ^ 2 + t ^ 2 ≤ (229:ℝ) := by
    have : ((2:ℝ)) ^ 2 + ((15:ℝ)) ^ 2 = (229:ℝ) := by norm_num
    nlinarith
  have hlogU : Real.log (x ^ 2 + t ^ 2) ≤ ((29872202761228730659157:ℝ)/5497558138880000000000) := by
    exact (Real.log_le_log hapos ha_le).trans vlog_ub_m229
  -- log(2+t) lower bound
  have hDmono : Real.log ((15:ℝ)) ≤ Real.log (2 + t) := by
    apply Real.log_le_log (by norm_num : 0 < (15:ℝ))
    linarith
  have hDL : ((24846468902980723:ℝ)/9175040000000000) ≤ Real.log (2 + t) := (vlog_lb_m15).trans hDmono
  -- lower square bound
  have hx2ge : (((3:ℝ)/2)) ^ 2 ≤ x ^ 2 := sq_le_of_nonneg (by norm_num : 0 ≤ ((3:ℝ)/2)) hxl
  have ht2ge : ((13:ℝ)) ^ 2 ≤ t ^ 2 := sq_le_of_nonneg (by norm_num : 0 ≤ (13:ℝ)) htl
  have hQ3le : ((685:ℝ)/4) ≤ x ^ 2 + t ^ 2 := by
    have : (((3:ℝ)/2)) ^ 2 + ((13:ℝ)) ^ 2 = ((685:ℝ)/4) := by norm_num
    nlinarith
  have hlogL : ((39847000474700510266731395014387:ℝ)/7747632510958011678720000000000) ≤ Real.log (x ^ 2 + t ^ 2) := by
    exact (vlog_lb_m685_4).trans (Real.log_le_log (by norm_num : 0 < ((685:ℝ)/4)) hQ3le)
  have hLDpos : 0 < ((39847000474700510266731395014387:ℝ)/7747632510958011678720000000000) := by norm_num
  -- arctan bound
  have htovx : t / x ≤ (10:ℝ) := by
    rw [div_le_iff₀ hxpos]
    have htu_le : (15:ℝ) ≤ (10:ℝ) * x := by
      calc
        (15:ℝ) = (10:ℝ) * ((3:ℝ)/2) := by norm_num
        _ ≤ (10:ℝ) * x := mul_le_mul_of_nonneg_left hxl (by norm_num : 0 ≤ (10:ℝ))
    nlinarith [htu_le]
  have hAT : Real.arctan (t / x) ≤ ((308937583:ℝ)/210000000) := (arctan_mono htovx).trans vatan_ub_m10
  have hθsq : (Real.arctan (t / x)) ^ 2 ≤ (((308937583:ℝ)/210000000)) ^ 2 := by
    have hθn : 0 ≤ Real.arctan (t / x) := Real.arctan_nonneg.mpr (div_nonneg (le_of_lt htpos) (le_of_lt hxpos))
    have hAn : 0 ≤ ((308937583:ℝ)/210000000) := by norm_num
    rw [sq_le_sq]
    rw [abs_of_nonneg hθn, abs_of_nonneg hAn]
    exact hAT
  have hQden : (Real.arctan (t / x)) ^ 2 / Real.log (x ^ 2 + t ^ 2) ≤
      (((308937583:ℝ)/210000000)) ^ 2 / (((39847000474700510266731395014387:ℝ)/7747632510958011678720000000000)) := by
    have h1 : (Real.arctan (t / x)) ^ 2 / Real.log (x ^ 2 + t ^ 2) ≤
        (Real.arctan (t / x)) ^ 2 / ((39847000474700510266731395014387:ℝ)/7747632510958011678720000000000) := by
      exact div_le_div_of_nonneg_left (sq_nonneg _) hLDpos (by linarith : ((39847000474700510266731395014387:ℝ)/7747632510958011678720000000000) ≤ Real.log (x ^ 2 + t ^ 2))
    have h2 : (Real.arctan (t / x)) ^ 2 / ((39847000474700510266731395014387:ℝ)/7747632510958011678720000000000) ≤ (((308937583:ℝ)/210000000)) ^ 2 / ((39847000474700510266731395014387:ℝ)/7747632510958011678720000000000) := by
      exact div_le_div_of_nonneg_right hθsq (le_of_lt hLDpos)
    exact h1.trans h2
  -- P bound
  have hP : (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) ≤ ((38209:ℝ)/1000000) := by
    have hsqrt : Real.sqrt ((685:ℝ)/4) ≤ Real.sqrt (x ^ 2 + t ^ 2) := Real.sqrt_le_sqrt hQ3le
    have hd1 : (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) ≤ (1 : ℝ) / (2 * Real.sqrt ((685:ℝ)/4)) := by
      have hdenpos : 0 < 2 * Real.sqrt ((685:ℝ)/4) := by positivity
      exact div_le_div_of_nonneg_left (by norm_num : 0 ≤ (1 : ℝ)) hdenpos (by nlinarith)
    exact hd1.trans (inv_two_sqrt_le ((685:ℝ)/4) (by norm_num) ((38209:ℝ)/1000000) (by norm_num) (by norm_num))
  -- S bound
  have hS : Real.log (x ^ 2 + t ^ 2) / 2 - Real.log (2 + t) ≤ (1 / 2) * ((29872202761228730659157:ℝ)/5497558138880000000000) - ((24846468902980723:ℝ)/9175040000000000) := by
    nlinarith [hlogU, hDL]
  exact combine x t hxpos htpos ((29872202761228730659157:ℝ)/5497558138880000000000) ((24846468902980723:ℝ)/9175040000000000) ((39847000474700510266731395014387:ℝ)/7747632510958011678720000000000) ((308937583:ℝ)/210000000) ((38209:ℝ)/1000000) hLDpos hS hQden hP (by norm_num)

private lemma box_3_0 (x t : ℝ) (hx1 : 1 ≤ x) (hx2 : x ≤ 8) (ht : 1 ≤ t)
    (hxl : (2:ℝ) ≤ x) (hxu : x ≤ ((5:ℝ)/2)) (htl : (1:ℝ) ≤ t) (htu : t ≤ ((3:ℝ)/2)) :
    Real.log (Real.sqrt (x ^ 2 + t ^ 2)) +
        (Real.arctan (t / x)) ^ 2 / (2 * Real.log (Real.sqrt (x ^ 2 + t ^ 2))) +
        (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) ≤
      Real.log (2 + t) + (3 : ℝ) / 2 := by
  have hxpos : 0 < x := by linarith
  have htpos : 0 < t := by linarith
  have hapos : 0 < x ^ 2 + t ^ 2 := by positivity
  -- upper square bound
  have hx2le : x ^ 2 ≤ (((5:ℝ)/2)) ^ 2 := sq_le_of_nonneg (le_of_lt hxpos) hxu
  have ht2le : t ^ 2 ≤ (((3:ℝ)/2)) ^ 2 := sq_le_of_nonneg (le_of_lt htpos) htu
  have ha_le : x ^ 2 + t ^ 2 ≤ ((17:ℝ)/2) := by
    have : (((5:ℝ)/2)) ^ 2 + (((3:ℝ)/2)) ^ 2 = ((17:ℝ)/2) := by norm_num
    nlinarith
  have hlogU : Real.log (x ^ 2 + t ^ 2) ≤ ((117811155957512051:ℝ)/55050240000000000) := by
    exact (Real.log_le_log hapos ha_le).trans vlog_ub_m17_2
  -- log(2+t) lower bound
  have hDmono : Real.log ((3:ℝ)) ≤ Real.log (2 + t) := by
    apply Real.log_le_log (by norm_num : 0 < (3:ℝ))
    linarith
  have hDL : ((153784745867:ℝ)/140000000000) ≤ Real.log (2 + t) := (vlog_lb_m3).trans hDmono
  -- lower square bound
  have hx2ge : ((2:ℝ)) ^ 2 ≤ x ^ 2 := sq_le_of_nonneg (by norm_num : 0 ≤ (2:ℝ)) hxl
  have ht2ge : ((1:ℝ)) ^ 2 ≤ t ^ 2 := sq_le_of_nonneg (by norm_num : 0 ≤ (1:ℝ)) htl
  have hQ3le : (5:ℝ) ≤ x ^ 2 + t ^ 2 := by
    have : ((2:ℝ)) ^ 2 + ((1:ℝ)) ^ 2 = (5:ℝ) := by norm_num
    nlinarith
  have hlogL : ((173046727073587:ℝ)/107520000000000) ≤ Real.log (x ^ 2 + t ^ 2) := by
    exact (vlog_lb_m5).trans (Real.log_le_log (by norm_num : 0 < (5:ℝ)) hQ3le)
  have hLDpos : 0 < ((173046727073587:ℝ)/107520000000000) := by norm_num
  -- arctan bound
  have htovx : t / x ≤ ((3:ℝ)/4) := by
    rw [div_le_iff₀ hxpos]
    have htu_le : ((3:ℝ)/2) ≤ ((3:ℝ)/4) * x := by
      calc
        ((3:ℝ)/2) = ((3:ℝ)/4) * (2:ℝ) := by norm_num
        _ ≤ ((3:ℝ)/4) * x := mul_le_mul_of_nonneg_left hxl (by norm_num : 0 ≤ ((3:ℝ)/4))
    nlinarith [htu_le]
  have hAT : Real.arctan (t / x) ≤ ((5928081:ℝ)/9175040) := (arctan_mono htovx).trans vatan_ub_m3_4
  have hθsq : (Real.arctan (t / x)) ^ 2 ≤ (((5928081:ℝ)/9175040)) ^ 2 := by
    have hθn : 0 ≤ Real.arctan (t / x) := Real.arctan_nonneg.mpr (div_nonneg (le_of_lt htpos) (le_of_lt hxpos))
    have hAn : 0 ≤ ((5928081:ℝ)/9175040) := by norm_num
    rw [sq_le_sq]
    rw [abs_of_nonneg hθn, abs_of_nonneg hAn]
    exact hAT
  have hQden : (Real.arctan (t / x)) ^ 2 / Real.log (x ^ 2 + t ^ 2) ≤
      (((5928081:ℝ)/9175040)) ^ 2 / (((173046727073587:ℝ)/107520000000000)) := by
    have h1 : (Real.arctan (t / x)) ^ 2 / Real.log (x ^ 2 + t ^ 2) ≤
        (Real.arctan (t / x)) ^ 2 / ((173046727073587:ℝ)/107520000000000) := by
      exact div_le_div_of_nonneg_left (sq_nonneg _) hLDpos (by linarith : ((173046727073587:ℝ)/107520000000000) ≤ Real.log (x ^ 2 + t ^ 2))
    have h2 : (Real.arctan (t / x)) ^ 2 / ((173046727073587:ℝ)/107520000000000) ≤ (((5928081:ℝ)/9175040)) ^ 2 / ((173046727073587:ℝ)/107520000000000) := by
      exact div_le_div_of_nonneg_right hθsq (le_of_lt hLDpos)
    exact h1.trans h2
  -- P bound
  have hP : (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) ≤ ((223607:ℝ)/1000000) := by
    have hsqrt : Real.sqrt (5:ℝ) ≤ Real.sqrt (x ^ 2 + t ^ 2) := Real.sqrt_le_sqrt hQ3le
    have hd1 : (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) ≤ (1 : ℝ) / (2 * Real.sqrt (5:ℝ)) := by
      have hdenpos : 0 < 2 * Real.sqrt (5:ℝ) := by positivity
      exact div_le_div_of_nonneg_left (by norm_num : 0 ≤ (1 : ℝ)) hdenpos (by nlinarith)
    exact hd1.trans (inv_two_sqrt_le (5:ℝ) (by norm_num) ((223607:ℝ)/1000000) (by norm_num) (by norm_num))
  -- S bound
  have hS : Real.log (x ^ 2 + t ^ 2) / 2 - Real.log (2 + t) ≤ (1 / 2) * ((117811155957512051:ℝ)/55050240000000000) - ((153784745867:ℝ)/140000000000) := by
    nlinarith [hlogU, hDL]
  exact combine x t hxpos htpos ((117811155957512051:ℝ)/55050240000000000) ((153784745867:ℝ)/140000000000) ((173046727073587:ℝ)/107520000000000) ((5928081:ℝ)/9175040) ((223607:ℝ)/1000000) hLDpos hS hQden hP (by norm_num)

private lemma box_3_1 (x t : ℝ) (hx1 : 1 ≤ x) (hx2 : x ≤ 8) (ht : 1 ≤ t)
    (hxl : (2:ℝ) ≤ x) (hxu : x ≤ ((5:ℝ)/2)) (htl : ((3:ℝ)/2) ≤ t) (htu : t ≤ (2:ℝ)) :
    Real.log (Real.sqrt (x ^ 2 + t ^ 2)) +
        (Real.arctan (t / x)) ^ 2 / (2 * Real.log (Real.sqrt (x ^ 2 + t ^ 2))) +
        (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) ≤
      Real.log (2 + t) + (3 : ℝ) / 2 := by
  have hxpos : 0 < x := by linarith
  have htpos : 0 < t := by linarith
  have hapos : 0 < x ^ 2 + t ^ 2 := by positivity
  -- upper square bound
  have hx2le : x ^ 2 ≤ (((5:ℝ)/2)) ^ 2 := sq_le_of_nonneg (le_of_lt hxpos) hxu
  have ht2le : t ^ 2 ≤ ((2:ℝ)) ^ 2 := sq_le_of_nonneg (le_of_lt htpos) htu
  have ha_le : x ^ 2 + t ^ 2 ≤ ((41:ℝ)/4) := by
    have : (((5:ℝ)/2)) ^ 2 + ((2:ℝ)) ^ 2 = ((41:ℝ)/4) := by norm_num
    nlinarith
  have hlogU : Real.log (x ^ 2 + t ^ 2) ≤ ((5466342908420904801:ℝ)/2348810240000000000) := by
    exact (Real.log_le_log hapos ha_le).trans vlog_ub_m41_4
  -- log(2+t) lower bound
  have hDmono : Real.log (((7:ℝ)/2)) ≤ Real.log (2 + t) := by
    apply Real.log_le_log (by norm_num : 0 < ((7:ℝ)/2))
    linarith
  have hDL : ((269394135787799:ℝ)/215040000000000) ≤ Real.log (2 + t) := (vlog_lb_m7_2).trans hDmono
  -- lower square bound
  have hx2ge : ((2:ℝ)) ^ 2 ≤ x ^ 2 := sq_le_of_nonneg (by norm_num : 0 ≤ (2:ℝ)) hxl
  have ht2ge : (((3:ℝ)/2)) ^ 2 ≤ t ^ 2 := sq_le_of_nonneg (by norm_num : 0 ≤ ((3:ℝ)/2)) htl
  have hQ3le : ((25:ℝ)/4) ≤ x ^ 2 + t ^ 2 := by
    have : ((2:ℝ)) ^ 2 + (((3:ℝ)/2)) ^ 2 = ((25:ℝ)/4) := by norm_num
    nlinarith
  have hlogL : ((922367137655392157:ℝ)/503316480000000000) ≤ Real.log (x ^ 2 + t ^ 2) := by
    exact (vlog_lb_m25_4).trans (Real.log_le_log (by norm_num : 0 < ((25:ℝ)/4)) hQ3le)
  have hLDpos : 0 < ((922367137655392157:ℝ)/503316480000000000) := by norm_num
  -- arctan bound
  have htovx : t / x ≤ (1:ℝ) := by
    rw [div_le_iff₀ hxpos]
    have htu_le : (2:ℝ) ≤ (1:ℝ) * x := by
      calc
        (2:ℝ) = (1:ℝ) * (2:ℝ) := by norm_num
        _ ≤ (1:ℝ) * x := mul_le_mul_of_nonneg_left hxl (by norm_num : 0 ≤ (1:ℝ))
    nlinarith [htu_le]
  have hAT : Real.arctan (t / x) ≤ ((263:ℝ)/315) := (arctan_mono htovx).trans vatan_ub_m1
  have hθsq : (Real.arctan (t / x)) ^ 2 ≤ (((263:ℝ)/315)) ^ 2 := by
    have hθn : 0 ≤ Real.arctan (t / x) := Real.arctan_nonneg.mpr (div_nonneg (le_of_lt htpos) (le_of_lt hxpos))
    have hAn : 0 ≤ ((263:ℝ)/315) := by norm_num
    rw [sq_le_sq]
    rw [abs_of_nonneg hθn, abs_of_nonneg hAn]
    exact hAT
  have hQden : (Real.arctan (t / x)) ^ 2 / Real.log (x ^ 2 + t ^ 2) ≤
      (((263:ℝ)/315)) ^ 2 / (((922367137655392157:ℝ)/503316480000000000)) := by
    have h1 : (Real.arctan (t / x)) ^ 2 / Real.log (x ^ 2 + t ^ 2) ≤
        (Real.arctan (t / x)) ^ 2 / ((922367137655392157:ℝ)/503316480000000000) := by
      exact div_le_div_of_nonneg_left (sq_nonneg _) hLDpos (by linarith : ((922367137655392157:ℝ)/503316480000000000) ≤ Real.log (x ^ 2 + t ^ 2))
    have h2 : (Real.arctan (t / x)) ^ 2 / ((922367137655392157:ℝ)/503316480000000000) ≤ (((263:ℝ)/315)) ^ 2 / ((922367137655392157:ℝ)/503316480000000000) := by
      exact div_le_div_of_nonneg_right hθsq (le_of_lt hLDpos)
    exact h1.trans h2
  -- P bound
  have hP : (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) ≤ ((200001:ℝ)/1000000) := by
    have hsqrt : Real.sqrt ((25:ℝ)/4) ≤ Real.sqrt (x ^ 2 + t ^ 2) := Real.sqrt_le_sqrt hQ3le
    have hd1 : (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) ≤ (1 : ℝ) / (2 * Real.sqrt ((25:ℝ)/4)) := by
      have hdenpos : 0 < 2 * Real.sqrt ((25:ℝ)/4) := by positivity
      exact div_le_div_of_nonneg_left (by norm_num : 0 ≤ (1 : ℝ)) hdenpos (by nlinarith)
    exact hd1.trans (inv_two_sqrt_le ((25:ℝ)/4) (by norm_num) ((200001:ℝ)/1000000) (by norm_num) (by norm_num))
  -- S bound
  have hS : Real.log (x ^ 2 + t ^ 2) / 2 - Real.log (2 + t) ≤ (1 / 2) * ((5466342908420904801:ℝ)/2348810240000000000) - ((269394135787799:ℝ)/215040000000000) := by
    nlinarith [hlogU, hDL]
  exact combine x t hxpos htpos ((5466342908420904801:ℝ)/2348810240000000000) ((269394135787799:ℝ)/215040000000000) ((922367137655392157:ℝ)/503316480000000000) ((263:ℝ)/315) ((200001:ℝ)/1000000) hLDpos hS hQden hP (by norm_num)

private lemma box_3_2 (x t : ℝ) (hx1 : 1 ≤ x) (hx2 : x ≤ 8) (ht : 1 ≤ t)
    (hxl : (2:ℝ) ≤ x) (hxu : x ≤ ((5:ℝ)/2)) (htl : (2:ℝ) ≤ t) (htu : t ≤ (3:ℝ)) :
    Real.log (Real.sqrt (x ^ 2 + t ^ 2)) +
        (Real.arctan (t / x)) ^ 2 / (2 * Real.log (Real.sqrt (x ^ 2 + t ^ 2))) +
        (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) ≤
      Real.log (2 + t) + (3 : ℝ) / 2 := by
  have hxpos : 0 < x := by linarith
  have htpos : 0 < t := by linarith
  have hapos : 0 < x ^ 2 + t ^ 2 := by positivity
  -- upper square bound
  have hx2le : x ^ 2 ≤ (((5:ℝ)/2)) ^ 2 := sq_le_of_nonneg (le_of_lt hxpos) hxu
  have ht2le : t ^ 2 ≤ ((3:ℝ)) ^ 2 := sq_le_of_nonneg (le_of_lt htpos) htu
  have ha_le : x ^ 2 + t ^ 2 ≤ ((61:ℝ)/4) := by
    have : (((5:ℝ)/2)) ^ 2 + ((3:ℝ)) ^ 2 = ((61:ℝ)/4) := by norm_num
    nlinarith
  have hlogU : Real.log (x ^ 2 + t ^ 2) ≤ ((3656868707940202021:ℝ)/1342177280000000000) := by
    exact (Real.log_le_log hapos ha_le).trans vlog_ub_m61_4
  -- log(2+t) lower bound
  have hDmono : Real.log ((4:ℝ)) ≤ Real.log (2 + t) := by
    apply Real.log_le_log (by norm_num : 0 < (4:ℝ))
    linarith
  have hDL : ((6931471803:ℝ)/5000000000) ≤ Real.log (2 + t) := (vlog_lb_m4).trans hDmono
  -- lower square bound
  have hx2ge : ((2:ℝ)) ^ 2 ≤ x ^ 2 := sq_le_of_nonneg (by norm_num : 0 ≤ (2:ℝ)) hxl
  have ht2ge : ((2:ℝ)) ^ 2 ≤ t ^ 2 := sq_le_of_nonneg (by norm_num : 0 ≤ (2:ℝ)) htl
  have hQ3le : (8:ℝ) ≤ x ^ 2 + t ^ 2 := by
    have : ((2:ℝ)) ^ 2 + ((2:ℝ)) ^ 2 = (8:ℝ) := by norm_num
    nlinarith
  have hlogL : ((20794415409:ℝ)/10000000000) ≤ Real.log (x ^ 2 + t ^ 2) := by
    exact (vlog_lb_m8).trans (Real.log_le_log (by norm_num : 0 < (8:ℝ)) hQ3le)
  have hLDpos : 0 < ((20794415409:ℝ)/10000000000) := by norm_num
  -- arctan bound
  have htovx : t / x ≤ ((3:ℝ)/2) := by
    rw [div_le_iff₀ hxpos]
    have htu_le : (3:ℝ) ≤ ((3:ℝ)/2) * x := by
      calc
        (3:ℝ) = ((3:ℝ)/2) * (2:ℝ) := by norm_num
        _ ≤ ((3:ℝ)/2) * x := mul_le_mul_of_nonneg_left hxl (by norm_num : 0 ≤ ((3:ℝ)/2))
    nlinarith [htu_le]
  have hAT : Real.arctan (t / x) ≤ ((37695443:ℝ)/38272500) := (arctan_mono htovx).trans vatan_ub_m3_2
  have hθsq : (Real.arctan (t / x)) ^ 2 ≤ (((37695443:ℝ)/38272500)) ^ 2 := by
    have hθn : 0 ≤ Real.arctan (t / x) := Real.arctan_nonneg.mpr (div_nonneg (le_of_lt htpos) (le_of_lt hxpos))
    have hAn : 0 ≤ ((37695443:ℝ)/38272500) := by norm_num
    rw [sq_le_sq]
    rw [abs_of_nonneg hθn, abs_of_nonneg hAn]
    exact hAT
  have hQden : (Real.arctan (t / x)) ^ 2 / Real.log (x ^ 2 + t ^ 2) ≤
      (((37695443:ℝ)/38272500)) ^ 2 / (((20794415409:ℝ)/10000000000)) := by
    have h1 : (Real.arctan (t / x)) ^ 2 / Real.log (x ^ 2 + t ^ 2) ≤
        (Real.arctan (t / x)) ^ 2 / ((20794415409:ℝ)/10000000000) := by
      exact div_le_div_of_nonneg_left (sq_nonneg _) hLDpos (by linarith : ((20794415409:ℝ)/10000000000) ≤ Real.log (x ^ 2 + t ^ 2))
    have h2 : (Real.arctan (t / x)) ^ 2 / ((20794415409:ℝ)/10000000000) ≤ (((37695443:ℝ)/38272500)) ^ 2 / ((20794415409:ℝ)/10000000000) := by
      exact div_le_div_of_nonneg_right hθsq (le_of_lt hLDpos)
    exact h1.trans h2
  -- P bound
  have hP : (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) ≤ ((176777:ℝ)/1000000) := by
    have hsqrt : Real.sqrt (8:ℝ) ≤ Real.sqrt (x ^ 2 + t ^ 2) := Real.sqrt_le_sqrt hQ3le
    have hd1 : (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) ≤ (1 : ℝ) / (2 * Real.sqrt (8:ℝ)) := by
      have hdenpos : 0 < 2 * Real.sqrt (8:ℝ) := by positivity
      exact div_le_div_of_nonneg_left (by norm_num : 0 ≤ (1 : ℝ)) hdenpos (by nlinarith)
    exact hd1.trans (inv_two_sqrt_le (8:ℝ) (by norm_num) ((176777:ℝ)/1000000) (by norm_num) (by norm_num))
  -- S bound
  have hS : Real.log (x ^ 2 + t ^ 2) / 2 - Real.log (2 + t) ≤ (1 / 2) * ((3656868707940202021:ℝ)/1342177280000000000) - ((6931471803:ℝ)/5000000000) := by
    nlinarith [hlogU, hDL]
  exact combine x t hxpos htpos ((3656868707940202021:ℝ)/1342177280000000000) ((6931471803:ℝ)/5000000000) ((20794415409:ℝ)/10000000000) ((37695443:ℝ)/38272500) ((176777:ℝ)/1000000) hLDpos hS hQden hP (by norm_num)

private lemma box_3_3 (x t : ℝ) (hx1 : 1 ≤ x) (hx2 : x ≤ 8) (ht : 1 ≤ t)
    (hxl : (2:ℝ) ≤ x) (hxu : x ≤ ((5:ℝ)/2)) (htl : (3:ℝ) ≤ t) (htu : t ≤ (4:ℝ)) :
    Real.log (Real.sqrt (x ^ 2 + t ^ 2)) +
        (Real.arctan (t / x)) ^ 2 / (2 * Real.log (Real.sqrt (x ^ 2 + t ^ 2))) +
        (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) ≤
      Real.log (2 + t) + (3 : ℝ) / 2 := by
  have hxpos : 0 < x := by linarith
  have htpos : 0 < t := by linarith
  have hapos : 0 < x ^ 2 + t ^ 2 := by positivity
  -- upper square bound
  have hx2le : x ^ 2 ≤ (((5:ℝ)/2)) ^ 2 := sq_le_of_nonneg (le_of_lt hxpos) hxu
  have ht2le : t ^ 2 ≤ ((4:ℝ)) ^ 2 := sq_le_of_nonneg (le_of_lt htpos) htu
  have ha_le : x ^ 2 + t ^ 2 ≤ ((89:ℝ)/4) := by
    have : (((5:ℝ)/2)) ^ 2 + ((4:ℝ)) ^ 2 = ((89:ℝ)/4) := by norm_num
    nlinarith
  have hlogU : Real.log (x ^ 2 + t ^ 2) ≤ ((2798181474511641929987:ℝ)/901943132160000000000) := by
    exact (Real.log_le_log hapos ha_le).trans vlog_ub_m89_4
  -- log(2+t) lower bound
  have hDmono : Real.log ((5:ℝ)) ≤ Real.log (2 + t) := by
    apply Real.log_le_log (by norm_num : 0 < (5:ℝ))
    linarith
  have hDL : ((173046727073587:ℝ)/107520000000000) ≤ Real.log (2 + t) := (vlog_lb_m5).trans hDmono
  -- lower square bound
  have hx2ge : ((2:ℝ)) ^ 2 ≤ x ^ 2 := sq_le_of_nonneg (by norm_num : 0 ≤ (2:ℝ)) hxl
  have ht2ge : ((3:ℝ)) ^ 2 ≤ t ^ 2 := sq_le_of_nonneg (by norm_num : 0 ≤ (3:ℝ)) htl
  have hQ3le : (13:ℝ) ≤ x ^ 2 + t ^ 2 := by
    have : ((2:ℝ)) ^ 2 + ((3:ℝ)) ^ 2 = (13:ℝ) := by norm_num
    nlinarith
  have hlogL : ((23533504367824473:ℝ)/9175040000000000) ≤ Real.log (x ^ 2 + t ^ 2) := by
    exact (vlog_lb_m13).trans (Real.log_le_log (by norm_num : 0 < (13:ℝ)) hQ3le)
  have hLDpos : 0 < ((23533504367824473:ℝ)/9175040000000000) := by norm_num
  -- arctan bound
  have htovx : t / x ≤ (2:ℝ) := by
    rw [div_le_iff₀ hxpos]
    have htu_le : (4:ℝ) ≤ (2:ℝ) * x := by
      calc
        (4:ℝ) = (2:ℝ) * (2:ℝ) := by norm_num
        _ ≤ (2:ℝ) * x := mul_le_mul_of_nonneg_left hxl (by norm_num : 0 ≤ (2:ℝ))
    nlinarith [htu_le]
  have hAT : Real.arctan (t / x) ≤ ((1860319:ℝ)/1680000) := (arctan_mono htovx).trans vatan_ub_m2
  have hθsq : (Real.arctan (t / x)) ^ 2 ≤ (((1860319:ℝ)/1680000)) ^ 2 := by
    have hθn : 0 ≤ Real.arctan (t / x) := Real.arctan_nonneg.mpr (div_nonneg (le_of_lt htpos) (le_of_lt hxpos))
    have hAn : 0 ≤ ((1860319:ℝ)/1680000) := by norm_num
    rw [sq_le_sq]
    rw [abs_of_nonneg hθn, abs_of_nonneg hAn]
    exact hAT
  have hQden : (Real.arctan (t / x)) ^ 2 / Real.log (x ^ 2 + t ^ 2) ≤
      (((1860319:ℝ)/1680000)) ^ 2 / (((23533504367824473:ℝ)/9175040000000000)) := by
    have h1 : (Real.arctan (t / x)) ^ 2 / Real.log (x ^ 2 + t ^ 2) ≤
        (Real.arctan (t / x)) ^ 2 / ((23533504367824473:ℝ)/9175040000000000) := by
      exact div_le_div_of_nonneg_left (sq_nonneg _) hLDpos (by linarith : ((23533504367824473:ℝ)/9175040000000000) ≤ Real.log (x ^ 2 + t ^ 2))
    have h2 : (Real.arctan (t / x)) ^ 2 / ((23533504367824473:ℝ)/9175040000000000) ≤ (((1860319:ℝ)/1680000)) ^ 2 / ((23533504367824473:ℝ)/9175040000000000) := by
      exact div_le_div_of_nonneg_right hθsq (le_of_lt hLDpos)
    exact h1.trans h2
  -- P bound
  have hP : (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) ≤ ((34669:ℝ)/250000) := by
    have hsqrt : Real.sqrt (13:ℝ) ≤ Real.sqrt (x ^ 2 + t ^ 2) := Real.sqrt_le_sqrt hQ3le
    have hd1 : (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) ≤ (1 : ℝ) / (2 * Real.sqrt (13:ℝ)) := by
      have hdenpos : 0 < 2 * Real.sqrt (13:ℝ) := by positivity
      exact div_le_div_of_nonneg_left (by norm_num : 0 ≤ (1 : ℝ)) hdenpos (by nlinarith)
    exact hd1.trans (inv_two_sqrt_le (13:ℝ) (by norm_num) ((34669:ℝ)/250000) (by norm_num) (by norm_num))
  -- S bound
  have hS : Real.log (x ^ 2 + t ^ 2) / 2 - Real.log (2 + t) ≤ (1 / 2) * ((2798181474511641929987:ℝ)/901943132160000000000) - ((173046727073587:ℝ)/107520000000000) := by
    nlinarith [hlogU, hDL]
  exact combine x t hxpos htpos ((2798181474511641929987:ℝ)/901943132160000000000) ((173046727073587:ℝ)/107520000000000) ((23533504367824473:ℝ)/9175040000000000) ((1860319:ℝ)/1680000) ((34669:ℝ)/250000) hLDpos hS hQden hP (by norm_num)

private lemma box_3_4 (x t : ℝ) (hx1 : 1 ≤ x) (hx2 : x ≤ 8) (ht : 1 ≤ t)
    (hxl : (2:ℝ) ≤ x) (hxu : x ≤ ((5:ℝ)/2)) (htl : (4:ℝ) ≤ t) (htu : t ≤ (6:ℝ)) :
    Real.log (Real.sqrt (x ^ 2 + t ^ 2)) +
        (Real.arctan (t / x)) ^ 2 / (2 * Real.log (Real.sqrt (x ^ 2 + t ^ 2))) +
        (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) ≤
      Real.log (2 + t) + (3 : ℝ) / 2 := by
  have hxpos : 0 < x := by linarith
  have htpos : 0 < t := by linarith
  have hapos : 0 < x ^ 2 + t ^ 2 := by positivity
  -- upper square bound
  have hx2le : x ^ 2 ≤ (((5:ℝ)/2)) ^ 2 := sq_le_of_nonneg (le_of_lt hxpos) hxu
  have ht2le : t ^ 2 ≤ ((6:ℝ)) ^ 2 := sq_le_of_nonneg (le_of_lt htpos) htu
  have ha_le : x ^ 2 + t ^ 2 ≤ ((169:ℝ)/4) := by
    have : (((5:ℝ)/2)) ^ 2 + ((6:ℝ)) ^ 2 = ((169:ℝ)/4) := by norm_num
    nlinarith
  have hlogU : Real.log (x ^ 2 + t ^ 2) ≤ ((86439115988623150743959:ℝ)/23089744183296000000000) := by
    exact (Real.log_le_log hapos ha_le).trans vlog_ub_m169_4
  -- log(2+t) lower bound
  have hDmono : Real.log ((6:ℝ)) ≤ Real.log (2 + t) := by
    apply Real.log_le_log (by norm_num : 0 < (6:ℝ))
    linarith
  have hDL : ((250825351109:ℝ)/140000000000) ≤ Real.log (2 + t) := (vlog_lb_m6).trans hDmono
  -- lower square bound
  have hx2ge : ((2:ℝ)) ^ 2 ≤ x ^ 2 := sq_le_of_nonneg (by norm_num : 0 ≤ (2:ℝ)) hxl
  have ht2ge : ((4:ℝ)) ^ 2 ≤ t ^ 2 := sq_le_of_nonneg (by norm_num : 0 ≤ (4:ℝ)) htl
  have hQ3le : (20:ℝ) ≤ x ^ 2 + t ^ 2 := by
    have : ((2:ℝ)) ^ 2 + ((4:ℝ)) ^ 2 = (20:ℝ) := by norm_num
    nlinarith
  have hlogL : ((322101096725299:ℝ)/107520000000000) ≤ Real.log (x ^ 2 + t ^ 2) := by
    exact (vlog_lb_m20).trans (Real.log_le_log (by norm_num : 0 < (20:ℝ)) hQ3le)
  have hLDpos : 0 < ((322101096725299:ℝ)/107520000000000) := by norm_num
  -- arctan bound
  have htovx : t / x ≤ (3:ℝ) := by
    rw [div_le_iff₀ hxpos]
    have htu_le : (6:ℝ) ≤ (3:ℝ) * x := by
      calc
        (6:ℝ) = (3:ℝ) * (2:ℝ) := by norm_num
        _ ≤ (3:ℝ) * x := mul_le_mul_of_nonneg_left hxl (by norm_num : 0 ≤ (3:ℝ))
    nlinarith [htu_le]
  have hAT : Real.arctan (t / x) ≤ ((47804443:ℝ)/38272500) := (arctan_mono htovx).trans vatan_ub_m3
  have hθsq : (Real.arctan (t / x)) ^ 2 ≤ (((47804443:ℝ)/38272500)) ^ 2 := by
    have hθn : 0 ≤ Real.arctan (t / x) := Real.arctan_nonneg.mpr (div_nonneg (le_of_lt htpos) (le_of_lt hxpos))
    have hAn : 0 ≤ ((47804443:ℝ)/38272500) := by norm_num
    rw [sq_le_sq]
    rw [abs_of_nonneg hθn, abs_of_nonneg hAn]
    exact hAT
  have hQden : (Real.arctan (t / x)) ^ 2 / Real.log (x ^ 2 + t ^ 2) ≤
      (((47804443:ℝ)/38272500)) ^ 2 / (((322101096725299:ℝ)/107520000000000)) := by
    have h1 : (Real.arctan (t / x)) ^ 2 / Real.log (x ^ 2 + t ^ 2) ≤
        (Real.arctan (t / x)) ^ 2 / ((322101096725299:ℝ)/107520000000000) := by
      exact div_le_div_of_nonneg_left (sq_nonneg _) hLDpos (by linarith : ((322101096725299:ℝ)/107520000000000) ≤ Real.log (x ^ 2 + t ^ 2))
    have h2 : (Real.arctan (t / x)) ^ 2 / ((322101096725299:ℝ)/107520000000000) ≤ (((47804443:ℝ)/38272500)) ^ 2 / ((322101096725299:ℝ)/107520000000000) := by
      exact div_le_div_of_nonneg_right hθsq (le_of_lt hLDpos)
    exact h1.trans h2
  -- P bound
  have hP : (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) ≤ ((27951:ℝ)/250000) := by
    have hsqrt : Real.sqrt (20:ℝ) ≤ Real.sqrt (x ^ 2 + t ^ 2) := Real.sqrt_le_sqrt hQ3le
    have hd1 : (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) ≤ (1 : ℝ) / (2 * Real.sqrt (20:ℝ)) := by
      have hdenpos : 0 < 2 * Real.sqrt (20:ℝ) := by positivity
      exact div_le_div_of_nonneg_left (by norm_num : 0 ≤ (1 : ℝ)) hdenpos (by nlinarith)
    exact hd1.trans (inv_two_sqrt_le (20:ℝ) (by norm_num) ((27951:ℝ)/250000) (by norm_num) (by norm_num))
  -- S bound
  have hS : Real.log (x ^ 2 + t ^ 2) / 2 - Real.log (2 + t) ≤ (1 / 2) * ((86439115988623150743959:ℝ)/23089744183296000000000) - ((250825351109:ℝ)/140000000000) := by
    nlinarith [hlogU, hDL]
  exact combine x t hxpos htpos ((86439115988623150743959:ℝ)/23089744183296000000000) ((250825351109:ℝ)/140000000000) ((322101096725299:ℝ)/107520000000000) ((47804443:ℝ)/38272500) ((27951:ℝ)/250000) hLDpos hS hQden hP (by norm_num)

private lemma box_3_5 (x t : ℝ) (hx1 : 1 ≤ x) (hx2 : x ≤ 8) (ht : 1 ≤ t)
    (hxl : (2:ℝ) ≤ x) (hxu : x ≤ ((5:ℝ)/2)) (htl : (6:ℝ) ≤ t) (htu : t ≤ (9:ℝ)) :
    Real.log (Real.sqrt (x ^ 2 + t ^ 2)) +
        (Real.arctan (t / x)) ^ 2 / (2 * Real.log (Real.sqrt (x ^ 2 + t ^ 2))) +
        (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) ≤
      Real.log (2 + t) + (3 : ℝ) / 2 := by
  have hxpos : 0 < x := by linarith
  have htpos : 0 < t := by linarith
  have hapos : 0 < x ^ 2 + t ^ 2 := by positivity
  -- upper square bound
  have hx2le : x ^ 2 ≤ (((5:ℝ)/2)) ^ 2 := sq_le_of_nonneg (le_of_lt hxpos) hxu
  have ht2le : t ^ 2 ≤ ((9:ℝ)) ^ 2 := sq_le_of_nonneg (le_of_lt htpos) htu
  have ha_le : x ^ 2 + t ^ 2 ≤ ((349:ℝ)/4) := by
    have : (((5:ℝ)/2)) ^ 2 + ((9:ℝ)) ^ 2 = ((349:ℝ)/4) := by norm_num
    nlinarith
  have hlogU : Real.log (x ^ 2 + t ^ 2) ≤ ((22012499854045905145531629:ℝ)/4925812092436480000000000) := by
    exact (Real.log_le_log hapos ha_le).trans vlog_ub_m349_4
  -- log(2+t) lower bound
  have hDmono : Real.log ((8:ℝ)) ≤ Real.log (2 + t) := by
    apply Real.log_le_log (by norm_num : 0 < (8:ℝ))
    linarith
  have hDL : ((20794415409:ℝ)/10000000000) ≤ Real.log (2 + t) := (vlog_lb_m8).trans hDmono
  -- lower square bound
  have hx2ge : ((2:ℝ)) ^ 2 ≤ x ^ 2 := sq_le_of_nonneg (by norm_num : 0 ≤ (2:ℝ)) hxl
  have ht2ge : ((6:ℝ)) ^ 2 ≤ t ^ 2 := sq_le_of_nonneg (by norm_num : 0 ≤ (6:ℝ)) htl
  have hQ3le : (40:ℝ) ≤ x ^ 2 + t ^ 2 := by
    have : ((2:ℝ)) ^ 2 + ((6:ℝ)) ^ 2 = (40:ℝ) := by norm_num
    nlinarith
  have hlogL : ((79325656310231:ℝ)/21504000000000) ≤ Real.log (x ^ 2 + t ^ 2) := by
    exact (vlog_lb_m40).trans (Real.log_le_log (by norm_num : 0 < (40:ℝ)) hQ3le)
  have hLDpos : 0 < ((79325656310231:ℝ)/21504000000000) := by norm_num
  -- arctan bound
  have htovx : t / x ≤ ((9:ℝ)/2) := by
    rw [div_le_iff₀ hxpos]
    have htu_le : (9:ℝ) ≤ ((9:ℝ)/2) * x := by
      calc
        (9:ℝ) = ((9:ℝ)/2) * (2:ℝ) := by norm_num
        _ ≤ ((9:ℝ)/2) * x := mul_le_mul_of_nonneg_left hxl (by norm_num : 0 ≤ ((9:ℝ)/2))
    nlinarith [htu_le]
  have hAT : Real.arctan (t / x) ≤ ((113176027841:ℝ)/83701957500) := (arctan_mono htovx).trans vatan_ub_m9_2
  have hθsq : (Real.arctan (t / x)) ^ 2 ≤ (((113176027841:ℝ)/83701957500)) ^ 2 := by
    have hθn : 0 ≤ Real.arctan (t / x) := Real.arctan_nonneg.mpr (div_nonneg (le_of_lt htpos) (le_of_lt hxpos))
    have hAn : 0 ≤ ((113176027841:ℝ)/83701957500) := by norm_num
    rw [sq_le_sq]
    rw [abs_of_nonneg hθn, abs_of_nonneg hAn]
    exact hAT
  have hQden : (Real.arctan (t / x)) ^ 2 / Real.log (x ^ 2 + t ^ 2) ≤
      (((113176027841:ℝ)/83701957500)) ^ 2 / (((79325656310231:ℝ)/21504000000000)) := by
    have h1 : (Real.arctan (t / x)) ^ 2 / Real.log (x ^ 2 + t ^ 2) ≤
        (Real.arctan (t / x)) ^ 2 / ((79325656310231:ℝ)/21504000000000) := by
      exact div_le_div_of_nonneg_left (sq_nonneg _) hLDpos (by linarith : ((79325656310231:ℝ)/21504000000000) ≤ Real.log (x ^ 2 + t ^ 2))
    have h2 : (Real.arctan (t / x)) ^ 2 / ((79325656310231:ℝ)/21504000000000) ≤ (((113176027841:ℝ)/83701957500)) ^ 2 / ((79325656310231:ℝ)/21504000000000) := by
      exact div_le_div_of_nonneg_right hθsq (le_of_lt hLDpos)
    exact h1.trans h2
  -- P bound
  have hP : (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) ≤ ((79057:ℝ)/1000000) := by
    have hsqrt : Real.sqrt (40:ℝ) ≤ Real.sqrt (x ^ 2 + t ^ 2) := Real.sqrt_le_sqrt hQ3le
    have hd1 : (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) ≤ (1 : ℝ) / (2 * Real.sqrt (40:ℝ)) := by
      have hdenpos : 0 < 2 * Real.sqrt (40:ℝ) := by positivity
      exact div_le_div_of_nonneg_left (by norm_num : 0 ≤ (1 : ℝ)) hdenpos (by nlinarith)
    exact hd1.trans (inv_two_sqrt_le (40:ℝ) (by norm_num) ((79057:ℝ)/1000000) (by norm_num) (by norm_num))
  -- S bound
  have hS : Real.log (x ^ 2 + t ^ 2) / 2 - Real.log (2 + t) ≤ (1 / 2) * ((22012499854045905145531629:ℝ)/4925812092436480000000000) - ((20794415409:ℝ)/10000000000) := by
    nlinarith [hlogU, hDL]
  exact combine x t hxpos htpos ((22012499854045905145531629:ℝ)/4925812092436480000000000) ((20794415409:ℝ)/10000000000) ((79325656310231:ℝ)/21504000000000) ((113176027841:ℝ)/83701957500) ((79057:ℝ)/1000000) hLDpos hS hQden hP (by norm_num)

private lemma box_3_6 (x t : ℝ) (hx1 : 1 ≤ x) (hx2 : x ≤ 8) (ht : 1 ≤ t)
    (hxl : (2:ℝ) ≤ x) (hxu : x ≤ ((5:ℝ)/2)) (htl : (9:ℝ) ≤ t) (htu : t ≤ (13:ℝ)) :
    Real.log (Real.sqrt (x ^ 2 + t ^ 2)) +
        (Real.arctan (t / x)) ^ 2 / (2 * Real.log (Real.sqrt (x ^ 2 + t ^ 2))) +
        (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) ≤
      Real.log (2 + t) + (3 : ℝ) / 2 := by
  have hxpos : 0 < x := by linarith
  have htpos : 0 < t := by linarith
  have hapos : 0 < x ^ 2 + t ^ 2 := by positivity
  -- upper square bound
  have hx2le : x ^ 2 ≤ (((5:ℝ)/2)) ^ 2 := sq_le_of_nonneg (le_of_lt hxpos) hxu
  have ht2le : t ^ 2 ≤ ((13:ℝ)) ^ 2 := sq_le_of_nonneg (le_of_lt htpos) htu
  have ha_le : x ^ 2 + t ^ 2 ≤ ((701:ℝ)/4) := by
    have : (((5:ℝ)/2)) ^ 2 + ((13:ℝ)) ^ 2 = ((701:ℝ)/4) := by norm_num
    nlinarith
  have hlogU : Real.log (x ^ 2 + t ^ 2) ≤ ((465334071459721956196471627:ℝ)/90071992547409920000000000) := by
    exact (Real.log_le_log hapos ha_le).trans vlog_ub_m701_4
  -- log(2+t) lower bound
  have hDmono : Real.log ((11:ℝ)) ≤ Real.log (2 + t) := by
    apply Real.log_le_log (by norm_num : 0 < (11:ℝ))
    linarith
  have hDL : ((22000673184559761:ℝ)/9175040000000000) ≤ Real.log (2 + t) := (vlog_lb_m11).trans hDmono
  -- lower square bound
  have hx2ge : ((2:ℝ)) ^ 2 ≤ x ^ 2 := sq_le_of_nonneg (by norm_num : 0 ≤ (2:ℝ)) hxl
  have ht2ge : ((9:ℝ)) ^ 2 ≤ t ^ 2 := sq_le_of_nonneg (by norm_num : 0 ≤ (9:ℝ)) htl
  have hQ3le : (85:ℝ) ≤ x ^ 2 + t ^ 2 := by
    have : ((2:ℝ)) ^ 2 + ((9:ℝ)) ^ 2 = (85:ℝ) := by norm_num
    nlinarith
  have hlogL : ((97694851043729759935911:ℝ)/21990232555520000000000) ≤ Real.log (x ^ 2 + t ^ 2) := by
    exact (vlog_lb_m85).trans (Real.log_le_log (by norm_num : 0 < (85:ℝ)) hQ3le)
  have hLDpos : 0 < ((97694851043729759935911:ℝ)/21990232555520000000000) := by norm_num
  -- arctan bound
  have htovx : t / x ≤ ((13:ℝ)/2) := by
    rw [div_le_iff₀ hxpos]
    have htu_le : (13:ℝ) ≤ ((13:ℝ)/2) * x := by
      calc
        (13:ℝ) = ((13:ℝ)/2) * (2:ℝ) := by norm_num
        _ ≤ ((13:ℝ)/2) * x := mul_le_mul_of_nonneg_left hxl (by norm_num : 0 ≤ ((13:ℝ)/2))
    nlinarith [htu_le]
  have hAT : Real.arctan (t / x) ≤ ((4671809722439:ℝ)/3294297142500) := (arctan_mono htovx).trans vatan_ub_m13_2
  have hθsq : (Real.arctan (t / x)) ^ 2 ≤ (((4671809722439:ℝ)/3294297142500)) ^ 2 := by
    have hθn : 0 ≤ Real.arctan (t / x) := Real.arctan_nonneg.mpr (div_nonneg (le_of_lt htpos) (le_of_lt hxpos))
    have hAn : 0 ≤ ((4671809722439:ℝ)/3294297142500) := by norm_num
    rw [sq_le_sq]
    rw [abs_of_nonneg hθn, abs_of_nonneg hAn]
    exact hAT
  have hQden : (Real.arctan (t / x)) ^ 2 / Real.log (x ^ 2 + t ^ 2) ≤
      (((4671809722439:ℝ)/3294297142500)) ^ 2 / (((97694851043729759935911:ℝ)/21990232555520000000000)) := by
    have h1 : (Real.arctan (t / x)) ^ 2 / Real.log (x ^ 2 + t ^ 2) ≤
        (Real.arctan (t / x)) ^ 2 / ((97694851043729759935911:ℝ)/21990232555520000000000) := by
      exact div_le_div_of_nonneg_left (sq_nonneg _) hLDpos (by linarith : ((97694851043729759935911:ℝ)/21990232555520000000000) ≤ Real.log (x ^ 2 + t ^ 2))
    have h2 : (Real.arctan (t / x)) ^ 2 / ((97694851043729759935911:ℝ)/21990232555520000000000) ≤ (((4671809722439:ℝ)/3294297142500)) ^ 2 / ((97694851043729759935911:ℝ)/21990232555520000000000) := by
      exact div_le_div_of_nonneg_right hθsq (le_of_lt hLDpos)
    exact h1.trans h2
  -- P bound
  have hP : (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) ≤ ((54233:ℝ)/1000000) := by
    have hsqrt : Real.sqrt (85:ℝ) ≤ Real.sqrt (x ^ 2 + t ^ 2) := Real.sqrt_le_sqrt hQ3le
    have hd1 : (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) ≤ (1 : ℝ) / (2 * Real.sqrt (85:ℝ)) := by
      have hdenpos : 0 < 2 * Real.sqrt (85:ℝ) := by positivity
      exact div_le_div_of_nonneg_left (by norm_num : 0 ≤ (1 : ℝ)) hdenpos (by nlinarith)
    exact hd1.trans (inv_two_sqrt_le (85:ℝ) (by norm_num) ((54233:ℝ)/1000000) (by norm_num) (by norm_num))
  -- S bound
  have hS : Real.log (x ^ 2 + t ^ 2) / 2 - Real.log (2 + t) ≤ (1 / 2) * ((465334071459721956196471627:ℝ)/90071992547409920000000000) - ((22000673184559761:ℝ)/9175040000000000) := by
    nlinarith [hlogU, hDL]
  exact combine x t hxpos htpos ((465334071459721956196471627:ℝ)/90071992547409920000000000) ((22000673184559761:ℝ)/9175040000000000) ((97694851043729759935911:ℝ)/21990232555520000000000) ((4671809722439:ℝ)/3294297142500) ((54233:ℝ)/1000000) hLDpos hS hQden hP (by norm_num)

private lemma box_3_7 (x t : ℝ) (hx1 : 1 ≤ x) (hx2 : x ≤ 8) (ht : 1 ≤ t)
    (hxl : (2:ℝ) ≤ x) (hxu : x ≤ ((5:ℝ)/2)) (htl : (13:ℝ) ≤ t) (htu : t ≤ (15:ℝ)) :
    Real.log (Real.sqrt (x ^ 2 + t ^ 2)) +
        (Real.arctan (t / x)) ^ 2 / (2 * Real.log (Real.sqrt (x ^ 2 + t ^ 2))) +
        (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) ≤
      Real.log (2 + t) + (3 : ℝ) / 2 := by
  have hxpos : 0 < x := by linarith
  have htpos : 0 < t := by linarith
  have hapos : 0 < x ^ 2 + t ^ 2 := by positivity
  -- upper square bound
  have hx2le : x ^ 2 ≤ (((5:ℝ)/2)) ^ 2 := sq_le_of_nonneg (le_of_lt hxpos) hxu
  have ht2le : t ^ 2 ≤ ((15:ℝ)) ^ 2 := sq_le_of_nonneg (le_of_lt htpos) htu
  have ha_le : x ^ 2 + t ^ 2 ≤ ((925:ℝ)/4) := by
    have : (((5:ℝ)/2)) ^ 2 + ((15:ℝ)) ^ 2 = ((925:ℝ)/4) := by norm_num
    nlinarith
  have hlogU : Real.log (x ^ 2 + t ^ 2) ≤ ((122576709136283568781860197:ℝ)/22517998136852480000000000) := by
    exact (Real.log_le_log hapos ha_le).trans vlog_ub_m925_4
  -- log(2+t) lower bound
  have hDmono : Real.log ((15:ℝ)) ≤ Real.log (2 + t) := by
    apply Real.log_le_log (by norm_num : 0 < (15:ℝ))
    linarith
  have hDL : ((24846468902980723:ℝ)/9175040000000000) ≤ Real.log (2 + t) := (vlog_lb_m15).trans hDmono
  -- lower square bound
  have hx2ge : ((2:ℝ)) ^ 2 ≤ x ^ 2 := sq_le_of_nonneg (by norm_num : 0 ≤ (2:ℝ)) hxl
  have ht2ge : ((13:ℝ)) ^ 2 ≤ t ^ 2 := sq_le_of_nonneg (by norm_num : 0 ≤ (13:ℝ)) htl
  have hQ3le : (173:ℝ) ≤ x ^ 2 + t ^ 2 := by
    have : ((2:ℝ)) ^ 2 + ((13:ℝ)) ^ 2 = (173:ℝ) := by norm_num
    nlinarith
  have hlogL : ((203072895307493988100151889:ℝ)/39406496739491840000000000) ≤ Real.log (x ^ 2 + t ^ 2) := by
    exact (vlog_lb_m173).trans (Real.log_le_log (by norm_num : 0 < (173:ℝ)) hQ3le)
  have hLDpos : 0 < ((203072895307493988100151889:ℝ)/39406496739491840000000000) := by norm_num
  -- arctan bound
  have htovx : t / x ≤ ((15:ℝ)/2) := by
    rw [div_le_iff₀ hxpos]
    have htu_le : (15:ℝ) ≤ ((15:ℝ)/2) * x := by
      calc
        (15:ℝ) = ((15:ℝ)/2) * (2:ℝ) := by norm_num
        _ ≤ ((15:ℝ)/2) * x := mul_le_mul_of_nonneg_left hxl (by norm_num : 0 ≤ ((15:ℝ)/2))
    nlinarith [htu_le]
  have hAT : Real.arctan (t / x) ≤ ((6880670567:ℝ)/4784062500) := (arctan_mono htovx).trans vatan_ub_m15_2
  have hθsq : (Real.arctan (t / x)) ^ 2 ≤ (((6880670567:ℝ)/4784062500)) ^ 2 := by
    have hθn : 0 ≤ Real.arctan (t / x) := Real.arctan_nonneg.mpr (div_nonneg (le_of_lt htpos) (le_of_lt hxpos))
    have hAn : 0 ≤ ((6880670567:ℝ)/4784062500) := by norm_num
    rw [sq_le_sq]
    rw [abs_of_nonneg hθn, abs_of_nonneg hAn]
    exact hAT
  have hQden : (Real.arctan (t / x)) ^ 2 / Real.log (x ^ 2 + t ^ 2) ≤
      (((6880670567:ℝ)/4784062500)) ^ 2 / (((203072895307493988100151889:ℝ)/39406496739491840000000000)) := by
    have h1 : (Real.arctan (t / x)) ^ 2 / Real.log (x ^ 2 + t ^ 2) ≤
        (Real.arctan (t / x)) ^ 2 / ((203072895307493988100151889:ℝ)/39406496739491840000000000) := by
      exact div_le_div_of_nonneg_left (sq_nonneg _) hLDpos (by linarith : ((203072895307493988100151889:ℝ)/39406496739491840000000000) ≤ Real.log (x ^ 2 + t ^ 2))
    have h2 : (Real.arctan (t / x)) ^ 2 / ((203072895307493988100151889:ℝ)/39406496739491840000000000) ≤ (((6880670567:ℝ)/4784062500)) ^ 2 / ((203072895307493988100151889:ℝ)/39406496739491840000000000) := by
      exact div_le_div_of_nonneg_right hθsq (le_of_lt hLDpos)
    exact h1.trans h2
  -- P bound
  have hP : (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) ≤ ((7603:ℝ)/200000) := by
    have hsqrt : Real.sqrt (173:ℝ) ≤ Real.sqrt (x ^ 2 + t ^ 2) := Real.sqrt_le_sqrt hQ3le
    have hd1 : (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) ≤ (1 : ℝ) / (2 * Real.sqrt (173:ℝ)) := by
      have hdenpos : 0 < 2 * Real.sqrt (173:ℝ) := by positivity
      exact div_le_div_of_nonneg_left (by norm_num : 0 ≤ (1 : ℝ)) hdenpos (by nlinarith)
    exact hd1.trans (inv_two_sqrt_le (173:ℝ) (by norm_num) ((7603:ℝ)/200000) (by norm_num) (by norm_num))
  -- S bound
  have hS : Real.log (x ^ 2 + t ^ 2) / 2 - Real.log (2 + t) ≤ (1 / 2) * ((122576709136283568781860197:ℝ)/22517998136852480000000000) - ((24846468902980723:ℝ)/9175040000000000) := by
    nlinarith [hlogU, hDL]
  exact combine x t hxpos htpos ((122576709136283568781860197:ℝ)/22517998136852480000000000) ((24846468902980723:ℝ)/9175040000000000) ((203072895307493988100151889:ℝ)/39406496739491840000000000) ((6880670567:ℝ)/4784062500) ((7603:ℝ)/200000) hLDpos hS hQden hP (by norm_num)

private lemma box_4_0 (x t : ℝ) (hx1 : 1 ≤ x) (hx2 : x ≤ 8) (ht : 1 ≤ t)
    (hxl : ((5:ℝ)/2) ≤ x) (hxu : x ≤ (3:ℝ)) (htl : (1:ℝ) ≤ t) (htu : t ≤ ((3:ℝ)/2)) :
    Real.log (Real.sqrt (x ^ 2 + t ^ 2)) +
        (Real.arctan (t / x)) ^ 2 / (2 * Real.log (Real.sqrt (x ^ 2 + t ^ 2))) +
        (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) ≤
      Real.log (2 + t) + (3 : ℝ) / 2 := by
  have hxpos : 0 < x := by linarith
  have htpos : 0 < t := by linarith
  have hapos : 0 < x ^ 2 + t ^ 2 := by positivity
  -- upper square bound
  have hx2le : x ^ 2 ≤ ((3:ℝ)) ^ 2 := sq_le_of_nonneg (le_of_lt hxpos) hxu
  have ht2le : t ^ 2 ≤ (((3:ℝ)/2)) ^ 2 := sq_le_of_nonneg (le_of_lt htpos) htu
  have ha_le : x ^ 2 + t ^ 2 ≤ ((45:ℝ)/4) := by
    have : ((3:ℝ)) ^ 2 + (((3:ℝ)/2)) ^ 2 = ((45:ℝ)/4) := by norm_num
    nlinarith
  have hlogU : Real.log (x ^ 2 + t ^ 2) ≤ ((5685145627975592301:ℝ)/2348810240000000000) := by
    exact (Real.log_le_log hapos ha_le).trans vlog_ub_m45_4
  -- log(2+t) lower bound
  have hDmono : Real.log ((3:ℝ)) ≤ Real.log (2 + t) := by
    apply Real.log_le_log (by norm_num : 0 < (3:ℝ))
    linarith
  have hDL : ((153784745867:ℝ)/140000000000) ≤ Real.log (2 + t) := (vlog_lb_m3).trans hDmono
  -- lower square bound
  have hx2ge : (((5:ℝ)/2)) ^ 2 ≤ x ^ 2 := sq_le_of_nonneg (by norm_num : 0 ≤ ((5:ℝ)/2)) hxl
  have ht2ge : ((1:ℝ)) ^ 2 ≤ t ^ 2 := sq_le_of_nonneg (by norm_num : 0 ≤ (1:ℝ)) htl
  have hQ3le : ((29:ℝ)/4) ≤ x ^ 2 + t ^ 2 := by
    have : (((5:ℝ)/2)) ^ 2 + ((1:ℝ)) ^ 2 = ((29:ℝ)/4) := by norm_num
    nlinarith
  have hlogL : ((2326498257125602533:ℝ)/1174405120000000000) ≤ Real.log (x ^ 2 + t ^ 2) := by
    exact (vlog_lb_m29_4).trans (Real.log_le_log (by norm_num : 0 < ((29:ℝ)/4)) hQ3le)
  have hLDpos : 0 < ((2326498257125602533:ℝ)/1174405120000000000) := by norm_num
  -- arctan bound
  have htovx : t / x ≤ ((3:ℝ)/5) := by
    rw [div_le_iff₀ hxpos]
    have htu_le : ((3:ℝ)/2) ≤ ((3:ℝ)/5) * x := by
      calc
        ((3:ℝ)/2) = ((3:ℝ)/5) * ((5:ℝ)/2) := by norm_num
        _ ≤ ((3:ℝ)/5) * x := mul_le_mul_of_nonneg_left hxl (by norm_num : 0 ≤ ((3:ℝ)/5))
    nlinarith [htu_le]
  have hAT : Real.arctan (t / x) ≤ ((7392009:ℝ)/13671875) := (arctan_mono htovx).trans vatan_ub_m3_5
  have hθsq : (Real.arctan (t / x)) ^ 2 ≤ (((7392009:ℝ)/13671875)) ^ 2 := by
    have hθn : 0 ≤ Real.arctan (t / x) := Real.arctan_nonneg.mpr (div_nonneg (le_of_lt htpos) (le_of_lt hxpos))
    have hAn : 0 ≤ ((7392009:ℝ)/13671875) := by norm_num
    rw [sq_le_sq]
    rw [abs_of_nonneg hθn, abs_of_nonneg hAn]
    exact hAT
  have hQden : (Real.arctan (t / x)) ^ 2 / Real.log (x ^ 2 + t ^ 2) ≤
      (((7392009:ℝ)/13671875)) ^ 2 / (((2326498257125602533:ℝ)/1174405120000000000)) := by
    have h1 : (Real.arctan (t / x)) ^ 2 / Real.log (x ^ 2 + t ^ 2) ≤
        (Real.arctan (t / x)) ^ 2 / ((2326498257125602533:ℝ)/1174405120000000000) := by
      exact div_le_div_of_nonneg_left (sq_nonneg _) hLDpos (by linarith : ((2326498257125602533:ℝ)/1174405120000000000) ≤ Real.log (x ^ 2 + t ^ 2))
    have h2 : (Real.arctan (t / x)) ^ 2 / ((2326498257125602533:ℝ)/1174405120000000000) ≤ (((7392009:ℝ)/13671875)) ^ 2 / ((2326498257125602533:ℝ)/1174405120000000000) := by
      exact div_le_div_of_nonneg_right hθsq (le_of_lt hLDpos)
    exact h1.trans h2
  -- P bound
  have hP : (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) ≤ ((5803:ℝ)/31250) := by
    have hsqrt : Real.sqrt ((29:ℝ)/4) ≤ Real.sqrt (x ^ 2 + t ^ 2) := Real.sqrt_le_sqrt hQ3le
    have hd1 : (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) ≤ (1 : ℝ) / (2 * Real.sqrt ((29:ℝ)/4)) := by
      have hdenpos : 0 < 2 * Real.sqrt ((29:ℝ)/4) := by positivity
      exact div_le_div_of_nonneg_left (by norm_num : 0 ≤ (1 : ℝ)) hdenpos (by nlinarith)
    exact hd1.trans (inv_two_sqrt_le ((29:ℝ)/4) (by norm_num) ((5803:ℝ)/31250) (by norm_num) (by norm_num))
  -- S bound
  have hS : Real.log (x ^ 2 + t ^ 2) / 2 - Real.log (2 + t) ≤ (1 / 2) * ((5685145627975592301:ℝ)/2348810240000000000) - ((153784745867:ℝ)/140000000000) := by
    nlinarith [hlogU, hDL]
  exact combine x t hxpos htpos ((5685145627975592301:ℝ)/2348810240000000000) ((153784745867:ℝ)/140000000000) ((2326498257125602533:ℝ)/1174405120000000000) ((7392009:ℝ)/13671875) ((5803:ℝ)/31250) hLDpos hS hQden hP (by norm_num)

private lemma box_4_1 (x t : ℝ) (hx1 : 1 ≤ x) (hx2 : x ≤ 8) (ht : 1 ≤ t)
    (hxl : ((5:ℝ)/2) ≤ x) (hxu : x ≤ (3:ℝ)) (htl : ((3:ℝ)/2) ≤ t) (htu : t ≤ (2:ℝ)) :
    Real.log (Real.sqrt (x ^ 2 + t ^ 2)) +
        (Real.arctan (t / x)) ^ 2 / (2 * Real.log (Real.sqrt (x ^ 2 + t ^ 2))) +
        (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) ≤
      Real.log (2 + t) + (3 : ℝ) / 2 := by
  have hxpos : 0 < x := by linarith
  have htpos : 0 < t := by linarith
  have hapos : 0 < x ^ 2 + t ^ 2 := by positivity
  -- upper square bound
  have hx2le : x ^ 2 ≤ ((3:ℝ)) ^ 2 := sq_le_of_nonneg (le_of_lt hxpos) hxu
  have ht2le : t ^ 2 ≤ ((2:ℝ)) ^ 2 := sq_le_of_nonneg (le_of_lt htpos) htu
  have ha_le : x ^ 2 + t ^ 2 ≤ (13:ℝ) := by
    have : ((3:ℝ)) ^ 2 + ((2:ℝ)) ^ 2 = (13:ℝ) := by norm_num
    nlinarith
  have hlogU : Real.log (x ^ 2 + t ^ 2) ≤ ((840483062271301:ℝ)/327680000000000) := by
    exact (Real.log_le_log hapos ha_le).trans vlog_ub_m13
  -- log(2+t) lower bound
  have hDmono : Real.log (((7:ℝ)/2)) ≤ Real.log (2 + t) := by
    apply Real.log_le_log (by norm_num : 0 < ((7:ℝ)/2))
    linarith
  have hDL : ((269394135787799:ℝ)/215040000000000) ≤ Real.log (2 + t) := (vlog_lb_m7_2).trans hDmono
  -- lower square bound
  have hx2ge : (((5:ℝ)/2)) ^ 2 ≤ x ^ 2 := sq_le_of_nonneg (by norm_num : 0 ≤ ((5:ℝ)/2)) hxl
  have ht2ge : (((3:ℝ)/2)) ^ 2 ≤ t ^ 2 := sq_le_of_nonneg (by norm_num : 0 ≤ ((3:ℝ)/2)) htl
  have hQ3le : ((17:ℝ)/2) ≤ x ^ 2 + t ^ 2 := by
    have : (((5:ℝ)/2)) ^ 2 + (((3:ℝ)/2)) ^ 2 = ((17:ℝ)/2) := by norm_num
    nlinarith
  have hlogL : ((15079827951786818323:ℝ)/7046430720000000000) ≤ Real.log (x ^ 2 + t ^ 2) := by
    exact (vlog_lb_m17_2).trans (Real.log_le_log (by norm_num : 0 < ((17:ℝ)/2)) hQ3le)
  have hLDpos : 0 < ((15079827951786818323:ℝ)/7046430720000000000) := by norm_num
  -- arctan bound
  have htovx : t / x ≤ ((4:ℝ)/5) := by
    rw [div_le_iff₀ hxpos]
    have htu_le : (2:ℝ) ≤ ((4:ℝ)/5) * x := by
      calc
        (2:ℝ) = ((4:ℝ)/5) * ((5:ℝ)/2) := by norm_num
        _ ≤ ((4:ℝ)/5) * x := mul_le_mul_of_nonneg_left hxl (by norm_num : 0 ≤ ((4:ℝ)/5))
    nlinarith [htu_le]
  have hAT : Real.arctan (t / x) ≤ ((83650108:ℝ)/123046875) := (arctan_mono htovx).trans vatan_ub_m4_5
  have hθsq : (Real.arctan (t / x)) ^ 2 ≤ (((83650108:ℝ)/123046875)) ^ 2 := by
    have hθn : 0 ≤ Real.arctan (t / x) := Real.arctan_nonneg.mpr (div_nonneg (le_of_lt htpos) (le_of_lt hxpos))
    have hAn : 0 ≤ ((83650108:ℝ)/123046875) := by norm_num
    rw [sq_le_sq]
    rw [abs_of_nonneg hθn, abs_of_nonneg hAn]
    exact hAT
  have hQden : (Real.arctan (t / x)) ^ 2 / Real.log (x ^ 2 + t ^ 2) ≤
      (((83650108:ℝ)/123046875)) ^ 2 / (((15079827951786818323:ℝ)/7046430720000000000)) := by
    have h1 : (Real.arctan (t / x)) ^ 2 / Real.log (x ^ 2 + t ^ 2) ≤
        (Real.arctan (t / x)) ^ 2 / ((15079827951786818323:ℝ)/7046430720000000000) := by
      exact div_le_div_of_nonneg_left (sq_nonneg _) hLDpos (by linarith : ((15079827951786818323:ℝ)/7046430720000000000) ≤ Real.log (x ^ 2 + t ^ 2))
    have h2 : (Real.arctan (t / x)) ^ 2 / ((15079827951786818323:ℝ)/7046430720000000000) ≤ (((83650108:ℝ)/123046875)) ^ 2 / ((15079827951786818323:ℝ)/7046430720000000000) := by
      exact div_le_div_of_nonneg_right hθsq (le_of_lt hLDpos)
    exact h1.trans h2
  -- P bound
  have hP : (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) ≤ ((171499:ℝ)/1000000) := by
    have hsqrt : Real.sqrt ((17:ℝ)/2) ≤ Real.sqrt (x ^ 2 + t ^ 2) := Real.sqrt_le_sqrt hQ3le
    have hd1 : (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) ≤ (1 : ℝ) / (2 * Real.sqrt ((17:ℝ)/2)) := by
      have hdenpos : 0 < 2 * Real.sqrt ((17:ℝ)/2) := by positivity
      exact div_le_div_of_nonneg_left (by norm_num : 0 ≤ (1 : ℝ)) hdenpos (by nlinarith)
    exact hd1.trans (inv_two_sqrt_le ((17:ℝ)/2) (by norm_num) ((171499:ℝ)/1000000) (by norm_num) (by norm_num))
  -- S bound
  have hS : Real.log (x ^ 2 + t ^ 2) / 2 - Real.log (2 + t) ≤ (1 / 2) * ((840483062271301:ℝ)/327680000000000) - ((269394135787799:ℝ)/215040000000000) := by
    nlinarith [hlogU, hDL]
  exact combine x t hxpos htpos ((840483062271301:ℝ)/327680000000000) ((269394135787799:ℝ)/215040000000000) ((15079827951786818323:ℝ)/7046430720000000000) ((83650108:ℝ)/123046875) ((171499:ℝ)/1000000) hLDpos hS hQden hP (by norm_num)

private lemma box_4_2 (x t : ℝ) (hx1 : 1 ≤ x) (hx2 : x ≤ 8) (ht : 1 ≤ t)
    (hxl : ((5:ℝ)/2) ≤ x) (hxu : x ≤ (3:ℝ)) (htl : (2:ℝ) ≤ t) (htu : t ≤ (3:ℝ)) :
    Real.log (Real.sqrt (x ^ 2 + t ^ 2)) +
        (Real.arctan (t / x)) ^ 2 / (2 * Real.log (Real.sqrt (x ^ 2 + t ^ 2))) +
        (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) ≤
      Real.log (2 + t) + (3 : ℝ) / 2 := by
  have hxpos : 0 < x := by linarith
  have htpos : 0 < t := by linarith
  have hapos : 0 < x ^ 2 + t ^ 2 := by positivity
  -- upper square bound
  have hx2le : x ^ 2 ≤ ((3:ℝ)) ^ 2 := sq_le_of_nonneg (le_of_lt hxpos) hxu
  have ht2le : t ^ 2 ≤ ((3:ℝ)) ^ 2 := sq_le_of_nonneg (le_of_lt htpos) htu
  have ha_le : x ^ 2 + t ^ 2 ≤ (18:ℝ) := by
    have : ((3:ℝ)) ^ 2 + ((3:ℝ)) ^ 2 = (18:ℝ) := by norm_num
    nlinarith
  have hlogU : Real.log (x ^ 2 + t ^ 2) ≤ ((414363696311077:ℝ)/143360000000000) := by
    exact (Real.log_le_log hapos ha_le).trans vlog_ub_m18
  -- log(2+t) lower bound
  have hDmono : Real.log ((4:ℝ)) ≤ Real.log (2 + t) := by
    apply Real.log_le_log (by norm_num : 0 < (4:ℝ))
    linarith
  have hDL : ((6931471803:ℝ)/5000000000) ≤ Real.log (2 + t) := (vlog_lb_m4).trans hDmono
  -- lower square bound
  have hx2ge : (((5:ℝ)/2)) ^ 2 ≤ x ^ 2 := sq_le_of_nonneg (by norm_num : 0 ≤ ((5:ℝ)/2)) hxl
  have ht2ge : ((2:ℝ)) ^ 2 ≤ t ^ 2 := sq_le_of_nonneg (by norm_num : 0 ≤ (2:ℝ)) htl
  have hQ3le : ((41:ℝ)/4) ≤ x ^ 2 + t ^ 2 := by
    have : (((5:ℝ)/2)) ^ 2 + ((2:ℝ)) ^ 2 = ((41:ℝ)/4) := by norm_num
    nlinarith
  have hlogL : ((1399380841006865137521:ℝ)/601295421440000000000) ≤ Real.log (x ^ 2 + t ^ 2) := by
    exact (vlog_lb_m41_4).trans (Real.log_le_log (by norm_num : 0 < ((41:ℝ)/4)) hQ3le)
  have hLDpos : 0 < ((1399380841006865137521:ℝ)/601295421440000000000) := by norm_num
  -- arctan bound
  have htovx : t / x ≤ ((6:ℝ)/5) := by
    rw [div_le_iff₀ hxpos]
    have htu_le : (3:ℝ) ≤ ((6:ℝ)/5) * x := by
      calc
        (3:ℝ) = ((6:ℝ)/5) * ((5:ℝ)/2) := by norm_num
        _ ≤ ((6:ℝ)/5) * x := mul_le_mul_of_nonneg_left hxl (by norm_num : 0 ≤ ((6:ℝ)/5))
    nlinarith [htu_le]
  have hAT : Real.arctan (t / x) ≤ ((1089830801:ℝ)/1224720000) := (arctan_mono htovx).trans vatan_ub_m6_5
  have hθsq : (Real.arctan (t / x)) ^ 2 ≤ (((1089830801:ℝ)/1224720000)) ^ 2 := by
    have hθn : 0 ≤ Real.arctan (t / x) := Real.arctan_nonneg.mpr (div_nonneg (le_of_lt htpos) (le_of_lt hxpos))
    have hAn : 0 ≤ ((1089830801:ℝ)/1224720000) := by norm_num
    rw [sq_le_sq]
    rw [abs_of_nonneg hθn, abs_of_nonneg hAn]
    exact hAT
  have hQden : (Real.arctan (t / x)) ^ 2 / Real.log (x ^ 2 + t ^ 2) ≤
      (((1089830801:ℝ)/1224720000)) ^ 2 / (((1399380841006865137521:ℝ)/601295421440000000000)) := by
    have h1 : (Real.arctan (t / x)) ^ 2 / Real.log (x ^ 2 + t ^ 2) ≤
        (Real.arctan (t / x)) ^ 2 / ((1399380841006865137521:ℝ)/601295421440000000000) := by
      exact div_le_div_of_nonneg_left (sq_nonneg _) hLDpos (by linarith : ((1399380841006865137521:ℝ)/601295421440000000000) ≤ Real.log (x ^ 2 + t ^ 2))
    have h2 : (Real.arctan (t / x)) ^ 2 / ((1399380841006865137521:ℝ)/601295421440000000000) ≤ (((1089830801:ℝ)/1224720000)) ^ 2 / ((1399380841006865137521:ℝ)/601295421440000000000) := by
      exact div_le_div_of_nonneg_right hθsq (le_of_lt hLDpos)
    exact h1.trans h2
  -- P bound
  have hP : (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) ≤ ((78087:ℝ)/500000) := by
    have hsqrt : Real.sqrt ((41:ℝ)/4) ≤ Real.sqrt (x ^ 2 + t ^ 2) := Real.sqrt_le_sqrt hQ3le
    have hd1 : (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) ≤ (1 : ℝ) / (2 * Real.sqrt ((41:ℝ)/4)) := by
      have hdenpos : 0 < 2 * Real.sqrt ((41:ℝ)/4) := by positivity
      exact div_le_div_of_nonneg_left (by norm_num : 0 ≤ (1 : ℝ)) hdenpos (by nlinarith)
    exact hd1.trans (inv_two_sqrt_le ((41:ℝ)/4) (by norm_num) ((78087:ℝ)/500000) (by norm_num) (by norm_num))
  -- S bound
  have hS : Real.log (x ^ 2 + t ^ 2) / 2 - Real.log (2 + t) ≤ (1 / 2) * ((414363696311077:ℝ)/143360000000000) - ((6931471803:ℝ)/5000000000) := by
    nlinarith [hlogU, hDL]
  exact combine x t hxpos htpos ((414363696311077:ℝ)/143360000000000) ((6931471803:ℝ)/5000000000) ((1399380841006865137521:ℝ)/601295421440000000000) ((1089830801:ℝ)/1224720000) ((78087:ℝ)/500000) hLDpos hS hQden hP (by norm_num)

private lemma box_4_3 (x t : ℝ) (hx1 : 1 ≤ x) (hx2 : x ≤ 8) (ht : 1 ≤ t)
    (hxl : ((5:ℝ)/2) ≤ x) (hxu : x ≤ (3:ℝ)) (htl : (3:ℝ) ≤ t) (htu : t ≤ (4:ℝ)) :
    Real.log (Real.sqrt (x ^ 2 + t ^ 2)) +
        (Real.arctan (t / x)) ^ 2 / (2 * Real.log (Real.sqrt (x ^ 2 + t ^ 2))) +
        (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) ≤
      Real.log (2 + t) + (3 : ℝ) / 2 := by
  have hxpos : 0 < x := by linarith
  have htpos : 0 < t := by linarith
  have hapos : 0 < x ^ 2 + t ^ 2 := by positivity
  -- upper square bound
  have hx2le : x ^ 2 ≤ ((3:ℝ)) ^ 2 := sq_le_of_nonneg (le_of_lt hxpos) hxu
  have ht2le : t ^ 2 ≤ ((4:ℝ)) ^ 2 := sq_le_of_nonneg (le_of_lt htpos) htu
  have ha_le : x ^ 2 + t ^ 2 ≤ (25:ℝ) := by
    have : ((3:ℝ)) ^ 2 + ((4:ℝ)) ^ 2 = (25:ℝ) := by norm_num
    nlinarith
  have hlogU : Real.log (x ^ 2 + t ^ 2) ≤ ((40502884587069323:ℝ)/12582912000000000) := by
    exact (Real.log_le_log hapos ha_le).trans vlog_ub_m25
  -- log(2+t) lower bound
  have hDmono : Real.log ((5:ℝ)) ≤ Real.log (2 + t) := by
    apply Real.log_le_log (by norm_num : 0 < (5:ℝ))
    linarith
  have hDL : ((173046727073587:ℝ)/107520000000000) ≤ Real.log (2 + t) := (vlog_lb_m5).trans hDmono
  -- lower square bound
  have hx2ge : (((5:ℝ)/2)) ^ 2 ≤ x ^ 2 := sq_le_of_nonneg (by norm_num : 0 ≤ ((5:ℝ)/2)) hxl
  have ht2ge : ((3:ℝ)) ^ 2 ≤ t ^ 2 := sq_le_of_nonneg (by norm_num : 0 ≤ (3:ℝ)) htl
  have hQ3le : ((61:ℝ)/4) ≤ x ^ 2 + t ^ 2 := by
    have : (((5:ℝ)/2)) ^ 2 + ((3:ℝ)) ^ 2 = ((61:ℝ)/4) := by norm_num
    nlinarith
  have hlogL : ((409569294967297493757:ℝ)/150323855360000000000) ≤ Real.log (x ^ 2 + t ^ 2) := by
    exact (vlog_lb_m61_4).trans (Real.log_le_log (by norm_num : 0 < ((61:ℝ)/4)) hQ3le)
  have hLDpos : 0 < ((409569294967297493757:ℝ)/150323855360000000000) := by norm_num
  -- arctan bound
  have htovx : t / x ≤ ((8:ℝ)/5) := by
    rw [div_le_iff₀ hxpos]
    have htu_le : (4:ℝ) ≤ ((8:ℝ)/5) * x := by
      calc
        (4:ℝ) = ((8:ℝ)/5) * ((5:ℝ)/2) := by norm_num
        _ ≤ ((8:ℝ)/5) * x := mul_le_mul_of_nonneg_left hxl (by norm_num : 0 ≤ ((8:ℝ)/5))
    nlinarith [htu_le]
  have hAT : Real.arctan (t / x) ≤ ((27894742871:ℝ)/27525120000) := (arctan_mono htovx).trans vatan_ub_m8_5
  have hθsq : (Real.arctan (t / x)) ^ 2 ≤ (((27894742871:ℝ)/27525120000)) ^ 2 := by
    have hθn : 0 ≤ Real.arctan (t / x) := Real.arctan_nonneg.mpr (div_nonneg (le_of_lt htpos) (le_of_lt hxpos))
    have hAn : 0 ≤ ((27894742871:ℝ)/27525120000) := by norm_num
    rw [sq_le_sq]
    rw [abs_of_nonneg hθn, abs_of_nonneg hAn]
    exact hAT
  have hQden : (Real.arctan (t / x)) ^ 2 / Real.log (x ^ 2 + t ^ 2) ≤
      (((27894742871:ℝ)/27525120000)) ^ 2 / (((409569294967297493757:ℝ)/150323855360000000000)) := by
    have h1 : (Real.arctan (t / x)) ^ 2 / Real.log (x ^ 2 + t ^ 2) ≤
        (Real.arctan (t / x)) ^ 2 / ((409569294967297493757:ℝ)/150323855360000000000) := by
      exact div_le_div_of_nonneg_left (sq_nonneg _) hLDpos (by linarith : ((409569294967297493757:ℝ)/150323855360000000000) ≤ Real.log (x ^ 2 + t ^ 2))
    have h2 : (Real.arctan (t / x)) ^ 2 / ((409569294967297493757:ℝ)/150323855360000000000) ≤ (((27894742871:ℝ)/27525120000)) ^ 2 / ((409569294967297493757:ℝ)/150323855360000000000) := by
      exact div_le_div_of_nonneg_right hθsq (le_of_lt hLDpos)
    exact h1.trans h2
  -- P bound
  have hP : (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) ≤ ((128037:ℝ)/1000000) := by
    have hsqrt : Real.sqrt ((61:ℝ)/4) ≤ Real.sqrt (x ^ 2 + t ^ 2) := Real.sqrt_le_sqrt hQ3le
    have hd1 : (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) ≤ (1 : ℝ) / (2 * Real.sqrt ((61:ℝ)/4)) := by
      have hdenpos : 0 < 2 * Real.sqrt ((61:ℝ)/4) := by positivity
      exact div_le_div_of_nonneg_left (by norm_num : 0 ≤ (1 : ℝ)) hdenpos (by nlinarith)
    exact hd1.trans (inv_two_sqrt_le ((61:ℝ)/4) (by norm_num) ((128037:ℝ)/1000000) (by norm_num) (by norm_num))
  -- S bound
  have hS : Real.log (x ^ 2 + t ^ 2) / 2 - Real.log (2 + t) ≤ (1 / 2) * ((40502884587069323:ℝ)/12582912000000000) - ((173046727073587:ℝ)/107520000000000) := by
    nlinarith [hlogU, hDL]
  exact combine x t hxpos htpos ((40502884587069323:ℝ)/12582912000000000) ((173046727073587:ℝ)/107520000000000) ((409569294967297493757:ℝ)/150323855360000000000) ((27894742871:ℝ)/27525120000) ((128037:ℝ)/1000000) hLDpos hS hQden hP (by norm_num)

private lemma box_4_4 (x t : ℝ) (hx1 : 1 ≤ x) (hx2 : x ≤ 8) (ht : 1 ≤ t)
    (hxl : ((5:ℝ)/2) ≤ x) (hxu : x ≤ (3:ℝ)) (htl : (4:ℝ) ≤ t) (htu : t ≤ (6:ℝ)) :
    Real.log (Real.sqrt (x ^ 2 + t ^ 2)) +
        (Real.arctan (t / x)) ^ 2 / (2 * Real.log (Real.sqrt (x ^ 2 + t ^ 2))) +
        (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) ≤
      Real.log (2 + t) + (3 : ℝ) / 2 := by
  have hxpos : 0 < x := by linarith
  have htpos : 0 < t := by linarith
  have hapos : 0 < x ^ 2 + t ^ 2 := by positivity
  -- upper square bound
  have hx2le : x ^ 2 ≤ ((3:ℝ)) ^ 2 := sq_le_of_nonneg (le_of_lt hxpos) hxu
  have ht2le : t ^ 2 ≤ ((6:ℝ)) ^ 2 := sq_le_of_nonneg (le_of_lt htpos) htu
  have ha_le : x ^ 2 + t ^ 2 ≤ (45:ℝ) := by
    have : ((3:ℝ)) ^ 2 + ((6:ℝ)) ^ 2 = (45:ℝ) := by norm_num
    nlinarith
  have hlogU : Real.log (x ^ 2 + t ^ 2) ≤ ((1788257604031187017:ℝ)/469762048000000000) := by
    exact (Real.log_le_log hapos ha_le).trans vlog_ub_m45
  -- log(2+t) lower bound
  have hDmono : Real.log ((6:ℝ)) ≤ Real.log (2 + t) := by
    apply Real.log_le_log (by norm_num : 0 < (6:ℝ))
    linarith
  have hDL : ((250825351109:ℝ)/140000000000) ≤ Real.log (2 + t) := (vlog_lb_m6).trans hDmono
  -- lower square bound
  have hx2ge : (((5:ℝ)/2)) ^ 2 ≤ x ^ 2 := sq_le_of_nonneg (by norm_num : 0 ≤ ((5:ℝ)/2)) hxl
  have ht2ge : ((4:ℝ)) ^ 2 ≤ t ^ 2 := sq_le_of_nonneg (by norm_num : 0 ≤ (4:ℝ)) htl
  have hQ3le : ((89:ℝ)/4) ≤ x ^ 2 + t ^ 2 := by
    have : (((5:ℝ)/2)) ^ 2 + ((4:ℝ)) ^ 2 = ((89:ℝ)/4) := by norm_num
    nlinarith
  have hlogL : ((1432637621587863820743379:ℝ)/461794883665920000000000) ≤ Real.log (x ^ 2 + t ^ 2) := by
    exact (vlog_lb_m89_4).trans (Real.log_le_log (by norm_num : 0 < ((89:ℝ)/4)) hQ3le)
  have hLDpos : 0 < ((1432637621587863820743379:ℝ)/461794883665920000000000) := by norm_num
  -- arctan bound
  have htovx : t / x ≤ ((12:ℝ)/5) := by
    rw [div_le_iff₀ hxpos]
    have htu_le : (6:ℝ) ≤ ((12:ℝ)/5) * x := by
      calc
        (6:ℝ) = ((12:ℝ)/5) * ((5:ℝ)/2) := by norm_num
        _ ≤ ((12:ℝ)/5) * x := mul_le_mul_of_nonneg_left hxl (by norm_num : 0 ≤ ((12:ℝ)/5))
    nlinarith [htu_le]
  have hAT : Real.arctan (t / x) ≤ ((184361820653:ℝ)/156764160000) := (arctan_mono htovx).trans vatan_ub_m12_5
  have hθsq : (Real.arctan (t / x)) ^ 2 ≤ (((184361820653:ℝ)/156764160000)) ^ 2 := by
    have hθn : 0 ≤ Real.arctan (t / x) := Real.arctan_nonneg.mpr (div_nonneg (le_of_lt htpos) (le_of_lt hxpos))
    have hAn : 0 ≤ ((184361820653:ℝ)/156764160000) := by norm_num
    rw [sq_le_sq]
    rw [abs_of_nonneg hθn, abs_of_nonneg hAn]
    exact hAT
  have hQden : (Real.arctan (t / x)) ^ 2 / Real.log (x ^ 2 + t ^ 2) ≤
      (((184361820653:ℝ)/156764160000)) ^ 2 / (((1432637621587863820743379:ℝ)/461794883665920000000000)) := by
    have h1 : (Real.arctan (t / x)) ^ 2 / Real.log (x ^ 2 + t ^ 2) ≤
        (Real.arctan (t / x)) ^ 2 / ((1432637621587863820743379:ℝ)/461794883665920000000000) := by
      exact div_le_div_of_nonneg_left (sq_nonneg _) hLDpos (by linarith : ((1432637621587863820743379:ℝ)/461794883665920000000000) ≤ Real.log (x ^ 2 + t ^ 2))
    have h2 : (Real.arctan (t / x)) ^ 2 / ((1432637621587863820743379:ℝ)/461794883665920000000000) ≤ (((184361820653:ℝ)/156764160000)) ^ 2 / ((1432637621587863820743379:ℝ)/461794883665920000000000) := by
      exact div_le_div_of_nonneg_right hθsq (le_of_lt hLDpos)
    exact h1.trans h2
  -- P bound
  have hP : (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) ≤ ((53:ℝ)/500) := by
    have hsqrt : Real.sqrt ((89:ℝ)/4) ≤ Real.sqrt (x ^ 2 + t ^ 2) := Real.sqrt_le_sqrt hQ3le
    have hd1 : (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) ≤ (1 : ℝ) / (2 * Real.sqrt ((89:ℝ)/4)) := by
      have hdenpos : 0 < 2 * Real.sqrt ((89:ℝ)/4) := by positivity
      exact div_le_div_of_nonneg_left (by norm_num : 0 ≤ (1 : ℝ)) hdenpos (by nlinarith)
    exact hd1.trans (inv_two_sqrt_le ((89:ℝ)/4) (by norm_num) ((53:ℝ)/500) (by norm_num) (by norm_num))
  -- S bound
  have hS : Real.log (x ^ 2 + t ^ 2) / 2 - Real.log (2 + t) ≤ (1 / 2) * ((1788257604031187017:ℝ)/469762048000000000) - ((250825351109:ℝ)/140000000000) := by
    nlinarith [hlogU, hDL]
  exact combine x t hxpos htpos ((1788257604031187017:ℝ)/469762048000000000) ((250825351109:ℝ)/140000000000) ((1432637621587863820743379:ℝ)/461794883665920000000000) ((184361820653:ℝ)/156764160000) ((53:ℝ)/500) hLDpos hS hQden hP (by norm_num)

private lemma box_4_5 (x t : ℝ) (hx1 : 1 ≤ x) (hx2 : x ≤ 8) (ht : 1 ≤ t)
    (hxl : ((5:ℝ)/2) ≤ x) (hxu : x ≤ (3:ℝ)) (htl : (6:ℝ) ≤ t) (htu : t ≤ (9:ℝ)) :
    Real.log (Real.sqrt (x ^ 2 + t ^ 2)) +
        (Real.arctan (t / x)) ^ 2 / (2 * Real.log (Real.sqrt (x ^ 2 + t ^ 2))) +
        (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) ≤
      Real.log (2 + t) + (3 : ℝ) / 2 := by
  have hxpos : 0 < x := by linarith
  have htpos : 0 < t := by linarith
  have hapos : 0 < x ^ 2 + t ^ 2 := by positivity
  -- upper square bound
  have hx2le : x ^ 2 ≤ ((3:ℝ)) ^ 2 := sq_le_of_nonneg (le_of_lt hxpos) hxu
  have ht2le : t ^ 2 ≤ ((9:ℝ)) ^ 2 := sq_le_of_nonneg (le_of_lt htpos) htu
  have ha_le : x ^ 2 + t ^ 2 ≤ (90:ℝ) := by
    have : ((3:ℝ)) ^ 2 + ((9:ℝ)) ^ 2 = (90:ℝ) := by norm_num
    nlinarith
  have hlogU : Real.log (x ^ 2 + t ^ 2) ≤ ((10569359216246106477:ℝ)/2348810240000000000) := by
    exact (Real.log_le_log hapos ha_le).trans vlog_ub_m90
  -- log(2+t) lower bound
  have hDmono : Real.log ((8:ℝ)) ≤ Real.log (2 + t) := by
    apply Real.log_le_log (by norm_num : 0 < (8:ℝ))
    linarith
  have hDL : ((20794415409:ℝ)/10000000000) ≤ Real.log (2 + t) := (vlog_lb_m8).trans hDmono
  -- lower square bound
  have hx2ge : (((5:ℝ)/2)) ^ 2 ≤ x ^ 2 := sq_le_of_nonneg (by norm_num : 0 ≤ ((5:ℝ)/2)) hxl
  have ht2ge : ((6:ℝ)) ^ 2 ≤ t ^ 2 := sq_le_of_nonneg (by norm_num : 0 ≤ (6:ℝ)) htl
  have hQ3le : ((169:ℝ)/4) ≤ x ^ 2 + t ^ 2 := by
    have : (((5:ℝ)/2)) ^ 2 + ((6:ℝ)) ^ 2 = ((169:ℝ)/4) := by norm_num
    nlinarith
  have hlogL : ((88513327206541510586560631:ℝ)/23643898043695104000000000) ≤ Real.log (x ^ 2 + t ^ 2) := by
    exact (vlog_lb_m169_4).trans (Real.log_le_log (by norm_num : 0 < ((169:ℝ)/4)) hQ3le)
  have hLDpos : 0 < ((88513327206541510586560631:ℝ)/23643898043695104000000000) := by norm_num
  -- arctan bound
  have htovx : t / x ≤ ((18:ℝ)/5) := by
    rw [div_le_iff₀ hxpos]
    have htu_le : (9:ℝ) ≤ ((18:ℝ)/5) * x := by
      calc
        (9:ℝ) = ((18:ℝ)/5) * ((5:ℝ)/2) := by norm_num
        _ ≤ ((18:ℝ)/5) * x := mul_le_mul_of_nonneg_left hxl (by norm_num : 0 ≤ ((18:ℝ)/5))
    nlinarith [htu_le]
  have hAT : Real.arctan (t / x) ≤ ((3481610855537:ℝ)/2678462640000) := (arctan_mono htovx).trans vatan_ub_m18_5
  have hθsq : (Real.arctan (t / x)) ^ 2 ≤ (((3481610855537:ℝ)/2678462640000)) ^ 2 := by
    have hθn : 0 ≤ Real.arctan (t / x) := Real.arctan_nonneg.mpr (div_nonneg (le_of_lt htpos) (le_of_lt hxpos))
    have hAn : 0 ≤ ((3481610855537:ℝ)/2678462640000) := by norm_num
    rw [sq_le_sq]
    rw [abs_of_nonneg hθn, abs_of_nonneg hAn]
    exact hAT
  have hQden : (Real.arctan (t / x)) ^ 2 / Real.log (x ^ 2 + t ^ 2) ≤
      (((3481610855537:ℝ)/2678462640000)) ^ 2 / (((88513327206541510586560631:ℝ)/23643898043695104000000000)) := by
    have h1 : (Real.arctan (t / x)) ^ 2 / Real.log (x ^ 2 + t ^ 2) ≤
        (Real.arctan (t / x)) ^ 2 / ((88513327206541510586560631:ℝ)/23643898043695104000000000) := by
      exact div_le_div_of_nonneg_left (sq_nonneg _) hLDpos (by linarith : ((88513327206541510586560631:ℝ)/23643898043695104000000000) ≤ Real.log (x ^ 2 + t ^ 2))
    have h2 : (Real.arctan (t / x)) ^ 2 / ((88513327206541510586560631:ℝ)/23643898043695104000000000) ≤ (((3481610855537:ℝ)/2678462640000)) ^ 2 / ((88513327206541510586560631:ℝ)/23643898043695104000000000) := by
      exact div_le_div_of_nonneg_right hθsq (le_of_lt hLDpos)
    exact h1.trans h2
  -- P bound
  have hP : (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) ≤ ((19231:ℝ)/250000) := by
    have hsqrt : Real.sqrt ((169:ℝ)/4) ≤ Real.sqrt (x ^ 2 + t ^ 2) := Real.sqrt_le_sqrt hQ3le
    have hd1 : (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) ≤ (1 : ℝ) / (2 * Real.sqrt ((169:ℝ)/4)) := by
      have hdenpos : 0 < 2 * Real.sqrt ((169:ℝ)/4) := by positivity
      exact div_le_div_of_nonneg_left (by norm_num : 0 ≤ (1 : ℝ)) hdenpos (by nlinarith)
    exact hd1.trans (inv_two_sqrt_le ((169:ℝ)/4) (by norm_num) ((19231:ℝ)/250000) (by norm_num) (by norm_num))
  -- S bound
  have hS : Real.log (x ^ 2 + t ^ 2) / 2 - Real.log (2 + t) ≤ (1 / 2) * ((10569359216246106477:ℝ)/2348810240000000000) - ((20794415409:ℝ)/10000000000) := by
    nlinarith [hlogU, hDL]
  exact combine x t hxpos htpos ((10569359216246106477:ℝ)/2348810240000000000) ((20794415409:ℝ)/10000000000) ((88513327206541510586560631:ℝ)/23643898043695104000000000) ((3481610855537:ℝ)/2678462640000) ((19231:ℝ)/250000) hLDpos hS hQden hP (by norm_num)

private lemma box_4_6 (x t : ℝ) (hx1 : 1 ≤ x) (hx2 : x ≤ 8) (ht : 1 ≤ t)
    (hxl : ((5:ℝ)/2) ≤ x) (hxu : x ≤ (3:ℝ)) (htl : (9:ℝ) ≤ t) (htu : t ≤ (13:ℝ)) :
    Real.log (Real.sqrt (x ^ 2 + t ^ 2)) +
        (Real.arctan (t / x)) ^ 2 / (2 * Real.log (Real.sqrt (x ^ 2 + t ^ 2))) +
        (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) ≤
      Real.log (2 + t) + (3 : ℝ) / 2 := by
  have hxpos : 0 < x := by linarith
  have htpos : 0 < t := by linarith
  have hapos : 0 < x ^ 2 + t ^ 2 := by positivity
  -- upper square bound
  have hx2le : x ^ 2 ≤ ((3:ℝ)) ^ 2 := sq_le_of_nonneg (le_of_lt hxpos) hxu
  have ht2le : t ^ 2 ≤ ((13:ℝ)) ^ 2 := sq_le_of_nonneg (le_of_lt htpos) htu
  have ha_le : x ^ 2 + t ^ 2 ≤ (178:ℝ) := by
    have : ((3:ℝ)) ^ 2 + ((13:ℝ)) ^ 2 = (178:ℝ) := by norm_num
    nlinarith
  have hlogU : Real.log (x ^ 2 + t ^ 2) ≤ ((4673719492407519373571:ℝ)/901943132160000000000) := by
    exact (Real.log_le_log hapos ha_le).trans vlog_ub_m178
  -- log(2+t) lower bound
  have hDmono : Real.log ((11:ℝ)) ≤ Real.log (2 + t) := by
    apply Real.log_le_log (by norm_num : 0 < (11:ℝ))
    linarith
  have hDL : ((22000673184559761:ℝ)/9175040000000000) ≤ Real.log (2 + t) := (vlog_lb_m11).trans hDmono
  -- lower square bound
  have hx2ge : (((5:ℝ)/2)) ^ 2 ≤ x ^ 2 := sq_le_of_nonneg (by norm_num : 0 ≤ ((5:ℝ)/2)) hxl
  have ht2ge : ((9:ℝ)) ^ 2 ≤ t ^ 2 := sq_le_of_nonneg (by norm_num : 0 ≤ (9:ℝ)) htl
  have hQ3le : ((349:ℝ)/4) ≤ x ^ 2 + t ^ 2 := by
    have : (((5:ℝ)/2)) ^ 2 + ((9:ℝ)) ^ 2 = ((349:ℝ)/4) := by norm_num
    nlinarith
  have hlogL : ((45081217144194123531113183697:ℝ)/10088063165309911040000000000) ≤ Real.log (x ^ 2 + t ^ 2) := by
    exact (vlog_lb_m349_4).trans (Real.log_le_log (by norm_num : 0 < ((349:ℝ)/4)) hQ3le)
  have hLDpos : 0 < ((45081217144194123531113183697:ℝ)/10088063165309911040000000000) := by norm_num
  -- arctan bound
  have htovx : t / x ≤ ((26:ℝ)/5) := by
    rw [div_le_iff₀ hxpos]
    have htu_le : (13:ℝ) ≤ ((26:ℝ)/5) * x := by
      calc
        (13:ℝ) = ((26:ℝ)/5) * ((5:ℝ)/2) := by norm_num
        _ ≤ ((26:ℝ)/5) * x := mul_le_mul_of_nonneg_left hxl (by norm_num : 0 ≤ ((26:ℝ)/5))
    nlinarith [htu_le]
  have hAT : Real.arctan (t / x) ≤ ((145561734567923:ℝ)/105417508560000) := (arctan_mono htovx).trans vatan_ub_m26_5
  have hθsq : (Real.arctan (t / x)) ^ 2 ≤ (((145561734567923:ℝ)/105417508560000)) ^ 2 := by
    have hθn : 0 ≤ Real.arctan (t / x) := Real.arctan_nonneg.mpr (div_nonneg (le_of_lt htpos) (le_of_lt hxpos))
    have hAn : 0 ≤ ((145561734567923:ℝ)/105417508560000) := by norm_num
    rw [sq_le_sq]
    rw [abs_of_nonneg hθn, abs_of_nonneg hAn]
    exact hAT
  have hQden : (Real.arctan (t / x)) ^ 2 / Real.log (x ^ 2 + t ^ 2) ≤
      (((145561734567923:ℝ)/105417508560000)) ^ 2 / (((45081217144194123531113183697:ℝ)/10088063165309911040000000000)) := by
    have h1 : (Real.arctan (t / x)) ^ 2 / Real.log (x ^ 2 + t ^ 2) ≤
        (Real.arctan (t / x)) ^ 2 / ((45081217144194123531113183697:ℝ)/10088063165309911040000000000) := by
      exact div_le_div_of_nonneg_left (sq_nonneg _) hLDpos (by linarith : ((45081217144194123531113183697:ℝ)/10088063165309911040000000000) ≤ Real.log (x ^ 2 + t ^ 2))
    have h2 : (Real.arctan (t / x)) ^ 2 / ((45081217144194123531113183697:ℝ)/10088063165309911040000000000) ≤ (((145561734567923:ℝ)/105417508560000)) ^ 2 / ((45081217144194123531113183697:ℝ)/10088063165309911040000000000) := by
      exact div_le_div_of_nonneg_right hθsq (le_of_lt hLDpos)
    exact h1.trans h2
  -- P bound
  have hP : (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) ≤ ((53529:ℝ)/1000000) := by
    have hsqrt : Real.sqrt ((349:ℝ)/4) ≤ Real.sqrt (x ^ 2 + t ^ 2) := Real.sqrt_le_sqrt hQ3le
    have hd1 : (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) ≤ (1 : ℝ) / (2 * Real.sqrt ((349:ℝ)/4)) := by
      have hdenpos : 0 < 2 * Real.sqrt ((349:ℝ)/4) := by positivity
      exact div_le_div_of_nonneg_left (by norm_num : 0 ≤ (1 : ℝ)) hdenpos (by nlinarith)
    exact hd1.trans (inv_two_sqrt_le ((349:ℝ)/4) (by norm_num) ((53529:ℝ)/1000000) (by norm_num) (by norm_num))
  -- S bound
  have hS : Real.log (x ^ 2 + t ^ 2) / 2 - Real.log (2 + t) ≤ (1 / 2) * ((4673719492407519373571:ℝ)/901943132160000000000) - ((22000673184559761:ℝ)/9175040000000000) := by
    nlinarith [hlogU, hDL]
  exact combine x t hxpos htpos ((4673719492407519373571:ℝ)/901943132160000000000) ((22000673184559761:ℝ)/9175040000000000) ((45081217144194123531113183697:ℝ)/10088063165309911040000000000) ((145561734567923:ℝ)/105417508560000) ((53529:ℝ)/1000000) hLDpos hS hQden hP (by norm_num)

private lemma box_4_7 (x t : ℝ) (hx1 : 1 ≤ x) (hx2 : x ≤ 8) (ht : 1 ≤ t)
    (hxl : ((5:ℝ)/2) ≤ x) (hxu : x ≤ (3:ℝ)) (htl : (13:ℝ) ≤ t) (htu : t ≤ (15:ℝ)) :
    Real.log (Real.sqrt (x ^ 2 + t ^ 2)) +
        (Real.arctan (t / x)) ^ 2 / (2 * Real.log (Real.sqrt (x ^ 2 + t ^ 2))) +
        (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) ≤
      Real.log (2 + t) + (3 : ℝ) / 2 := by
  have hxpos : 0 < x := by linarith
  have htpos : 0 < t := by linarith
  have hapos : 0 < x ^ 2 + t ^ 2 := by positivity
  -- upper square bound
  have hx2le : x ^ 2 ≤ ((3:ℝ)) ^ 2 := sq_le_of_nonneg (le_of_lt hxpos) hxu
  have ht2le : t ^ 2 ≤ ((15:ℝ)) ^ 2 := sq_le_of_nonneg (le_of_lt htpos) htu
  have ha_le : x ^ 2 + t ^ 2 ≤ (234:ℝ) := by
    have : ((3:ℝ)) ^ 2 + ((15:ℝ)) ^ 2 = (234:ℝ) := by norm_num
    nlinarith
  have hlogU : Real.log (x ^ 2 + t ^ 2) ≤ ((468608516217129061813:ℝ)/85899345920000000000) := by
    exact (Real.log_le_log hapos ha_le).trans vlog_ub_m234
  -- log(2+t) lower bound
  have hDmono : Real.log ((15:ℝ)) ≤ Real.log (2 + t) := by
    apply Real.log_le_log (by norm_num : 0 < (15:ℝ))
    linarith
  have hDL : ((24846468902980723:ℝ)/9175040000000000) ≤ Real.log (2 + t) := (vlog_lb_m15).trans hDmono
  -- lower square bound
  have hx2ge : (((5:ℝ)/2)) ^ 2 ≤ x ^ 2 := sq_le_of_nonneg (by norm_num : 0 ≤ ((5:ℝ)/2)) hxl
  have ht2ge : ((13:ℝ)) ^ 2 ≤ t ^ 2 := sq_le_of_nonneg (by norm_num : 0 ≤ (13:ℝ)) htl
  have hQ3le : ((701:ℝ)/4) ≤ x ^ 2 + t ^ 2 := by
    have : (((5:ℝ)/2)) ^ 2 + ((13:ℝ)) ^ 2 = ((701:ℝ)/4) := by norm_num
    nlinarith
  have hlogL : ((1905992455504679367682006905447:ℝ)/368934881474191032320000000000) ≤ Real.log (x ^ 2 + t ^ 2) := by
    exact (vlog_lb_m701_4).trans (Real.log_le_log (by norm_num : 0 < ((701:ℝ)/4)) hQ3le)
  have hLDpos : 0 < ((1905992455504679367682006905447:ℝ)/368934881474191032320000000000) := by norm_num
  -- arctan bound
  have htovx : t / x ≤ (6:ℝ) := by
    rw [div_le_iff₀ hxpos]
    have htu_le : (15:ℝ) ≤ (6:ℝ) * x := by
      calc
        (15:ℝ) = (6:ℝ) * ((5:ℝ)/2) := by norm_num
        _ ≤ (6:ℝ) * x := mul_le_mul_of_nonneg_left hxl (by norm_num : 0 ≤ (6:ℝ))
    nlinarith [htu_le]
  have hAT : Real.arctan (t / x) ≤ ((1721529301:ℝ)/1224720000) := (arctan_mono htovx).trans vatan_ub_m6
  have hθsq : (Real.arctan (t / x)) ^ 2 ≤ (((1721529301:ℝ)/1224720000)) ^ 2 := by
    have hθn : 0 ≤ Real.arctan (t / x) := Real.arctan_nonneg.mpr (div_nonneg (le_of_lt htpos) (le_of_lt hxpos))
    have hAn : 0 ≤ ((1721529301:ℝ)/1224720000) := by norm_num
    rw [sq_le_sq]
    rw [abs_of_nonneg hθn, abs_of_nonneg hAn]
    exact hAT
  have hQden : (Real.arctan (t / x)) ^ 2 / Real.log (x ^ 2 + t ^ 2) ≤
      (((1721529301:ℝ)/1224720000)) ^ 2 / (((1905992455504679367682006905447:ℝ)/368934881474191032320000000000)) := by
    have h1 : (Real.arctan (t / x)) ^ 2 / Real.log (x ^ 2 + t ^ 2) ≤
        (Real.arctan (t / x)) ^ 2 / ((1905992455504679367682006905447:ℝ)/368934881474191032320000000000) := by
      exact div_le_div_of_nonneg_left (sq_nonneg _) hLDpos (by linarith : ((1905992455504679367682006905447:ℝ)/368934881474191032320000000000) ≤ Real.log (x ^ 2 + t ^ 2))
    have h2 : (Real.arctan (t / x)) ^ 2 / ((1905992455504679367682006905447:ℝ)/368934881474191032320000000000) ≤ (((1721529301:ℝ)/1224720000)) ^ 2 / ((1905992455504679367682006905447:ℝ)/368934881474191032320000000000) := by
      exact div_le_div_of_nonneg_right hθsq (le_of_lt hLDpos)
    exact h1.trans h2
  -- P bound
  have hP : (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) ≤ ((3777:ℝ)/100000) := by
    have hsqrt : Real.sqrt ((701:ℝ)/4) ≤ Real.sqrt (x ^ 2 + t ^ 2) := Real.sqrt_le_sqrt hQ3le
    have hd1 : (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) ≤ (1 : ℝ) / (2 * Real.sqrt ((701:ℝ)/4)) := by
      have hdenpos : 0 < 2 * Real.sqrt ((701:ℝ)/4) := by positivity
      exact div_le_div_of_nonneg_left (by norm_num : 0 ≤ (1 : ℝ)) hdenpos (by nlinarith)
    exact hd1.trans (inv_two_sqrt_le ((701:ℝ)/4) (by norm_num) ((3777:ℝ)/100000) (by norm_num) (by norm_num))
  -- S bound
  have hS : Real.log (x ^ 2 + t ^ 2) / 2 - Real.log (2 + t) ≤ (1 / 2) * ((468608516217129061813:ℝ)/85899345920000000000) - ((24846468902980723:ℝ)/9175040000000000) := by
    nlinarith [hlogU, hDL]
  exact combine x t hxpos htpos ((468608516217129061813:ℝ)/85899345920000000000) ((24846468902980723:ℝ)/9175040000000000) ((1905992455504679367682006905447:ℝ)/368934881474191032320000000000) ((1721529301:ℝ)/1224720000) ((3777:ℝ)/100000) hLDpos hS hQden hP (by norm_num)

private lemma box_5_0 (x t : ℝ) (hx1 : 1 ≤ x) (hx2 : x ≤ 8) (ht : 1 ≤ t)
    (hxl : (3:ℝ) ≤ x) (hxu : x ≤ (4:ℝ)) (htl : (1:ℝ) ≤ t) (htu : t ≤ ((3:ℝ)/2)) :
    Real.log (Real.sqrt (x ^ 2 + t ^ 2)) +
        (Real.arctan (t / x)) ^ 2 / (2 * Real.log (Real.sqrt (x ^ 2 + t ^ 2))) +
        (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) ≤
      Real.log (2 + t) + (3 : ℝ) / 2 := by
  have hxpos : 0 < x := by linarith
  have htpos : 0 < t := by linarith
  have hapos : 0 < x ^ 2 + t ^ 2 := by positivity
  -- upper square bound
  have hx2le : x ^ 2 ≤ ((4:ℝ)) ^ 2 := sq_le_of_nonneg (le_of_lt hxpos) hxu
  have ht2le : t ^ 2 ≤ (((3:ℝ)/2)) ^ 2 := sq_le_of_nonneg (le_of_lt htpos) htu
  have ha_le : x ^ 2 + t ^ 2 ≤ ((73:ℝ)/4) := by
    have : ((4:ℝ)) ^ 2 + (((3:ℝ)/2)) ^ 2 = ((73:ℝ)/4) := by norm_num
    nlinarith
  have hlogU : Real.log (x ^ 2 + t ^ 2) ≤ ((873130588261786893329:ℝ)/300647710720000000000) := by
    exact (Real.log_le_log hapos ha_le).trans vlog_ub_m73_4
  -- log(2+t) lower bound
  have hDmono : Real.log ((3:ℝ)) ≤ Real.log (2 + t) := by
    apply Real.log_le_log (by norm_num : 0 < (3:ℝ))
    linarith
  have hDL : ((153784745867:ℝ)/140000000000) ≤ Real.log (2 + t) := (vlog_lb_m3).trans hDmono
  -- lower square bound
  have hx2ge : ((3:ℝ)) ^ 2 ≤ x ^ 2 := sq_le_of_nonneg (by norm_num : 0 ≤ (3:ℝ)) hxl
  have ht2ge : ((1:ℝ)) ^ 2 ≤ t ^ 2 := sq_le_of_nonneg (by norm_num : 0 ≤ (1:ℝ)) htl
  have hQ3le : (10:ℝ) ≤ x ^ 2 + t ^ 2 := by
    have : ((3:ℝ)) ^ 2 + ((1:ℝ)) ^ 2 = (10:ℝ) := by norm_num
    nlinarith
  have hlogL : ((247573911899443:ℝ)/107520000000000) ≤ Real.log (x ^ 2 + t ^ 2) := by
    exact (vlog_lb_m10).trans (Real.log_le_log (by norm_num : 0 < (10:ℝ)) hQ3le)
  have hLDpos : 0 < ((247573911899443:ℝ)/107520000000000) := by norm_num
  -- arctan bound
  have htovx : t / x ≤ ((1:ℝ)/2) := by
    rw [div_le_iff₀ hxpos]
    have htu_le : ((3:ℝ)/2) ≤ ((1:ℝ)/2) * x := by
      calc
        ((3:ℝ)/2) = ((1:ℝ)/2) * (3:ℝ) := by norm_num
        _ ≤ ((1:ℝ)/2) * x := mul_le_mul_of_nonneg_left hxl (by norm_num : 0 ≤ ((1:ℝ)/2))
    nlinarith [htu_le]
  have hAT : Real.arctan (t / x) ≤ ((74783:ℝ)/161280) := (arctan_mono htovx).trans vatan_ub_m1_2
  have hθsq : (Real.arctan (t / x)) ^ 2 ≤ (((74783:ℝ)/161280)) ^ 2 := by
    have hθn : 0 ≤ Real.arctan (t / x) := Real.arctan_nonneg.mpr (div_nonneg (le_of_lt htpos) (le_of_lt hxpos))
    have hAn : 0 ≤ ((74783:ℝ)/161280) := by norm_num
    rw [sq_le_sq]
    rw [abs_of_nonneg hθn, abs_of_nonneg hAn]
    exact hAT
  have hQden : (Real.arctan (t / x)) ^ 2 / Real.log (x ^ 2 + t ^ 2) ≤
      (((74783:ℝ)/161280)) ^ 2 / (((247573911899443:ℝ)/107520000000000)) := by
    have h1 : (Real.arctan (t / x)) ^ 2 / Real.log (x ^ 2 + t ^ 2) ≤
        (Real.arctan (t / x)) ^ 2 / ((247573911899443:ℝ)/107520000000000) := by
      exact div_le_div_of_nonneg_left (sq_nonneg _) hLDpos (by linarith : ((247573911899443:ℝ)/107520000000000) ≤ Real.log (x ^ 2 + t ^ 2))
    have h2 : (Real.arctan (t / x)) ^ 2 / ((247573911899443:ℝ)/107520000000000) ≤ (((74783:ℝ)/161280)) ^ 2 / ((247573911899443:ℝ)/107520000000000) := by
      exact div_le_div_of_nonneg_right hθsq (le_of_lt hLDpos)
    exact h1.trans h2
  -- P bound
  have hP : (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) ≤ ((79057:ℝ)/500000) := by
    have hsqrt : Real.sqrt (10:ℝ) ≤ Real.sqrt (x ^ 2 + t ^ 2) := Real.sqrt_le_sqrt hQ3le
    have hd1 : (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) ≤ (1 : ℝ) / (2 * Real.sqrt (10:ℝ)) := by
      have hdenpos : 0 < 2 * Real.sqrt (10:ℝ) := by positivity
      exact div_le_div_of_nonneg_left (by norm_num : 0 ≤ (1 : ℝ)) hdenpos (by nlinarith)
    exact hd1.trans (inv_two_sqrt_le (10:ℝ) (by norm_num) ((79057:ℝ)/500000) (by norm_num) (by norm_num))
  -- S bound
  have hS : Real.log (x ^ 2 + t ^ 2) / 2 - Real.log (2 + t) ≤ (1 / 2) * ((873130588261786893329:ℝ)/300647710720000000000) - ((153784745867:ℝ)/140000000000) := by
    nlinarith [hlogU, hDL]
  exact combine x t hxpos htpos ((873130588261786893329:ℝ)/300647710720000000000) ((153784745867:ℝ)/140000000000) ((247573911899443:ℝ)/107520000000000) ((74783:ℝ)/161280) ((79057:ℝ)/500000) hLDpos hS hQden hP (by norm_num)

private lemma box_5_1 (x t : ℝ) (hx1 : 1 ≤ x) (hx2 : x ≤ 8) (ht : 1 ≤ t)
    (hxl : (3:ℝ) ≤ x) (hxu : x ≤ (4:ℝ)) (htl : ((3:ℝ)/2) ≤ t) (htu : t ≤ (2:ℝ)) :
    Real.log (Real.sqrt (x ^ 2 + t ^ 2)) +
        (Real.arctan (t / x)) ^ 2 / (2 * Real.log (Real.sqrt (x ^ 2 + t ^ 2))) +
        (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) ≤
      Real.log (2 + t) + (3 : ℝ) / 2 := by
  have hxpos : 0 < x := by linarith
  have htpos : 0 < t := by linarith
  have hapos : 0 < x ^ 2 + t ^ 2 := by positivity
  -- upper square bound
  have hx2le : x ^ 2 ≤ ((4:ℝ)) ^ 2 := sq_le_of_nonneg (le_of_lt hxpos) hxu
  have ht2le : t ^ 2 ≤ ((2:ℝ)) ^ 2 := sq_le_of_nonneg (le_of_lt htpos) htu
  have ha_le : x ^ 2 + t ^ 2 ≤ (20:ℝ) := by
    have : ((4:ℝ)) ^ 2 + ((2:ℝ)) ^ 2 = (20:ℝ) := by norm_num
    nlinarith
  have hlogU : Real.log (x ^ 2 + t ^ 2) ≤ ((10065665688077:ℝ)/3360000000000) := by
    exact (Real.log_le_log hapos ha_le).trans vlog_ub_m20
  -- log(2+t) lower bound
  have hDmono : Real.log (((7:ℝ)/2)) ≤ Real.log (2 + t) := by
    apply Real.log_le_log (by norm_num : 0 < ((7:ℝ)/2))
    linarith
  have hDL : ((269394135787799:ℝ)/215040000000000) ≤ Real.log (2 + t) := (vlog_lb_m7_2).trans hDmono
  -- lower square bound
  have hx2ge : ((3:ℝ)) ^ 2 ≤ x ^ 2 := sq_le_of_nonneg (by norm_num : 0 ≤ (3:ℝ)) hxl
  have ht2ge : (((3:ℝ)/2)) ^ 2 ≤ t ^ 2 := sq_le_of_nonneg (by norm_num : 0 ≤ ((3:ℝ)/2)) htl
  have hQ3le : ((45:ℝ)/4) ≤ x ^ 2 + t ^ 2 := by
    have : ((3:ℝ)) ^ 2 + (((3:ℝ)/2)) ^ 2 = ((45:ℝ)/4) := by norm_num
    nlinarith
  have hlogL : ((1455341517017552637521:ℝ)/601295421440000000000) ≤ Real.log (x ^ 2 + t ^ 2) := by
    exact (vlog_lb_m45_4).trans (Real.log_le_log (by norm_num : 0 < ((45:ℝ)/4)) hQ3le)
  have hLDpos : 0 < ((1455341517017552637521:ℝ)/601295421440000000000) := by norm_num
  -- arctan bound
  have htovx : t / x ≤ ((2:ℝ)/3) := by
    rw [div_le_iff₀ hxpos]
    have htu_le : (2:ℝ) ≤ ((2:ℝ)/3) * x := by
      calc
        (2:ℝ) = ((2:ℝ)/3) * (3:ℝ) := by norm_num
        _ ≤ ((2:ℝ)/3) * x := mul_le_mul_of_nonneg_left hxl (by norm_num : 0 ≤ ((2:ℝ)/3))
    nlinarith [htu_le]
  have hAT : Real.arctan (t / x) ≤ ((3650446:ℝ)/6200145) := (arctan_mono htovx).trans vatan_ub_m2_3
  have hθsq : (Real.arctan (t / x)) ^ 2 ≤ (((3650446:ℝ)/6200145)) ^ 2 := by
    have hθn : 0 ≤ Real.arctan (t / x) := Real.arctan_nonneg.mpr (div_nonneg (le_of_lt htpos) (le_of_lt hxpos))
    have hAn : 0 ≤ ((3650446:ℝ)/6200145) := by norm_num
    rw [sq_le_sq]
    rw [abs_of_nonneg hθn, abs_of_nonneg hAn]
    exact hAT
  have hQden : (Real.arctan (t / x)) ^ 2 / Real.log (x ^ 2 + t ^ 2) ≤
      (((3650446:ℝ)/6200145)) ^ 2 / (((1455341517017552637521:ℝ)/601295421440000000000)) := by
    have h1 : (Real.arctan (t / x)) ^ 2 / Real.log (x ^ 2 + t ^ 2) ≤
        (Real.arctan (t / x)) ^ 2 / ((1455341517017552637521:ℝ)/601295421440000000000) := by
      exact div_le_div_of_nonneg_left (sq_nonneg _) hLDpos (by linarith : ((1455341517017552637521:ℝ)/601295421440000000000) ≤ Real.log (x ^ 2 + t ^ 2))
    have h2 : (Real.arctan (t / x)) ^ 2 / ((1455341517017552637521:ℝ)/601295421440000000000) ≤ (((3650446:ℝ)/6200145)) ^ 2 / ((1455341517017552637521:ℝ)/601295421440000000000) := by
      exact div_le_div_of_nonneg_right hθsq (le_of_lt hLDpos)
    exact h1.trans h2
  -- P bound
  have hP : (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) ≤ ((9317:ℝ)/62500) := by
    have hsqrt : Real.sqrt ((45:ℝ)/4) ≤ Real.sqrt (x ^ 2 + t ^ 2) := Real.sqrt_le_sqrt hQ3le
    have hd1 : (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) ≤ (1 : ℝ) / (2 * Real.sqrt ((45:ℝ)/4)) := by
      have hdenpos : 0 < 2 * Real.sqrt ((45:ℝ)/4) := by positivity
      exact div_le_div_of_nonneg_left (by norm_num : 0 ≤ (1 : ℝ)) hdenpos (by nlinarith)
    exact hd1.trans (inv_two_sqrt_le ((45:ℝ)/4) (by norm_num) ((9317:ℝ)/62500) (by norm_num) (by norm_num))
  -- S bound
  have hS : Real.log (x ^ 2 + t ^ 2) / 2 - Real.log (2 + t) ≤ (1 / 2) * ((10065665688077:ℝ)/3360000000000) - ((269394135787799:ℝ)/215040000000000) := by
    nlinarith [hlogU, hDL]
  exact combine x t hxpos htpos ((10065665688077:ℝ)/3360000000000) ((269394135787799:ℝ)/215040000000000) ((1455341517017552637521:ℝ)/601295421440000000000) ((3650446:ℝ)/6200145) ((9317:ℝ)/62500) hLDpos hS hQden hP (by norm_num)

private lemma box_5_2 (x t : ℝ) (hx1 : 1 ≤ x) (hx2 : x ≤ 8) (ht : 1 ≤ t)
    (hxl : (3:ℝ) ≤ x) (hxu : x ≤ (4:ℝ)) (htl : (2:ℝ) ≤ t) (htu : t ≤ (3:ℝ)) :
    Real.log (Real.sqrt (x ^ 2 + t ^ 2)) +
        (Real.arctan (t / x)) ^ 2 / (2 * Real.log (Real.sqrt (x ^ 2 + t ^ 2))) +
        (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) ≤
      Real.log (2 + t) + (3 : ℝ) / 2 := by
  have hxpos : 0 < x := by linarith
  have htpos : 0 < t := by linarith
  have hapos : 0 < x ^ 2 + t ^ 2 := by positivity
  -- upper square bound
  have hx2le : x ^ 2 ≤ ((4:ℝ)) ^ 2 := sq_le_of_nonneg (le_of_lt hxpos) hxu
  have ht2le : t ^ 2 ≤ ((3:ℝ)) ^ 2 := sq_le_of_nonneg (le_of_lt htpos) htu
  have ha_le : x ^ 2 + t ^ 2 ≤ (25:ℝ) := by
    have : ((4:ℝ)) ^ 2 + ((3:ℝ)) ^ 2 = (25:ℝ) := by norm_num
    nlinarith
  have hlogU : Real.log (x ^ 2 + t ^ 2) ≤ ((40502884587069323:ℝ)/12582912000000000) := by
    exact (Real.log_le_log hapos ha_le).trans vlog_ub_m25
  -- log(2+t) lower bound
  have hDmono : Real.log ((4:ℝ)) ≤ Real.log (2 + t) := by
    apply Real.log_le_log (by norm_num : 0 < (4:ℝ))
    linarith
  have hDL : ((6931471803:ℝ)/5000000000) ≤ Real.log (2 + t) := (vlog_lb_m4).trans hDmono
  -- lower square bound
  have hx2ge : ((3:ℝ)) ^ 2 ≤ x ^ 2 := sq_le_of_nonneg (by norm_num : 0 ≤ (3:ℝ)) hxl
  have ht2ge : ((2:ℝ)) ^ 2 ≤ t ^ 2 := sq_le_of_nonneg (by norm_num : 0 ≤ (2:ℝ)) htl
  have hQ3le : (13:ℝ) ≤ x ^ 2 + t ^ 2 := by
    have : ((3:ℝ)) ^ 2 + ((2:ℝ)) ^ 2 = (13:ℝ) := by norm_num
    nlinarith
  have hlogL : ((23533504367824473:ℝ)/9175040000000000) ≤ Real.log (x ^ 2 + t ^ 2) := by
    exact (vlog_lb_m13).trans (Real.log_le_log (by norm_num : 0 < (13:ℝ)) hQ3le)
  have hLDpos : 0 < ((23533504367824473:ℝ)/9175040000000000) := by norm_num
  -- arctan bound
  have htovx : t / x ≤ (1:ℝ) := by
    rw [div_le_iff₀ hxpos]
    have htu_le : (3:ℝ) ≤ (1:ℝ) * x := by
      calc
        (3:ℝ) = (1:ℝ) * (3:ℝ) := by norm_num
        _ ≤ (1:ℝ) * x := mul_le_mul_of_nonneg_left hxl (by norm_num : 0 ≤ (1:ℝ))
    nlinarith [htu_le]
  have hAT : Real.arctan (t / x) ≤ ((263:ℝ)/315) := (arctan_mono htovx).trans vatan_ub_m1
  have hθsq : (Real.arctan (t / x)) ^ 2 ≤ (((263:ℝ)/315)) ^ 2 := by
    have hθn : 0 ≤ Real.arctan (t / x) := Real.arctan_nonneg.mpr (div_nonneg (le_of_lt htpos) (le_of_lt hxpos))
    have hAn : 0 ≤ ((263:ℝ)/315) := by norm_num
    rw [sq_le_sq]
    rw [abs_of_nonneg hθn, abs_of_nonneg hAn]
    exact hAT
  have hQden : (Real.arctan (t / x)) ^ 2 / Real.log (x ^ 2 + t ^ 2) ≤
      (((263:ℝ)/315)) ^ 2 / (((23533504367824473:ℝ)/9175040000000000)) := by
    have h1 : (Real.arctan (t / x)) ^ 2 / Real.log (x ^ 2 + t ^ 2) ≤
        (Real.arctan (t / x)) ^ 2 / ((23533504367824473:ℝ)/9175040000000000) := by
      exact div_le_div_of_nonneg_left (sq_nonneg _) hLDpos (by linarith : ((23533504367824473:ℝ)/9175040000000000) ≤ Real.log (x ^ 2 + t ^ 2))
    have h2 : (Real.arctan (t / x)) ^ 2 / ((23533504367824473:ℝ)/9175040000000000) ≤ (((263:ℝ)/315)) ^ 2 / ((23533504367824473:ℝ)/9175040000000000) := by
      exact div_le_div_of_nonneg_right hθsq (le_of_lt hLDpos)
    exact h1.trans h2
  -- P bound
  have hP : (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) ≤ ((34669:ℝ)/250000) := by
    have hsqrt : Real.sqrt (13:ℝ) ≤ Real.sqrt (x ^ 2 + t ^ 2) := Real.sqrt_le_sqrt hQ3le
    have hd1 : (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) ≤ (1 : ℝ) / (2 * Real.sqrt (13:ℝ)) := by
      have hdenpos : 0 < 2 * Real.sqrt (13:ℝ) := by positivity
      exact div_le_div_of_nonneg_left (by norm_num : 0 ≤ (1 : ℝ)) hdenpos (by nlinarith)
    exact hd1.trans (inv_two_sqrt_le (13:ℝ) (by norm_num) ((34669:ℝ)/250000) (by norm_num) (by norm_num))
  -- S bound
  have hS : Real.log (x ^ 2 + t ^ 2) / 2 - Real.log (2 + t) ≤ (1 / 2) * ((40502884587069323:ℝ)/12582912000000000) - ((6931471803:ℝ)/5000000000) := by
    nlinarith [hlogU, hDL]
  exact combine x t hxpos htpos ((40502884587069323:ℝ)/12582912000000000) ((6931471803:ℝ)/5000000000) ((23533504367824473:ℝ)/9175040000000000) ((263:ℝ)/315) ((34669:ℝ)/250000) hLDpos hS hQden hP (by norm_num)

private lemma box_5_3 (x t : ℝ) (hx1 : 1 ≤ x) (hx2 : x ≤ 8) (ht : 1 ≤ t)
    (hxl : (3:ℝ) ≤ x) (hxu : x ≤ (4:ℝ)) (htl : (3:ℝ) ≤ t) (htu : t ≤ (4:ℝ)) :
    Real.log (Real.sqrt (x ^ 2 + t ^ 2)) +
        (Real.arctan (t / x)) ^ 2 / (2 * Real.log (Real.sqrt (x ^ 2 + t ^ 2))) +
        (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) ≤
      Real.log (2 + t) + (3 : ℝ) / 2 := by
  have hxpos : 0 < x := by linarith
  have htpos : 0 < t := by linarith
  have hapos : 0 < x ^ 2 + t ^ 2 := by positivity
  -- upper square bound
  have hx2le : x ^ 2 ≤ ((4:ℝ)) ^ 2 := sq_le_of_nonneg (le_of_lt hxpos) hxu
  have ht2le : t ^ 2 ≤ ((4:ℝ)) ^ 2 := sq_le_of_nonneg (le_of_lt htpos) htu
  have ha_le : x ^ 2 + t ^ 2 ≤ (32:ℝ) := by
    have : ((4:ℝ)) ^ 2 + ((4:ℝ)) ^ 2 = (32:ℝ) := by norm_num
    nlinarith
  have hlogU : Real.log (x ^ 2 + t ^ 2) ≤ ((108304247:ℝ)/31250000) := by
    exact (Real.log_le_log hapos ha_le).trans vlog_ub_m32
  -- log(2+t) lower bound
  have hDmono : Real.log ((5:ℝ)) ≤ Real.log (2 + t) := by
    apply Real.log_le_log (by norm_num : 0 < (5:ℝ))
    linarith
  have hDL : ((173046727073587:ℝ)/107520000000000) ≤ Real.log (2 + t) := (vlog_lb_m5).trans hDmono
  -- lower square bound
  have hx2ge : ((3:ℝ)) ^ 2 ≤ x ^ 2 := sq_le_of_nonneg (by norm_num : 0 ≤ (3:ℝ)) hxl
  have ht2ge : ((3:ℝ)) ^ 2 ≤ t ^ 2 := sq_le_of_nonneg (by norm_num : 0 ≤ (3:ℝ)) htl
  have hQ3le : (18:ℝ) ≤ x ^ 2 + t ^ 2 := by
    have : ((3:ℝ)) ^ 2 + ((3:ℝ)) ^ 2 = (18:ℝ) := by norm_num
    nlinarith
  have hlogL : ((26519276477199473:ℝ)/9175040000000000) ≤ Real.log (x ^ 2 + t ^ 2) := by
    exact (vlog_lb_m18).trans (Real.log_le_log (by norm_num : 0 < (18:ℝ)) hQ3le)
  have hLDpos : 0 < ((26519276477199473:ℝ)/9175040000000000) := by norm_num
  -- arctan bound
  have htovx : t / x ≤ ((4:ℝ)/3) := by
    rw [div_le_iff₀ hxpos]
    have htu_le : (4:ℝ) ≤ ((4:ℝ)/3) * x := by
      calc
        (4:ℝ) = ((4:ℝ)/3) * (3:ℝ) := by norm_num
        _ ≤ ((4:ℝ)/3) * x := mul_le_mul_of_nonneg_left hxl (by norm_num : 0 ≤ ((4:ℝ)/3))
    nlinarith [htu_le]
  have hAT : Real.arctan (t / x) ≤ ((66879819:ℝ)/71680000) := (arctan_mono htovx).trans vatan_ub_m4_3
  have hθsq : (Real.arctan (t / x)) ^ 2 ≤ (((66879819:ℝ)/71680000)) ^ 2 := by
    have hθn : 0 ≤ Real.arctan (t / x) := Real.arctan_nonneg.mpr (div_nonneg (le_of_lt htpos) (le_of_lt hxpos))
    have hAn : 0 ≤ ((66879819:ℝ)/71680000) := by norm_num
    rw [sq_le_sq]
    rw [abs_of_nonneg hθn, abs_of_nonneg hAn]
    exact hAT
  have hQden : (Real.arctan (t / x)) ^ 2 / Real.log (x ^ 2 + t ^ 2) ≤
      (((66879819:ℝ)/71680000)) ^ 2 / (((26519276477199473:ℝ)/9175040000000000)) := by
    have h1 : (Real.arctan (t / x)) ^ 2 / Real.log (x ^ 2 + t ^ 2) ≤
        (Real.arctan (t / x)) ^ 2 / ((26519276477199473:ℝ)/9175040000000000) := by
      exact div_le_div_of_nonneg_left (sq_nonneg _) hLDpos (by linarith : ((26519276477199473:ℝ)/9175040000000000) ≤ Real.log (x ^ 2 + t ^ 2))
    have h2 : (Real.arctan (t / x)) ^ 2 / ((26519276477199473:ℝ)/9175040000000000) ≤ (((66879819:ℝ)/71680000)) ^ 2 / ((26519276477199473:ℝ)/9175040000000000) := by
      exact div_le_div_of_nonneg_right hθsq (le_of_lt hLDpos)
    exact h1.trans h2
  -- P bound
  have hP : (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) ≤ ((29463:ℝ)/250000) := by
    have hsqrt : Real.sqrt (18:ℝ) ≤ Real.sqrt (x ^ 2 + t ^ 2) := Real.sqrt_le_sqrt hQ3le
    have hd1 : (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) ≤ (1 : ℝ) / (2 * Real.sqrt (18:ℝ)) := by
      have hdenpos : 0 < 2 * Real.sqrt (18:ℝ) := by positivity
      exact div_le_div_of_nonneg_left (by norm_num : 0 ≤ (1 : ℝ)) hdenpos (by nlinarith)
    exact hd1.trans (inv_two_sqrt_le (18:ℝ) (by norm_num) ((29463:ℝ)/250000) (by norm_num) (by norm_num))
  -- S bound
  have hS : Real.log (x ^ 2 + t ^ 2) / 2 - Real.log (2 + t) ≤ (1 / 2) * ((108304247:ℝ)/31250000) - ((173046727073587:ℝ)/107520000000000) := by
    nlinarith [hlogU, hDL]
  exact combine x t hxpos htpos ((108304247:ℝ)/31250000) ((173046727073587:ℝ)/107520000000000) ((26519276477199473:ℝ)/9175040000000000) ((66879819:ℝ)/71680000) ((29463:ℝ)/250000) hLDpos hS hQden hP (by norm_num)

private lemma box_5_4 (x t : ℝ) (hx1 : 1 ≤ x) (hx2 : x ≤ 8) (ht : 1 ≤ t)
    (hxl : (3:ℝ) ≤ x) (hxu : x ≤ (4:ℝ)) (htl : (4:ℝ) ≤ t) (htu : t ≤ (6:ℝ)) :
    Real.log (Real.sqrt (x ^ 2 + t ^ 2)) +
        (Real.arctan (t / x)) ^ 2 / (2 * Real.log (Real.sqrt (x ^ 2 + t ^ 2))) +
        (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) ≤
      Real.log (2 + t) + (3 : ℝ) / 2 := by
  have hxpos : 0 < x := by linarith
  have htpos : 0 < t := by linarith
  have hapos : 0 < x ^ 2 + t ^ 2 := by positivity
  -- upper square bound
  have hx2le : x ^ 2 ≤ ((4:ℝ)) ^ 2 := sq_le_of_nonneg (le_of_lt hxpos) hxu
  have ht2le : t ^ 2 ≤ ((6:ℝ)) ^ 2 := sq_le_of_nonneg (le_of_lt htpos) htu
  have ha_le : x ^ 2 + t ^ 2 ≤ (52:ℝ) := by
    have : ((4:ℝ)) ^ 2 + ((6:ℝ)) ^ 2 = (52:ℝ) := by norm_num
    nlinarith
  have hlogU : Real.log (x ^ 2 + t ^ 2) ≤ ((1294743998680389:ℝ)/327680000000000) := by
    exact (Real.log_le_log hapos ha_le).trans vlog_ub_m52
  -- log(2+t) lower bound
  have hDmono : Real.log ((6:ℝ)) ≤ Real.log (2 + t) := by
    apply Real.log_le_log (by norm_num : 0 < (6:ℝ))
    linarith
  have hDL : ((250825351109:ℝ)/140000000000) ≤ Real.log (2 + t) := (vlog_lb_m6).trans hDmono
  -- lower square bound
  have hx2ge : ((3:ℝ)) ^ 2 ≤ x ^ 2 := sq_le_of_nonneg (by norm_num : 0 ≤ (3:ℝ)) hxl
  have ht2ge : ((4:ℝ)) ^ 2 ≤ t ^ 2 := sq_le_of_nonneg (by norm_num : 0 ≤ (4:ℝ)) htl
  have hQ3le : (25:ℝ) ≤ x ^ 2 + t ^ 2 := by
    have : ((3:ℝ)) ^ 2 + ((4:ℝ)) ^ 2 = (25:ℝ) := by norm_num
    nlinarith
  have hlogL : ((324022387095286969:ℝ)/100663296000000000) ≤ Real.log (x ^ 2 + t ^ 2) := by
    exact (vlog_lb_m25).trans (Real.log_le_log (by norm_num : 0 < (25:ℝ)) hQ3le)
  have hLDpos : 0 < ((324022387095286969:ℝ)/100663296000000000) := by norm_num
  -- arctan bound
  have htovx : t / x ≤ (2:ℝ) := by
    rw [div_le_iff₀ hxpos]
    have htu_le : (6:ℝ) ≤ (2:ℝ) * x := by
      calc
        (6:ℝ) = (2:ℝ) * (3:ℝ) := by norm_num
        _ ≤ (2:ℝ) * x := mul_le_mul_of_nonneg_left hxl (by norm_num : 0 ≤ (2:ℝ))
    nlinarith [htu_le]
  have hAT : Real.arctan (t / x) ≤ ((1860319:ℝ)/1680000) := (arctan_mono htovx).trans vatan_ub_m2
  have hθsq : (Real.arctan (t / x)) ^ 2 ≤ (((1860319:ℝ)/1680000)) ^ 2 := by
    have hθn : 0 ≤ Real.arctan (t / x) := Real.arctan_nonneg.mpr (div_nonneg (le_of_lt htpos) (le_of_lt hxpos))
    have hAn : 0 ≤ ((1860319:ℝ)/1680000) := by norm_num
    rw [sq_le_sq]
    rw [abs_of_nonneg hθn, abs_of_nonneg hAn]
    exact hAT
  have hQden : (Real.arctan (t / x)) ^ 2 / Real.log (x ^ 2 + t ^ 2) ≤
      (((1860319:ℝ)/1680000)) ^ 2 / (((324022387095286969:ℝ)/100663296000000000)) := by
    have h1 : (Real.arctan (t / x)) ^ 2 / Real.log (x ^ 2 + t ^ 2) ≤
        (Real.arctan (t / x)) ^ 2 / ((324022387095286969:ℝ)/100663296000000000) := by
      exact div_le_div_of_nonneg_left (sq_nonneg _) hLDpos (by linarith : ((324022387095286969:ℝ)/100663296000000000) ≤ Real.log (x ^ 2 + t ^ 2))
    have h2 : (Real.arctan (t / x)) ^ 2 / ((324022387095286969:ℝ)/100663296000000000) ≤ (((1860319:ℝ)/1680000)) ^ 2 / ((324022387095286969:ℝ)/100663296000000000) := by
      exact div_le_div_of_nonneg_right hθsq (le_of_lt hLDpos)
    exact h1.trans h2
  -- P bound
  have hP : (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) ≤ ((100001:ℝ)/1000000) := by
    have hsqrt : Real.sqrt (25:ℝ) ≤ Real.sqrt (x ^ 2 + t ^ 2) := Real.sqrt_le_sqrt hQ3le
    have hd1 : (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) ≤ (1 : ℝ) / (2 * Real.sqrt (25:ℝ)) := by
      have hdenpos : 0 < 2 * Real.sqrt (25:ℝ) := by positivity
      exact div_le_div_of_nonneg_left (by norm_num : 0 ≤ (1 : ℝ)) hdenpos (by nlinarith)
    exact hd1.trans (inv_two_sqrt_le (25:ℝ) (by norm_num) ((100001:ℝ)/1000000) (by norm_num) (by norm_num))
  -- S bound
  have hS : Real.log (x ^ 2 + t ^ 2) / 2 - Real.log (2 + t) ≤ (1 / 2) * ((1294743998680389:ℝ)/327680000000000) - ((250825351109:ℝ)/140000000000) := by
    nlinarith [hlogU, hDL]
  exact combine x t hxpos htpos ((1294743998680389:ℝ)/327680000000000) ((250825351109:ℝ)/140000000000) ((324022387095286969:ℝ)/100663296000000000) ((1860319:ℝ)/1680000) ((100001:ℝ)/1000000) hLDpos hS hQden hP (by norm_num)

private lemma box_5_5 (x t : ℝ) (hx1 : 1 ≤ x) (hx2 : x ≤ 8) (ht : 1 ≤ t)
    (hxl : (3:ℝ) ≤ x) (hxu : x ≤ (4:ℝ)) (htl : (6:ℝ) ≤ t) (htu : t ≤ (9:ℝ)) :
    Real.log (Real.sqrt (x ^ 2 + t ^ 2)) +
        (Real.arctan (t / x)) ^ 2 / (2 * Real.log (Real.sqrt (x ^ 2 + t ^ 2))) +
        (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) ≤
      Real.log (2 + t) + (3 : ℝ) / 2 := by
  have hxpos : 0 < x := by linarith
  have htpos : 0 < t := by linarith
  have hapos : 0 < x ^ 2 + t ^ 2 := by positivity
  -- upper square bound
  have hx2le : x ^ 2 ≤ ((4:ℝ)) ^ 2 := sq_le_of_nonneg (le_of_lt hxpos) hxu
  have ht2le : t ^ 2 ≤ ((9:ℝ)) ^ 2 := sq_le_of_nonneg (le_of_lt htpos) htu
  have ha_le : x ^ 2 + t ^ 2 ≤ (97:ℝ) := by
    have : ((4:ℝ)) ^ 2 + ((9:ℝ)) ^ 2 = (97:ℝ) := by norm_num
    nlinarith
  have hlogU : Real.log (x ^ 2 + t ^ 2) ≤ ((1178896328402616863431:ℝ)/257698037760000000000) := by
    exact (Real.log_le_log hapos ha_le).trans vlog_ub_m97
  -- log(2+t) lower bound
  have hDmono : Real.log ((8:ℝ)) ≤ Real.log (2 + t) := by
    apply Real.log_le_log (by norm_num : 0 < (8:ℝ))
    linarith
  have hDL : ((20794415409:ℝ)/10000000000) ≤ Real.log (2 + t) := (vlog_lb_m8).trans hDmono
  -- lower square bound
  have hx2ge : ((3:ℝ)) ^ 2 ≤ x ^ 2 := sq_le_of_nonneg (by norm_num : 0 ≤ (3:ℝ)) hxl
  have ht2ge : ((6:ℝ)) ^ 2 ≤ t ^ 2 := sq_le_of_nonneg (by norm_num : 0 ≤ (6:ℝ)) htl
  have hQ3le : (45:ℝ) ≤ x ^ 2 + t ^ 2 := by
    have : ((3:ℝ)) ^ 2 + ((6:ℝ)) ^ 2 = (45:ℝ) := by norm_num
    nlinarith
  have hlogL : ((457782793762884993757:ℝ)/120259084288000000000) ≤ Real.log (x ^ 2 + t ^ 2) := by
    exact (vlog_lb_m45).trans (Real.log_le_log (by norm_num : 0 < (45:ℝ)) hQ3le)
  have hLDpos : 0 < ((457782793762884993757:ℝ)/120259084288000000000) := by norm_num
  -- arctan bound
  have htovx : t / x ≤ (3:ℝ) := by
    rw [div_le_iff₀ hxpos]
    have htu_le : (9:ℝ) ≤ (3:ℝ) * x := by
      calc
        (9:ℝ) = (3:ℝ) * (3:ℝ) := by norm_num
        _ ≤ (3:ℝ) * x := mul_le_mul_of_nonneg_left hxl (by norm_num : 0 ≤ (3:ℝ))
    nlinarith [htu_le]
  have hAT : Real.arctan (t / x) ≤ ((47804443:ℝ)/38272500) := (arctan_mono htovx).trans vatan_ub_m3
  have hθsq : (Real.arctan (t / x)) ^ 2 ≤ (((47804443:ℝ)/38272500)) ^ 2 := by
    have hθn : 0 ≤ Real.arctan (t / x) := Real.arctan_nonneg.mpr (div_nonneg (le_of_lt htpos) (le_of_lt hxpos))
    have hAn : 0 ≤ ((47804443:ℝ)/38272500) := by norm_num
    rw [sq_le_sq]
    rw [abs_of_nonneg hθn, abs_of_nonneg hAn]
    exact hAT
  have hQden : (Real.arctan (t / x)) ^ 2 / Real.log (x ^ 2 + t ^ 2) ≤
      (((47804443:ℝ)/38272500)) ^ 2 / (((457782793762884993757:ℝ)/120259084288000000000)) := by
    have h1 : (Real.arctan (t / x)) ^ 2 / Real.log (x ^ 2 + t ^ 2) ≤
        (Real.arctan (t / x)) ^ 2 / ((457782793762884993757:ℝ)/120259084288000000000) := by
      exact div_le_div_of_nonneg_left (sq_nonneg _) hLDpos (by linarith : ((457782793762884993757:ℝ)/120259084288000000000) ≤ Real.log (x ^ 2 + t ^ 2))
    have h2 : (Real.arctan (t / x)) ^ 2 / ((457782793762884993757:ℝ)/120259084288000000000) ≤ (((47804443:ℝ)/38272500)) ^ 2 / ((457782793762884993757:ℝ)/120259084288000000000) := by
      exact div_le_div_of_nonneg_right hθsq (le_of_lt hLDpos)
    exact h1.trans h2
  -- P bound
  have hP : (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) ≤ ((9317:ℝ)/125000) := by
    have hsqrt : Real.sqrt (45:ℝ) ≤ Real.sqrt (x ^ 2 + t ^ 2) := Real.sqrt_le_sqrt hQ3le
    have hd1 : (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) ≤ (1 : ℝ) / (2 * Real.sqrt (45:ℝ)) := by
      have hdenpos : 0 < 2 * Real.sqrt (45:ℝ) := by positivity
      exact div_le_div_of_nonneg_left (by norm_num : 0 ≤ (1 : ℝ)) hdenpos (by nlinarith)
    exact hd1.trans (inv_two_sqrt_le (45:ℝ) (by norm_num) ((9317:ℝ)/125000) (by norm_num) (by norm_num))
  -- S bound
  have hS : Real.log (x ^ 2 + t ^ 2) / 2 - Real.log (2 + t) ≤ (1 / 2) * ((1178896328402616863431:ℝ)/257698037760000000000) - ((20794415409:ℝ)/10000000000) := by
    nlinarith [hlogU, hDL]
  exact combine x t hxpos htpos ((1178896328402616863431:ℝ)/257698037760000000000) ((20794415409:ℝ)/10000000000) ((457782793762884993757:ℝ)/120259084288000000000) ((47804443:ℝ)/38272500) ((9317:ℝ)/125000) hLDpos hS hQden hP (by norm_num)

private lemma box_5_6 (x t : ℝ) (hx1 : 1 ≤ x) (hx2 : x ≤ 8) (ht : 1 ≤ t)
    (hxl : (3:ℝ) ≤ x) (hxu : x ≤ (4:ℝ)) (htl : (9:ℝ) ≤ t) (htu : t ≤ (13:ℝ)) :
    Real.log (Real.sqrt (x ^ 2 + t ^ 2)) +
        (Real.arctan (t / x)) ^ 2 / (2 * Real.log (Real.sqrt (x ^ 2 + t ^ 2))) +
        (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) ≤
      Real.log (2 + t) + (3 : ℝ) / 2 := by
  have hxpos : 0 < x := by linarith
  have htpos : 0 < t := by linarith
  have hapos : 0 < x ^ 2 + t ^ 2 := by positivity
  -- upper square bound
  have hx2le : x ^ 2 ≤ ((4:ℝ)) ^ 2 := sq_le_of_nonneg (le_of_lt hxpos) hxu
  have ht2le : t ^ 2 ≤ ((13:ℝ)) ^ 2 := sq_le_of_nonneg (le_of_lt htpos) htu
  have ha_le : x ^ 2 + t ^ 2 ≤ (185:ℝ) := by
    have : ((4:ℝ)) ^ 2 + ((13:ℝ)) ^ 2 = (185:ℝ) := by norm_num
    nlinarith
  have hlogU : Real.log (x ^ 2 + t ^ 2) ≤ ((200899802490351414496321:ℝ)/38482906972160000000000) := by
    exact (Real.log_le_log hapos ha_le).trans vlog_ub_m185
  -- log(2+t) lower bound
  have hDmono : Real.log ((11:ℝ)) ≤ Real.log (2 + t) := by
    apply Real.log_le_log (by norm_num : 0 < (11:ℝ))
    linarith
  have hDL : ((22000673184559761:ℝ)/9175040000000000) ≤ Real.log (2 + t) := (vlog_lb_m11).trans hDmono
  -- lower square bound
  have hx2ge : ((3:ℝ)) ^ 2 ≤ x ^ 2 := sq_le_of_nonneg (by norm_num : 0 ≤ (3:ℝ)) hxl
  have ht2ge : ((9:ℝ)) ^ 2 ≤ t ^ 2 := sq_le_of_nonneg (by norm_num : 0 ≤ (9:ℝ)) htl
  have hQ3le : (90:ℝ) ≤ x ^ 2 + t ^ 2 := by
    have : ((3:ℝ)) ^ 2 + ((9:ℝ)) ^ 2 = (90:ℝ) := by norm_num
    nlinarith
  have hlogL : ((2705700194712861134417:ℝ)/601295421440000000000) ≤ Real.log (x ^ 2 + t ^ 2) := by
    exact (vlog_lb_m90).trans (Real.log_le_log (by norm_num : 0 < (90:ℝ)) hQ3le)
  have hLDpos : 0 < ((2705700194712861134417:ℝ)/601295421440000000000) := by norm_num
  -- arctan bound
  have htovx : t / x ≤ ((13:ℝ)/3) := by
    rw [div_le_iff₀ hxpos]
    have htu_le : (13:ℝ) ≤ ((13:ℝ)/3) * x := by
      calc
        (13:ℝ) = ((13:ℝ)/3) * (3:ℝ) := by norm_num
        _ ≤ ((13:ℝ)/3) * x := mul_le_mul_of_nonneg_left hxl (by norm_num : 0 ≤ ((13:ℝ)/3))
    nlinarith [htu_le]
  have hAT : Real.arctan (t / x) ≤ ((1475846601813:ℝ)/1098099047500) := (arctan_mono htovx).trans vatan_ub_m13_3
  have hθsq : (Real.arctan (t / x)) ^ 2 ≤ (((1475846601813:ℝ)/1098099047500)) ^ 2 := by
    have hθn : 0 ≤ Real.arctan (t / x) := Real.arctan_nonneg.mpr (div_nonneg (le_of_lt htpos) (le_of_lt hxpos))
    have hAn : 0 ≤ ((1475846601813:ℝ)/1098099047500) := by norm_num
    rw [sq_le_sq]
    rw [abs_of_nonneg hθn, abs_of_nonneg hAn]
    exact hAT
  have hQden : (Real.arctan (t / x)) ^ 2 / Real.log (x ^ 2 + t ^ 2) ≤
      (((1475846601813:ℝ)/1098099047500)) ^ 2 / (((2705700194712861134417:ℝ)/601295421440000000000)) := by
    have h1 : (Real.arctan (t / x)) ^ 2 / Real.log (x ^ 2 + t ^ 2) ≤
        (Real.arctan (t / x)) ^ 2 / ((2705700194712861134417:ℝ)/601295421440000000000) := by
      exact div_le_div_of_nonneg_left (sq_nonneg _) hLDpos (by linarith : ((2705700194712861134417:ℝ)/601295421440000000000) ≤ Real.log (x ^ 2 + t ^ 2))
    have h2 : (Real.arctan (t / x)) ^ 2 / ((2705700194712861134417:ℝ)/601295421440000000000) ≤ (((1475846601813:ℝ)/1098099047500)) ^ 2 / ((2705700194712861134417:ℝ)/601295421440000000000) := by
      exact div_le_div_of_nonneg_right hθsq (le_of_lt hLDpos)
    exact h1.trans h2
  -- P bound
  have hP : (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) ≤ ((10541:ℝ)/200000) := by
    have hsqrt : Real.sqrt (90:ℝ) ≤ Real.sqrt (x ^ 2 + t ^ 2) := Real.sqrt_le_sqrt hQ3le
    have hd1 : (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) ≤ (1 : ℝ) / (2 * Real.sqrt (90:ℝ)) := by
      have hdenpos : 0 < 2 * Real.sqrt (90:ℝ) := by positivity
      exact div_le_div_of_nonneg_left (by norm_num : 0 ≤ (1 : ℝ)) hdenpos (by nlinarith)
    exact hd1.trans (inv_two_sqrt_le (90:ℝ) (by norm_num) ((10541:ℝ)/200000) (by norm_num) (by norm_num))
  -- S bound
  have hS : Real.log (x ^ 2 + t ^ 2) / 2 - Real.log (2 + t) ≤ (1 / 2) * ((200899802490351414496321:ℝ)/38482906972160000000000) - ((22000673184559761:ℝ)/9175040000000000) := by
    nlinarith [hlogU, hDL]
  exact combine x t hxpos htpos ((200899802490351414496321:ℝ)/38482906972160000000000) ((22000673184559761:ℝ)/9175040000000000) ((2705700194712861134417:ℝ)/601295421440000000000) ((1475846601813:ℝ)/1098099047500) ((10541:ℝ)/200000) hLDpos hS hQden hP (by norm_num)

private lemma box_5_7 (x t : ℝ) (hx1 : 1 ≤ x) (hx2 : x ≤ 8) (ht : 1 ≤ t)
    (hxl : (3:ℝ) ≤ x) (hxu : x ≤ (4:ℝ)) (htl : (13:ℝ) ≤ t) (htu : t ≤ (15:ℝ)) :
    Real.log (Real.sqrt (x ^ 2 + t ^ 2)) +
        (Real.arctan (t / x)) ^ 2 / (2 * Real.log (Real.sqrt (x ^ 2 + t ^ 2))) +
        (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) ≤
      Real.log (2 + t) + (3 : ℝ) / 2 := by
  have hxpos : 0 < x := by linarith
  have htpos : 0 < t := by linarith
  have hapos : 0 < x ^ 2 + t ^ 2 := by positivity
  -- upper square bound
  have hx2le : x ^ 2 ≤ ((4:ℝ)) ^ 2 := sq_le_of_nonneg (le_of_lt hxpos) hxu
  have ht2le : t ^ 2 ≤ ((15:ℝ)) ^ 2 := sq_le_of_nonneg (le_of_lt htpos) htu
  have ha_le : x ^ 2 + t ^ 2 ≤ (241:ℝ) := by
    have : ((4:ℝ)) ^ 2 + ((15:ℝ)) ^ 2 = (241:ℝ) := by norm_num
    nlinarith
  have hlogU : Real.log (x ^ 2 + t ^ 2) ≤ ((30152990034336277534157:ℝ)/5497558138880000000000) := by
    exact (Real.log_le_log hapos ha_le).trans vlog_ub_m241
  -- log(2+t) lower bound
  have hDmono : Real.log ((15:ℝ)) ≤ Real.log (2 + t) := by
    apply Real.log_le_log (by norm_num : 0 < (15:ℝ))
    linarith
  have hDL : ((24846468902980723:ℝ)/9175040000000000) ≤ Real.log (2 + t) := (vlog_lb_m15).trans hDmono
  -- lower square bound
  have hx2ge : ((3:ℝ)) ^ 2 ≤ x ^ 2 := sq_le_of_nonneg (by norm_num : 0 ≤ (3:ℝ)) hxl
  have ht2ge : ((13:ℝ)) ^ 2 ≤ t ^ 2 := sq_le_of_nonneg (by norm_num : 0 ≤ (13:ℝ)) htl
  have hQ3le : (178:ℝ) ≤ x ^ 2 + t ^ 2 := by
    have : ((3:ℝ)) ^ 2 + ((13:ℝ)) ^ 2 = (178:ℝ) := by norm_num
    nlinarith
  have hlogL : ((2392913086057860746359507:ℝ)/461794883665920000000000) ≤ Real.log (x ^ 2 + t ^ 2) := by
    exact (vlog_lb_m178).trans (Real.log_le_log (by norm_num : 0 < (178:ℝ)) hQ3le)
  have hLDpos : 0 < ((2392913086057860746359507:ℝ)/461794883665920000000000) := by norm_num
  -- arctan bound
  have htovx : t / x ≤ (5:ℝ) := by
    rw [div_le_iff₀ hxpos]
    have htu_le : (15:ℝ) ≤ (5:ℝ) * x := by
      calc
        (15:ℝ) = (5:ℝ) * (3:ℝ) := by norm_num
        _ ≤ (5:ℝ) * x := mul_le_mul_of_nonneg_left hxl (by norm_num : 0 ≤ (5:ℝ))
    nlinarith [htu_le]
  have hAT : Real.arctan (t / x) ≤ ((9012967:ℝ)/6562500) := (arctan_mono htovx).trans vatan_ub_m5
  have hθsq : (Real.arctan (t / x)) ^ 2 ≤ (((9012967:ℝ)/6562500)) ^ 2 := by
    have hθn : 0 ≤ Real.arctan (t / x) := Real.arctan_nonneg.mpr (div_nonneg (le_of_lt htpos) (le_of_lt hxpos))
    have hAn : 0 ≤ ((9012967:ℝ)/6562500) := by norm_num
    rw [sq_le_sq]
    rw [abs_of_nonneg hθn, abs_of_nonneg hAn]
    exact hAT
  have hQden : (Real.arctan (t / x)) ^ 2 / Real.log (x ^ 2 + t ^ 2) ≤
      (((9012967:ℝ)/6562500)) ^ 2 / (((2392913086057860746359507:ℝ)/461794883665920000000000)) := by
    have h1 : (Real.arctan (t / x)) ^ 2 / Real.log (x ^ 2 + t ^ 2) ≤
        (Real.arctan (t / x)) ^ 2 / ((2392913086057860746359507:ℝ)/461794883665920000000000) := by
      exact div_le_div_of_nonneg_left (sq_nonneg _) hLDpos (by linarith : ((2392913086057860746359507:ℝ)/461794883665920000000000) ≤ Real.log (x ^ 2 + t ^ 2))
    have h2 : (Real.arctan (t / x)) ^ 2 / ((2392913086057860746359507:ℝ)/461794883665920000000000) ≤ (((9012967:ℝ)/6562500)) ^ 2 / ((2392913086057860746359507:ℝ)/461794883665920000000000) := by
      exact div_le_div_of_nonneg_right hθsq (le_of_lt hLDpos)
    exact h1.trans h2
  -- P bound
  have hP : (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) ≤ ((37477:ℝ)/1000000) := by
    have hsqrt : Real.sqrt (178:ℝ) ≤ Real.sqrt (x ^ 2 + t ^ 2) := Real.sqrt_le_sqrt hQ3le
    have hd1 : (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) ≤ (1 : ℝ) / (2 * Real.sqrt (178:ℝ)) := by
      have hdenpos : 0 < 2 * Real.sqrt (178:ℝ) := by positivity
      exact div_le_div_of_nonneg_left (by norm_num : 0 ≤ (1 : ℝ)) hdenpos (by nlinarith)
    exact hd1.trans (inv_two_sqrt_le (178:ℝ) (by norm_num) ((37477:ℝ)/1000000) (by norm_num) (by norm_num))
  -- S bound
  have hS : Real.log (x ^ 2 + t ^ 2) / 2 - Real.log (2 + t) ≤ (1 / 2) * ((30152990034336277534157:ℝ)/5497558138880000000000) - ((24846468902980723:ℝ)/9175040000000000) := by
    nlinarith [hlogU, hDL]
  exact combine x t hxpos htpos ((30152990034336277534157:ℝ)/5497558138880000000000) ((24846468902980723:ℝ)/9175040000000000) ((2392913086057860746359507:ℝ)/461794883665920000000000) ((9012967:ℝ)/6562500) ((37477:ℝ)/1000000) hLDpos hS hQden hP (by norm_num)

private lemma box_6_0 (x t : ℝ) (hx1 : 1 ≤ x) (hx2 : x ≤ 8) (ht : 1 ≤ t)
    (hxl : (4:ℝ) ≤ x) (hxu : x ≤ (6:ℝ)) (htl : (1:ℝ) ≤ t) (htu : t ≤ ((3:ℝ)/2)) :
    Real.log (Real.sqrt (x ^ 2 + t ^ 2)) +
        (Real.arctan (t / x)) ^ 2 / (2 * Real.log (Real.sqrt (x ^ 2 + t ^ 2))) +
        (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) ≤
      Real.log (2 + t) + (3 : ℝ) / 2 := by
  have hxpos : 0 < x := by linarith
  have htpos : 0 < t := by linarith
  have hapos : 0 < x ^ 2 + t ^ 2 := by positivity
  -- upper square bound
  have hx2le : x ^ 2 ≤ ((6:ℝ)) ^ 2 := sq_le_of_nonneg (le_of_lt hxpos) hxu
  have ht2le : t ^ 2 ≤ (((3:ℝ)/2)) ^ 2 := sq_le_of_nonneg (le_of_lt htpos) htu
  have ha_le : x ^ 2 + t ^ 2 ≤ ((153:ℝ)/4) := by
    have : ((6:ℝ)) ^ 2 + (((3:ℝ)/2)) ^ 2 = ((153:ℝ)/4) := by norm_num
    nlinarith
  have hlogU : Real.log (x ^ 2 + t ^ 2) ≤ ((28047449270254698164653:ℝ)/7696581394432000000000) := by
    exact (Real.log_le_log hapos ha_le).trans vlog_ub_m153_4
  -- log(2+t) lower bound
  have hDmono : Real.log ((3:ℝ)) ≤ Real.log (2 + t) := by
    apply Real.log_le_log (by norm_num : 0 < (3:ℝ))
    linarith
  have hDL : ((153784745867:ℝ)/140000000000) ≤ Real.log (2 + t) := (vlog_lb_m3).trans hDmono
  -- lower square bound
  have hx2ge : ((4:ℝ)) ^ 2 ≤ x ^ 2 := sq_le_of_nonneg (by norm_num : 0 ≤ (4:ℝ)) hxl
  have ht2ge : ((1:ℝ)) ^ 2 ≤ t ^ 2 := sq_le_of_nonneg (by norm_num : 0 ≤ (1:ℝ)) htl
  have hQ3le : (17:ℝ) ≤ x ^ 2 + t ^ 2 := by
    have : ((4:ℝ)) ^ 2 + ((1:ℝ)) ^ 2 = (17:ℝ) := by norm_num
    nlinarith
  have hlogL : ((19964041536534117139:ℝ)/7046430720000000000) ≤ Real.log (x ^ 2 + t ^ 2) := by
    exact (vlog_lb_m17).trans (Real.log_le_log (by norm_num : 0 < (17:ℝ)) hQ3le)
  have hLDpos : 0 < ((19964041536534117139:ℝ)/7046430720000000000) := by norm_num
  -- arctan bound
  have htovx : t / x ≤ ((3:ℝ)/8) := by
    rw [div_le_iff₀ hxpos]
    have htu_le : ((3:ℝ)/2) ≤ ((3:ℝ)/8) * x := by
      calc
        ((3:ℝ)/2) = ((3:ℝ)/8) * (4:ℝ) := by norm_num
        _ ≤ ((3:ℝ)/8) * x := mul_le_mul_of_nonneg_left hxl (by norm_num : 0 ≤ ((3:ℝ)/8))
    nlinarith [htu_le]
  have hAT : Real.arctan (t / x) ≤ ((1685376321:ℝ)/4697620480) := (arctan_mono htovx).trans vatan_ub_m3_8
  have hθsq : (Real.arctan (t / x)) ^ 2 ≤ (((1685376321:ℝ)/4697620480)) ^ 2 := by
    have hθn : 0 ≤ Real.arctan (t / x) := Real.arctan_nonneg.mpr (div_nonneg (le_of_lt htpos) (le_of_lt hxpos))
    have hAn : 0 ≤ ((1685376321:ℝ)/4697620480) := by norm_num
    rw [sq_le_sq]
    rw [abs_of_nonneg hθn, abs_of_nonneg hAn]
    exact hAT
  have hQden : (Real.arctan (t / x)) ^ 2 / Real.log (x ^ 2 + t ^ 2) ≤
      (((1685376321:ℝ)/4697620480)) ^ 2 / (((19964041536534117139:ℝ)/7046430720000000000)) := by
    have h1 : (Real.arctan (t / x)) ^ 2 / Real.log (x ^ 2 + t ^ 2) ≤
        (Real.arctan (t / x)) ^ 2 / ((19964041536534117139:ℝ)/7046430720000000000) := by
      exact div_le_div_of_nonneg_left (sq_nonneg _) hLDpos (by linarith : ((19964041536534117139:ℝ)/7046430720000000000) ≤ Real.log (x ^ 2 + t ^ 2))
    have h2 : (Real.arctan (t / x)) ^ 2 / ((19964041536534117139:ℝ)/7046430720000000000) ≤ (((1685376321:ℝ)/4697620480)) ^ 2 / ((19964041536534117139:ℝ)/7046430720000000000) := by
      exact div_le_div_of_nonneg_right hθsq (le_of_lt hLDpos)
    exact h1.trans h2
  -- P bound
  have hP : (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) ≤ ((30317:ℝ)/250000) := by
    have hsqrt : Real.sqrt (17:ℝ) ≤ Real.sqrt (x ^ 2 + t ^ 2) := Real.sqrt_le_sqrt hQ3le
    have hd1 : (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) ≤ (1 : ℝ) / (2 * Real.sqrt (17:ℝ)) := by
      have hdenpos : 0 < 2 * Real.sqrt (17:ℝ) := by positivity
      exact div_le_div_of_nonneg_left (by norm_num : 0 ≤ (1 : ℝ)) hdenpos (by nlinarith)
    exact hd1.trans (inv_two_sqrt_le (17:ℝ) (by norm_num) ((30317:ℝ)/250000) (by norm_num) (by norm_num))
  -- S bound
  have hS : Real.log (x ^ 2 + t ^ 2) / 2 - Real.log (2 + t) ≤ (1 / 2) * ((28047449270254698164653:ℝ)/7696581394432000000000) - ((153784745867:ℝ)/140000000000) := by
    nlinarith [hlogU, hDL]
  exact combine x t hxpos htpos ((28047449270254698164653:ℝ)/7696581394432000000000) ((153784745867:ℝ)/140000000000) ((19964041536534117139:ℝ)/7046430720000000000) ((1685376321:ℝ)/4697620480) ((30317:ℝ)/250000) hLDpos hS hQden hP (by norm_num)

private lemma box_6_1 (x t : ℝ) (hx1 : 1 ≤ x) (hx2 : x ≤ 8) (ht : 1 ≤ t)
    (hxl : (4:ℝ) ≤ x) (hxu : x ≤ (6:ℝ)) (htl : ((3:ℝ)/2) ≤ t) (htu : t ≤ (2:ℝ)) :
    Real.log (Real.sqrt (x ^ 2 + t ^ 2)) +
        (Real.arctan (t / x)) ^ 2 / (2 * Real.log (Real.sqrt (x ^ 2 + t ^ 2))) +
        (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) ≤
      Real.log (2 + t) + (3 : ℝ) / 2 := by
  have hxpos : 0 < x := by linarith
  have htpos : 0 < t := by linarith
  have hapos : 0 < x ^ 2 + t ^ 2 := by positivity
  -- upper square bound
  have hx2le : x ^ 2 ≤ ((6:ℝ)) ^ 2 := sq_le_of_nonneg (le_of_lt hxpos) hxu
  have ht2le : t ^ 2 ≤ ((2:ℝ)) ^ 2 := sq_le_of_nonneg (le_of_lt htpos) htu
  have ha_le : x ^ 2 + t ^ 2 ≤ (40:ℝ) := by
    have : ((6:ℝ)) ^ 2 + ((2:ℝ)) ^ 2 = (40:ℝ) := by norm_num
    nlinarith
  have hlogU : Real.log (x ^ 2 + t ^ 2) ≤ ((2478928043113:ℝ)/672000000000) := by
    exact (Real.log_le_log hapos ha_le).trans vlog_ub_m40
  -- log(2+t) lower bound
  have hDmono : Real.log (((7:ℝ)/2)) ≤ Real.log (2 + t) := by
    apply Real.log_le_log (by norm_num : 0 < ((7:ℝ)/2))
    linarith
  have hDL : ((269394135787799:ℝ)/215040000000000) ≤ Real.log (2 + t) := (vlog_lb_m7_2).trans hDmono
  -- lower square bound
  have hx2ge : ((4:ℝ)) ^ 2 ≤ x ^ 2 := sq_le_of_nonneg (by norm_num : 0 ≤ (4:ℝ)) hxl
  have ht2ge : (((3:ℝ)/2)) ^ 2 ≤ t ^ 2 := sq_le_of_nonneg (by norm_num : 0 ≤ ((3:ℝ)/2)) htl
  have hQ3le : ((73:ℝ)/4) ≤ x ^ 2 + t ^ 2 := by
    have : ((4:ℝ)) ^ 2 + (((3:ℝ)/2)) ^ 2 = ((73:ℝ)/4) := by norm_num
    nlinarith
  have hlogL : ((447042857939524690247793:ℝ)/153931627888640000000000) ≤ Real.log (x ^ 2 + t ^ 2) := by
    exact (vlog_lb_m73_4).trans (Real.log_le_log (by norm_num : 0 < ((73:ℝ)/4)) hQ3le)
  have hLDpos : 0 < ((447042857939524690247793:ℝ)/153931627888640000000000) := by norm_num
  -- arctan bound
  have htovx : t / x ≤ ((1:ℝ)/2) := by
    rw [div_le_iff₀ hxpos]
    have htu_le : (2:ℝ) ≤ ((1:ℝ)/2) * x := by
      calc
        (2:ℝ) = ((1:ℝ)/2) * (4:ℝ) := by norm_num
        _ ≤ ((1:ℝ)/2) * x := mul_le_mul_of_nonneg_left hxl (by norm_num : 0 ≤ ((1:ℝ)/2))
    nlinarith [htu_le]
  have hAT : Real.arctan (t / x) ≤ ((74783:ℝ)/161280) := (arctan_mono htovx).trans vatan_ub_m1_2
  have hθsq : (Real.arctan (t / x)) ^ 2 ≤ (((74783:ℝ)/161280)) ^ 2 := by
    have hθn : 0 ≤ Real.arctan (t / x) := Real.arctan_nonneg.mpr (div_nonneg (le_of_lt htpos) (le_of_lt hxpos))
    have hAn : 0 ≤ ((74783:ℝ)/161280) := by norm_num
    rw [sq_le_sq]
    rw [abs_of_nonneg hθn, abs_of_nonneg hAn]
    exact hAT
  have hQden : (Real.arctan (t / x)) ^ 2 / Real.log (x ^ 2 + t ^ 2) ≤
      (((74783:ℝ)/161280)) ^ 2 / (((447042857939524690247793:ℝ)/153931627888640000000000)) := by
    have h1 : (Real.arctan (t / x)) ^ 2 / Real.log (x ^ 2 + t ^ 2) ≤
        (Real.arctan (t / x)) ^ 2 / ((447042857939524690247793:ℝ)/153931627888640000000000) := by
      exact div_le_div_of_nonneg_left (sq_nonneg _) hLDpos (by linarith : ((447042857939524690247793:ℝ)/153931627888640000000000) ≤ Real.log (x ^ 2 + t ^ 2))
    have h2 : (Real.arctan (t / x)) ^ 2 / ((447042857939524690247793:ℝ)/153931627888640000000000) ≤ (((74783:ℝ)/161280)) ^ 2 / ((447042857939524690247793:ℝ)/153931627888640000000000) := by
      exact div_le_div_of_nonneg_right hθsq (le_of_lt hLDpos)
    exact h1.trans h2
  -- P bound
  have hP : (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) ≤ ((58521:ℝ)/500000) := by
    have hsqrt : Real.sqrt ((73:ℝ)/4) ≤ Real.sqrt (x ^ 2 + t ^ 2) := Real.sqrt_le_sqrt hQ3le
    have hd1 : (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) ≤ (1 : ℝ) / (2 * Real.sqrt ((73:ℝ)/4)) := by
      have hdenpos : 0 < 2 * Real.sqrt ((73:ℝ)/4) := by positivity
      exact div_le_div_of_nonneg_left (by norm_num : 0 ≤ (1 : ℝ)) hdenpos (by nlinarith)
    exact hd1.trans (inv_two_sqrt_le ((73:ℝ)/4) (by norm_num) ((58521:ℝ)/500000) (by norm_num) (by norm_num))
  -- S bound
  have hS : Real.log (x ^ 2 + t ^ 2) / 2 - Real.log (2 + t) ≤ (1 / 2) * ((2478928043113:ℝ)/672000000000) - ((269394135787799:ℝ)/215040000000000) := by
    nlinarith [hlogU, hDL]
  exact combine x t hxpos htpos ((2478928043113:ℝ)/672000000000) ((269394135787799:ℝ)/215040000000000) ((447042857939524690247793:ℝ)/153931627888640000000000) ((74783:ℝ)/161280) ((58521:ℝ)/500000) hLDpos hS hQden hP (by norm_num)

private lemma box_6_2 (x t : ℝ) (hx1 : 1 ≤ x) (hx2 : x ≤ 8) (ht : 1 ≤ t)
    (hxl : (4:ℝ) ≤ x) (hxu : x ≤ (6:ℝ)) (htl : (2:ℝ) ≤ t) (htu : t ≤ (3:ℝ)) :
    Real.log (Real.sqrt (x ^ 2 + t ^ 2)) +
        (Real.arctan (t / x)) ^ 2 / (2 * Real.log (Real.sqrt (x ^ 2 + t ^ 2))) +
        (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) ≤
      Real.log (2 + t) + (3 : ℝ) / 2 := by
  have hxpos : 0 < x := by linarith
  have htpos : 0 < t := by linarith
  have hapos : 0 < x ^ 2 + t ^ 2 := by positivity
  -- upper square bound
  have hx2le : x ^ 2 ≤ ((6:ℝ)) ^ 2 := sq_le_of_nonneg (le_of_lt hxpos) hxu
  have ht2le : t ^ 2 ≤ ((3:ℝ)) ^ 2 := sq_le_of_nonneg (le_of_lt htpos) htu
  have ha_le : x ^ 2 + t ^ 2 ≤ (45:ℝ) := by
    have : ((6:ℝ)) ^ 2 + ((3:ℝ)) ^ 2 = (45:ℝ) := by norm_num
    nlinarith
  have hlogU : Real.log (x ^ 2 + t ^ 2) ≤ ((1788257604031187017:ℝ)/469762048000000000) := by
    exact (Real.log_le_log hapos ha_le).trans vlog_ub_m45
  -- log(2+t) lower bound
  have hDmono : Real.log ((4:ℝ)) ≤ Real.log (2 + t) := by
    apply Real.log_le_log (by norm_num : 0 < (4:ℝ))
    linarith
  have hDL : ((6931471803:ℝ)/5000000000) ≤ Real.log (2 + t) := (vlog_lb_m4).trans hDmono
  -- lower square bound
  have hx2ge : ((4:ℝ)) ^ 2 ≤ x ^ 2 := sq_le_of_nonneg (by norm_num : 0 ≤ (4:ℝ)) hxl
  have ht2ge : ((2:ℝ)) ^ 2 ≤ t ^ 2 := sq_le_of_nonneg (by norm_num : 0 ≤ (2:ℝ)) htl
  have hQ3le : (20:ℝ) ≤ x ^ 2 + t ^ 2 := by
    have : ((4:ℝ)) ^ 2 + ((2:ℝ)) ^ 2 = (20:ℝ) := by norm_num
    nlinarith
  have hlogL : ((322101096725299:ℝ)/107520000000000) ≤ Real.log (x ^ 2 + t ^ 2) := by
    exact (vlog_lb_m20).trans (Real.log_le_log (by norm_num : 0 < (20:ℝ)) hQ3le)
  have hLDpos : 0 < ((322101096725299:ℝ)/107520000000000) := by norm_num
  -- arctan bound
  have htovx : t / x ≤ ((3:ℝ)/4) := by
    rw [div_le_iff₀ hxpos]
    have htu_le : (3:ℝ) ≤ ((3:ℝ)/4) * x := by
      calc
        (3:ℝ) = ((3:ℝ)/4) * (4:ℝ) := by norm_num
        _ ≤ ((3:ℝ)/4) * x := mul_le_mul_of_nonneg_left hxl (by norm_num : 0 ≤ ((3:ℝ)/4))
    nlinarith [htu_le]
  have hAT : Real.arctan (t / x) ≤ ((5928081:ℝ)/9175040) := (arctan_mono htovx).trans vatan_ub_m3_4
  have hθsq : (Real.arctan (t / x)) ^ 2 ≤ (((5928081:ℝ)/9175040)) ^ 2 := by
    have hθn : 0 ≤ Real.arctan (t / x) := Real.arctan_nonneg.mpr (div_nonneg (le_of_lt htpos) (le_of_lt hxpos))
    have hAn : 0 ≤ ((5928081:ℝ)/9175040) := by norm_num
    rw [sq_le_sq]
    rw [abs_of_nonneg hθn, abs_of_nonneg hAn]
    exact hAT
  have hQden : (Real.arctan (t / x)) ^ 2 / Real.log (x ^ 2 + t ^ 2) ≤
      (((5928081:ℝ)/9175040)) ^ 2 / (((322101096725299:ℝ)/107520000000000)) := by
    have h1 : (Real.arctan (t / x)) ^ 2 / Real.log (x ^ 2 + t ^ 2) ≤
        (Real.arctan (t / x)) ^ 2 / ((322101096725299:ℝ)/107520000000000) := by
      exact div_le_div_of_nonneg_left (sq_nonneg _) hLDpos (by linarith : ((322101096725299:ℝ)/107520000000000) ≤ Real.log (x ^ 2 + t ^ 2))
    have h2 : (Real.arctan (t / x)) ^ 2 / ((322101096725299:ℝ)/107520000000000) ≤ (((5928081:ℝ)/9175040)) ^ 2 / ((322101096725299:ℝ)/107520000000000) := by
      exact div_le_div_of_nonneg_right hθsq (le_of_lt hLDpos)
    exact h1.trans h2
  -- P bound
  have hP : (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) ≤ ((27951:ℝ)/250000) := by
    have hsqrt : Real.sqrt (20:ℝ) ≤ Real.sqrt (x ^ 2 + t ^ 2) := Real.sqrt_le_sqrt hQ3le
    have hd1 : (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) ≤ (1 : ℝ) / (2 * Real.sqrt (20:ℝ)) := by
      have hdenpos : 0 < 2 * Real.sqrt (20:ℝ) := by positivity
      exact div_le_div_of_nonneg_left (by norm_num : 0 ≤ (1 : ℝ)) hdenpos (by nlinarith)
    exact hd1.trans (inv_two_sqrt_le (20:ℝ) (by norm_num) ((27951:ℝ)/250000) (by norm_num) (by norm_num))
  -- S bound
  have hS : Real.log (x ^ 2 + t ^ 2) / 2 - Real.log (2 + t) ≤ (1 / 2) * ((1788257604031187017:ℝ)/469762048000000000) - ((6931471803:ℝ)/5000000000) := by
    nlinarith [hlogU, hDL]
  exact combine x t hxpos htpos ((1788257604031187017:ℝ)/469762048000000000) ((6931471803:ℝ)/5000000000) ((322101096725299:ℝ)/107520000000000) ((5928081:ℝ)/9175040) ((27951:ℝ)/250000) hLDpos hS hQden hP (by norm_num)

private lemma box_6_3 (x t : ℝ) (hx1 : 1 ≤ x) (hx2 : x ≤ 8) (ht : 1 ≤ t)
    (hxl : (4:ℝ) ≤ x) (hxu : x ≤ (6:ℝ)) (htl : (3:ℝ) ≤ t) (htu : t ≤ (4:ℝ)) :
    Real.log (Real.sqrt (x ^ 2 + t ^ 2)) +
        (Real.arctan (t / x)) ^ 2 / (2 * Real.log (Real.sqrt (x ^ 2 + t ^ 2))) +
        (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) ≤
      Real.log (2 + t) + (3 : ℝ) / 2 := by
  have hxpos : 0 < x := by linarith
  have htpos : 0 < t := by linarith
  have hapos : 0 < x ^ 2 + t ^ 2 := by positivity
  -- upper square bound
  have hx2le : x ^ 2 ≤ ((6:ℝ)) ^ 2 := sq_le_of_nonneg (le_of_lt hxpos) hxu
  have ht2le : t ^ 2 ≤ ((4:ℝ)) ^ 2 := sq_le_of_nonneg (le_of_lt htpos) htu
  have ha_le : x ^ 2 + t ^ 2 ≤ (52:ℝ) := by
    have : ((6:ℝ)) ^ 2 + ((4:ℝ)) ^ 2 = (52:ℝ) := by norm_num
    nlinarith
  have hlogU : Real.log (x ^ 2 + t ^ 2) ≤ ((1294743998680389:ℝ)/327680000000000) := by
    exact (Real.log_le_log hapos ha_le).trans vlog_ub_m52
  -- log(2+t) lower bound
  have hDmono : Real.log ((5:ℝ)) ≤ Real.log (2 + t) := by
    apply Real.log_le_log (by norm_num : 0 < (5:ℝ))
    linarith
  have hDL : ((173046727073587:ℝ)/107520000000000) ≤ Real.log (2 + t) := (vlog_lb_m5).trans hDmono
  -- lower square bound
  have hx2ge : ((4:ℝ)) ^ 2 ≤ x ^ 2 := sq_le_of_nonneg (by norm_num : 0 ≤ (4:ℝ)) hxl
  have ht2ge : ((3:ℝ)) ^ 2 ≤ t ^ 2 := sq_le_of_nonneg (by norm_num : 0 ≤ (3:ℝ)) htl
  have hQ3le : (25:ℝ) ≤ x ^ 2 + t ^ 2 := by
    have : ((4:ℝ)) ^ 2 + ((3:ℝ)) ^ 2 = (25:ℝ) := by norm_num
    nlinarith
  have hlogL : ((324022387095286969:ℝ)/100663296000000000) ≤ Real.log (x ^ 2 + t ^ 2) := by
    exact (vlog_lb_m25).trans (Real.log_le_log (by norm_num : 0 < (25:ℝ)) hQ3le)
  have hLDpos : 0 < ((324022387095286969:ℝ)/100663296000000000) := by norm_num
  -- arctan bound
  have htovx : t / x ≤ (1:ℝ) := by
    rw [div_le_iff₀ hxpos]
    have htu_le : (4:ℝ) ≤ (1:ℝ) * x := by
      calc
        (4:ℝ) = (1:ℝ) * (4:ℝ) := by norm_num
        _ ≤ (1:ℝ) * x := mul_le_mul_of_nonneg_left hxl (by norm_num : 0 ≤ (1:ℝ))
    nlinarith [htu_le]
  have hAT : Real.arctan (t / x) ≤ ((263:ℝ)/315) := (arctan_mono htovx).trans vatan_ub_m1
  have hθsq : (Real.arctan (t / x)) ^ 2 ≤ (((263:ℝ)/315)) ^ 2 := by
    have hθn : 0 ≤ Real.arctan (t / x) := Real.arctan_nonneg.mpr (div_nonneg (le_of_lt htpos) (le_of_lt hxpos))
    have hAn : 0 ≤ ((263:ℝ)/315) := by norm_num
    rw [sq_le_sq]
    rw [abs_of_nonneg hθn, abs_of_nonneg hAn]
    exact hAT
  have hQden : (Real.arctan (t / x)) ^ 2 / Real.log (x ^ 2 + t ^ 2) ≤
      (((263:ℝ)/315)) ^ 2 / (((324022387095286969:ℝ)/100663296000000000)) := by
    have h1 : (Real.arctan (t / x)) ^ 2 / Real.log (x ^ 2 + t ^ 2) ≤
        (Real.arctan (t / x)) ^ 2 / ((324022387095286969:ℝ)/100663296000000000) := by
      exact div_le_div_of_nonneg_left (sq_nonneg _) hLDpos (by linarith : ((324022387095286969:ℝ)/100663296000000000) ≤ Real.log (x ^ 2 + t ^ 2))
    have h2 : (Real.arctan (t / x)) ^ 2 / ((324022387095286969:ℝ)/100663296000000000) ≤ (((263:ℝ)/315)) ^ 2 / ((324022387095286969:ℝ)/100663296000000000) := by
      exact div_le_div_of_nonneg_right hθsq (le_of_lt hLDpos)
    exact h1.trans h2
  -- P bound
  have hP : (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) ≤ ((100001:ℝ)/1000000) := by
    have hsqrt : Real.sqrt (25:ℝ) ≤ Real.sqrt (x ^ 2 + t ^ 2) := Real.sqrt_le_sqrt hQ3le
    have hd1 : (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) ≤ (1 : ℝ) / (2 * Real.sqrt (25:ℝ)) := by
      have hdenpos : 0 < 2 * Real.sqrt (25:ℝ) := by positivity
      exact div_le_div_of_nonneg_left (by norm_num : 0 ≤ (1 : ℝ)) hdenpos (by nlinarith)
    exact hd1.trans (inv_two_sqrt_le (25:ℝ) (by norm_num) ((100001:ℝ)/1000000) (by norm_num) (by norm_num))
  -- S bound
  have hS : Real.log (x ^ 2 + t ^ 2) / 2 - Real.log (2 + t) ≤ (1 / 2) * ((1294743998680389:ℝ)/327680000000000) - ((173046727073587:ℝ)/107520000000000) := by
    nlinarith [hlogU, hDL]
  exact combine x t hxpos htpos ((1294743998680389:ℝ)/327680000000000) ((173046727073587:ℝ)/107520000000000) ((324022387095286969:ℝ)/100663296000000000) ((263:ℝ)/315) ((100001:ℝ)/1000000) hLDpos hS hQden hP (by norm_num)

private lemma box_6_4 (x t : ℝ) (hx1 : 1 ≤ x) (hx2 : x ≤ 8) (ht : 1 ≤ t)
    (hxl : (4:ℝ) ≤ x) (hxu : x ≤ (6:ℝ)) (htl : (4:ℝ) ≤ t) (htu : t ≤ (6:ℝ)) :
    Real.log (Real.sqrt (x ^ 2 + t ^ 2)) +
        (Real.arctan (t / x)) ^ 2 / (2 * Real.log (Real.sqrt (x ^ 2 + t ^ 2))) +
        (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) ≤
      Real.log (2 + t) + (3 : ℝ) / 2 := by
  have hxpos : 0 < x := by linarith
  have htpos : 0 < t := by linarith
  have hapos : 0 < x ^ 2 + t ^ 2 := by positivity
  -- upper square bound
  have hx2le : x ^ 2 ≤ ((6:ℝ)) ^ 2 := sq_le_of_nonneg (le_of_lt hxpos) hxu
  have ht2le : t ^ 2 ≤ ((6:ℝ)) ^ 2 := sq_le_of_nonneg (le_of_lt htpos) htu
  have ha_le : x ^ 2 + t ^ 2 ≤ (72:ℝ) := by
    have : ((6:ℝ)) ^ 2 + ((6:ℝ)) ^ 2 = (72:ℝ) := by norm_num
    nlinarith
  have hlogU : Real.log (x ^ 2 + t ^ 2) ≤ ((613102855990053:ℝ)/143360000000000) := by
    exact (Real.log_le_log hapos ha_le).trans vlog_ub_m72
  -- log(2+t) lower bound
  have hDmono : Real.log ((6:ℝ)) ≤ Real.log (2 + t) := by
    apply Real.log_le_log (by norm_num : 0 < (6:ℝ))
    linarith
  have hDL : ((250825351109:ℝ)/140000000000) ≤ Real.log (2 + t) := (vlog_lb_m6).trans hDmono
  -- lower square bound
  have hx2ge : ((4:ℝ)) ^ 2 ≤ x ^ 2 := sq_le_of_nonneg (by norm_num : 0 ≤ (4:ℝ)) hxl
  have ht2ge : ((4:ℝ)) ^ 2 ≤ t ^ 2 := sq_le_of_nonneg (by norm_num : 0 ≤ (4:ℝ)) htl
  have hQ3le : (32:ℝ) ≤ x ^ 2 + t ^ 2 := by
    have : ((4:ℝ)) ^ 2 + ((4:ℝ)) ^ 2 = (32:ℝ) := by norm_num
    nlinarith
  have hlogL : ((6931471803:ℝ)/2000000000) ≤ Real.log (x ^ 2 + t ^ 2) := by
    exact (vlog_lb_m32).trans (Real.log_le_log (by norm_num : 0 < (32:ℝ)) hQ3le)
  have hLDpos : 0 < ((6931471803:ℝ)/2000000000) := by norm_num
  -- arctan bound
  have htovx : t / x ≤ ((3:ℝ)/2) := by
    rw [div_le_iff₀ hxpos]
    have htu_le : (6:ℝ) ≤ ((3:ℝ)/2) * x := by
      calc
        (6:ℝ) = ((3:ℝ)/2) * (4:ℝ) := by norm_num
        _ ≤ ((3:ℝ)/2) * x := mul_le_mul_of_nonneg_left hxl (by norm_num : 0 ≤ ((3:ℝ)/2))
    nlinarith [htu_le]
  have hAT : Real.arctan (t / x) ≤ ((37695443:ℝ)/38272500) := (arctan_mono htovx).trans vatan_ub_m3_2
  have hθsq : (Real.arctan (t / x)) ^ 2 ≤ (((37695443:ℝ)/38272500)) ^ 2 := by
    have hθn : 0 ≤ Real.arctan (t / x) := Real.arctan_nonneg.mpr (div_nonneg (le_of_lt htpos) (le_of_lt hxpos))
    have hAn : 0 ≤ ((37695443:ℝ)/38272500) := by norm_num
    rw [sq_le_sq]
    rw [abs_of_nonneg hθn, abs_of_nonneg hAn]
    exact hAT
  have hQden : (Real.arctan (t / x)) ^ 2 / Real.log (x ^ 2 + t ^ 2) ≤
      (((37695443:ℝ)/38272500)) ^ 2 / (((6931471803:ℝ)/2000000000)) := by
    have h1 : (Real.arctan (t / x)) ^ 2 / Real.log (x ^ 2 + t ^ 2) ≤
        (Real.arctan (t / x)) ^ 2 / ((6931471803:ℝ)/2000000000) := by
      exact div_le_div_of_nonneg_left (sq_nonneg _) hLDpos (by linarith : ((6931471803:ℝ)/2000000000) ≤ Real.log (x ^ 2 + t ^ 2))
    have h2 : (Real.arctan (t / x)) ^ 2 / ((6931471803:ℝ)/2000000000) ≤ (((37695443:ℝ)/38272500)) ^ 2 / ((6931471803:ℝ)/2000000000) := by
      exact div_le_div_of_nonneg_right hθsq (le_of_lt hLDpos)
    exact h1.trans h2
  -- P bound
  have hP : (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) ≤ ((88389:ℝ)/1000000) := by
    have hsqrt : Real.sqrt (32:ℝ) ≤ Real.sqrt (x ^ 2 + t ^ 2) := Real.sqrt_le_sqrt hQ3le
    have hd1 : (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) ≤ (1 : ℝ) / (2 * Real.sqrt (32:ℝ)) := by
      have hdenpos : 0 < 2 * Real.sqrt (32:ℝ) := by positivity
      exact div_le_div_of_nonneg_left (by norm_num : 0 ≤ (1 : ℝ)) hdenpos (by nlinarith)
    exact hd1.trans (inv_two_sqrt_le (32:ℝ) (by norm_num) ((88389:ℝ)/1000000) (by norm_num) (by norm_num))
  -- S bound
  have hS : Real.log (x ^ 2 + t ^ 2) / 2 - Real.log (2 + t) ≤ (1 / 2) * ((613102855990053:ℝ)/143360000000000) - ((250825351109:ℝ)/140000000000) := by
    nlinarith [hlogU, hDL]
  exact combine x t hxpos htpos ((613102855990053:ℝ)/143360000000000) ((250825351109:ℝ)/140000000000) ((6931471803:ℝ)/2000000000) ((37695443:ℝ)/38272500) ((88389:ℝ)/1000000) hLDpos hS hQden hP (by norm_num)

private lemma box_6_5 (x t : ℝ) (hx1 : 1 ≤ x) (hx2 : x ≤ 8) (ht : 1 ≤ t)
    (hxl : (4:ℝ) ≤ x) (hxu : x ≤ (6:ℝ)) (htl : (6:ℝ) ≤ t) (htu : t ≤ (9:ℝ)) :
    Real.log (Real.sqrt (x ^ 2 + t ^ 2)) +
        (Real.arctan (t / x)) ^ 2 / (2 * Real.log (Real.sqrt (x ^ 2 + t ^ 2))) +
        (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) ≤
      Real.log (2 + t) + (3 : ℝ) / 2 := by
  have hxpos : 0 < x := by linarith
  have htpos : 0 < t := by linarith
  have hapos : 0 < x ^ 2 + t ^ 2 := by positivity
  -- upper square bound
  have hx2le : x ^ 2 ≤ ((6:ℝ)) ^ 2 := sq_le_of_nonneg (le_of_lt hxpos) hxu
  have ht2le : t ^ 2 ≤ ((9:ℝ)) ^ 2 := sq_le_of_nonneg (le_of_lt htpos) htu
  have ha_le : x ^ 2 + t ^ 2 ≤ (117:ℝ) := by
    have : ((6:ℝ)) ^ 2 + ((9:ℝ)) ^ 2 = (117:ℝ) := by norm_num
    nlinarith
  have hlogU : Real.log (x ^ 2 + t ^ 2) ≤ ((409067626760117079477:ℝ)/85899345920000000000) := by
    exact (Real.log_le_log hapos ha_le).trans vlog_ub_m117
  -- log(2+t) lower bound
  have hDmono : Real.log ((8:ℝ)) ≤ Real.log (2 + t) := by
    apply Real.log_le_log (by norm_num : 0 < (8:ℝ))
    linarith
  have hDL : ((20794415409:ℝ)/10000000000) ≤ Real.log (2 + t) := (vlog_lb_m8).trans hDmono
  -- lower square bound
  have hx2ge : ((4:ℝ)) ^ 2 ≤ x ^ 2 := sq_le_of_nonneg (by norm_num : 0 ≤ (4:ℝ)) hxl
  have ht2ge : ((6:ℝ)) ^ 2 ≤ t ^ 2 := sq_le_of_nonneg (by norm_num : 0 ≤ (6:ℝ)) htl
  have hQ3le : (52:ℝ) ≤ x ^ 2 + t ^ 2 := by
    have : ((4:ℝ)) ^ 2 + ((6:ℝ)) ^ 2 = (52:ℝ) := by norm_num
    nlinarith
  have hlogL : ((36252810578103897:ℝ)/9175040000000000) ≤ Real.log (x ^ 2 + t ^ 2) := by
    exact (vlog_lb_m52).trans (Real.log_le_log (by norm_num : 0 < (52:ℝ)) hQ3le)
  have hLDpos : 0 < ((36252810578103897:ℝ)/9175040000000000) := by norm_num
  -- arctan bound
  have htovx : t / x ≤ ((9:ℝ)/4) := by
    rw [div_le_iff₀ hxpos]
    have htu_le : (9:ℝ) ≤ ((9:ℝ)/4) * x := by
      calc
        (9:ℝ) = ((9:ℝ)/4) * (4:ℝ) := by norm_num
        _ ≤ ((9:ℝ)/4) * x := mul_le_mul_of_nonneg_left hxl (by norm_num : 0 ≤ ((9:ℝ)/4))
    nlinarith [htu_le]
  have hAT : Real.arctan (t / x) ≤ ((96478260841:ℝ)/83701957500) := (arctan_mono htovx).trans vatan_ub_m9_4
  have hθsq : (Real.arctan (t / x)) ^ 2 ≤ (((96478260841:ℝ)/83701957500)) ^ 2 := by
    have hθn : 0 ≤ Real.arctan (t / x) := Real.arctan_nonneg.mpr (div_nonneg (le_of_lt htpos) (le_of_lt hxpos))
    have hAn : 0 ≤ ((96478260841:ℝ)/83701957500) := by norm_num
    rw [sq_le_sq]
    rw [abs_of_nonneg hθn, abs_of_nonneg hAn]
    exact hAT
  have hQden : (Real.arctan (t / x)) ^ 2 / Real.log (x ^ 2 + t ^ 2) ≤
      (((96478260841:ℝ)/83701957500)) ^ 2 / (((36252810578103897:ℝ)/9175040000000000)) := by
    have h1 : (Real.arctan (t / x)) ^ 2 / Real.log (x ^ 2 + t ^ 2) ≤
        (Real.arctan (t / x)) ^ 2 / ((36252810578103897:ℝ)/9175040000000000) := by
      exact div_le_div_of_nonneg_left (sq_nonneg _) hLDpos (by linarith : ((36252810578103897:ℝ)/9175040000000000) ≤ Real.log (x ^ 2 + t ^ 2))
    have h2 : (Real.arctan (t / x)) ^ 2 / ((36252810578103897:ℝ)/9175040000000000) ≤ (((96478260841:ℝ)/83701957500)) ^ 2 / ((36252810578103897:ℝ)/9175040000000000) := by
      exact div_le_div_of_nonneg_right hθsq (le_of_lt hLDpos)
    exact h1.trans h2
  -- P bound
  have hP : (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) ≤ ((34669:ℝ)/500000) := by
    have hsqrt : Real.sqrt (52:ℝ) ≤ Real.sqrt (x ^ 2 + t ^ 2) := Real.sqrt_le_sqrt hQ3le
    have hd1 : (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) ≤ (1 : ℝ) / (2 * Real.sqrt (52:ℝ)) := by
      have hdenpos : 0 < 2 * Real.sqrt (52:ℝ) := by positivity
      exact div_le_div_of_nonneg_left (by norm_num : 0 ≤ (1 : ℝ)) hdenpos (by nlinarith)
    exact hd1.trans (inv_two_sqrt_le (52:ℝ) (by norm_num) ((34669:ℝ)/500000) (by norm_num) (by norm_num))
  -- S bound
  have hS : Real.log (x ^ 2 + t ^ 2) / 2 - Real.log (2 + t) ≤ (1 / 2) * ((409067626760117079477:ℝ)/85899345920000000000) - ((20794415409:ℝ)/10000000000) := by
    nlinarith [hlogU, hDL]
  exact combine x t hxpos htpos ((409067626760117079477:ℝ)/85899345920000000000) ((20794415409:ℝ)/10000000000) ((36252810578103897:ℝ)/9175040000000000) ((96478260841:ℝ)/83701957500) ((34669:ℝ)/500000) hLDpos hS hQden hP (by norm_num)

private lemma box_6_6 (x t : ℝ) (hx1 : 1 ≤ x) (hx2 : x ≤ 8) (ht : 1 ≤ t)
    (hxl : (4:ℝ) ≤ x) (hxu : x ≤ (6:ℝ)) (htl : (9:ℝ) ≤ t) (htu : t ≤ (13:ℝ)) :
    Real.log (Real.sqrt (x ^ 2 + t ^ 2)) +
        (Real.arctan (t / x)) ^ 2 / (2 * Real.log (Real.sqrt (x ^ 2 + t ^ 2))) +
        (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) ≤
      Real.log (2 + t) + (3 : ℝ) / 2 := by
  have hxpos : 0 < x := by linarith
  have htpos : 0 < t := by linarith
  have hapos : 0 < x ^ 2 + t ^ 2 := by positivity
  -- upper square bound
  have hx2le : x ^ 2 ≤ ((6:ℝ)) ^ 2 := sq_le_of_nonneg (le_of_lt hxpos) hxu
  have ht2le : t ^ 2 ≤ ((13:ℝ)) ^ 2 := sq_le_of_nonneg (le_of_lt htpos) htu
  have ha_le : x ^ 2 + t ^ 2 ≤ (205:ℝ) := by
    have : ((6:ℝ)) ^ 2 + ((13:ℝ)) ^ 2 = (205:ℝ) := by norm_num
    nlinarith
  have hlogU : Real.log (x ^ 2 + t ^ 2) ≤ ((29263568698756449409157:ℝ)/5497558138880000000000) := by
    exact (Real.log_le_log hapos ha_le).trans vlog_ub_m205
  -- log(2+t) lower bound
  have hDmono : Real.log ((11:ℝ)) ≤ Real.log (2 + t) := by
    apply Real.log_le_log (by norm_num : 0 < (11:ℝ))
    linarith
  have hDL : ((22000673184559761:ℝ)/9175040000000000) ≤ Real.log (2 + t) := (vlog_lb_m11).trans hDmono
  -- lower square bound
  have hx2ge : ((4:ℝ)) ^ 2 ≤ x ^ 2 := sq_le_of_nonneg (by norm_num : 0 ≤ (4:ℝ)) hxl
  have ht2ge : ((9:ℝ)) ^ 2 ≤ t ^ 2 := sq_le_of_nonneg (by norm_num : 0 ≤ (9:ℝ)) htl
  have hQ3le : (97:ℝ) ≤ x ^ 2 + t ^ 2 := by
    have : ((4:ℝ)) ^ 2 + ((9:ℝ)) ^ 2 = (97:ℝ) := by norm_num
    nlinarith
  have hlogL : ((264071971326534382601579:ℝ)/57724360458240000000000) ≤ Real.log (x ^ 2 + t ^ 2) := by
    exact (vlog_lb_m97).trans (Real.log_le_log (by norm_num : 0 < (97:ℝ)) hQ3le)
  have hLDpos : 0 < ((264071971326534382601579:ℝ)/57724360458240000000000) := by norm_num
  -- arctan bound
  have htovx : t / x ≤ ((13:ℝ)/4) := by
    rw [div_le_iff₀ hxpos]
    have htu_le : (13:ℝ) ≤ ((13:ℝ)/4) * x := by
      calc
        (13:ℝ) = ((13:ℝ)/4) * (4:ℝ) := by norm_num
        _ ≤ ((13:ℝ)/4) * x := mul_le_mul_of_nonneg_left hxl (by norm_num : 0 ≤ ((13:ℝ)/4))
    nlinarith [htu_le]
  have hAT : Real.arctan (t / x) ≤ ((4191346173439:ℝ)/3294297142500) := (arctan_mono htovx).trans vatan_ub_m13_4
  have hθsq : (Real.arctan (t / x)) ^ 2 ≤ (((4191346173439:ℝ)/3294297142500)) ^ 2 := by
    have hθn : 0 ≤ Real.arctan (t / x) := Real.arctan_nonneg.mpr (div_nonneg (le_of_lt htpos) (le_of_lt hxpos))
    have hAn : 0 ≤ ((4191346173439:ℝ)/3294297142500) := by norm_num
    rw [sq_le_sq]
    rw [abs_of_nonneg hθn, abs_of_nonneg hAn]
    exact hAT
  have hQden : (Real.arctan (t / x)) ^ 2 / Real.log (x ^ 2 + t ^ 2) ≤
      (((4191346173439:ℝ)/3294297142500)) ^ 2 / (((264071971326534382601579:ℝ)/57724360458240000000000)) := by
    have h1 : (Real.arctan (t / x)) ^ 2 / Real.log (x ^ 2 + t ^ 2) ≤
        (Real.arctan (t / x)) ^ 2 / ((264071971326534382601579:ℝ)/57724360458240000000000) := by
      exact div_le_div_of_nonneg_left (sq_nonneg _) hLDpos (by linarith : ((264071971326534382601579:ℝ)/57724360458240000000000) ≤ Real.log (x ^ 2 + t ^ 2))
    have h2 : (Real.arctan (t / x)) ^ 2 / ((264071971326534382601579:ℝ)/57724360458240000000000) ≤ (((4191346173439:ℝ)/3294297142500)) ^ 2 / ((264071971326534382601579:ℝ)/57724360458240000000000) := by
      exact div_le_div_of_nonneg_right hθsq (le_of_lt hLDpos)
    exact h1.trans h2
  -- P bound
  have hP : (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) ≤ ((3173:ℝ)/62500) := by
    have hsqrt : Real.sqrt (97:ℝ) ≤ Real.sqrt (x ^ 2 + t ^ 2) := Real.sqrt_le_sqrt hQ3le
    have hd1 : (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) ≤ (1 : ℝ) / (2 * Real.sqrt (97:ℝ)) := by
      have hdenpos : 0 < 2 * Real.sqrt (97:ℝ) := by positivity
      exact div_le_div_of_nonneg_left (by norm_num : 0 ≤ (1 : ℝ)) hdenpos (by nlinarith)
    exact hd1.trans (inv_two_sqrt_le (97:ℝ) (by norm_num) ((3173:ℝ)/62500) (by norm_num) (by norm_num))
  -- S bound
  have hS : Real.log (x ^ 2 + t ^ 2) / 2 - Real.log (2 + t) ≤ (1 / 2) * ((29263568698756449409157:ℝ)/5497558138880000000000) - ((22000673184559761:ℝ)/9175040000000000) := by
    nlinarith [hlogU, hDL]
  exact combine x t hxpos htpos ((29263568698756449409157:ℝ)/5497558138880000000000) ((22000673184559761:ℝ)/9175040000000000) ((264071971326534382601579:ℝ)/57724360458240000000000) ((4191346173439:ℝ)/3294297142500) ((3173:ℝ)/62500) hLDpos hS hQden hP (by norm_num)

private lemma box_6_7 (x t : ℝ) (hx1 : 1 ≤ x) (hx2 : x ≤ 8) (ht : 1 ≤ t)
    (hxl : (4:ℝ) ≤ x) (hxu : x ≤ (6:ℝ)) (htl : (13:ℝ) ≤ t) (htu : t ≤ (15:ℝ)) :
    Real.log (Real.sqrt (x ^ 2 + t ^ 2)) +
        (Real.arctan (t / x)) ^ 2 / (2 * Real.log (Real.sqrt (x ^ 2 + t ^ 2))) +
        (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) ≤
      Real.log (2 + t) + (3 : ℝ) / 2 := by
  have hxpos : 0 < x := by linarith
  have htpos : 0 < t := by linarith
  have hapos : 0 < x ^ 2 + t ^ 2 := by positivity
  -- upper square bound
  have hx2le : x ^ 2 ≤ ((6:ℝ)) ^ 2 := sq_le_of_nonneg (le_of_lt hxpos) hxu
  have ht2le : t ^ 2 ≤ ((15:ℝ)) ^ 2 := sq_le_of_nonneg (le_of_lt htpos) htu
  have ha_le : x ^ 2 + t ^ 2 ≤ (261:ℝ) := by
    have : ((6:ℝ)) ^ 2 + ((15:ℝ)) ^ 2 = (261:ℝ) := by norm_num
    nlinarith
  have hlogU : Real.log (x ^ 2 + t ^ 2) ≤ ((27409781920459417610057797:ℝ)/4925812092436480000000000) := by
    exact (Real.log_le_log hapos ha_le).trans vlog_ub_m261
  -- log(2+t) lower bound
  have hDmono : Real.log ((15:ℝ)) ≤ Real.log (2 + t) := by
    apply Real.log_le_log (by norm_num : 0 < (15:ℝ))
    linarith
  have hDL : ((24846468902980723:ℝ)/9175040000000000) ≤ Real.log (2 + t) := (vlog_lb_m15).trans hDmono
  -- lower square bound
  have hx2ge : ((4:ℝ)) ^ 2 ≤ x ^ 2 := sq_le_of_nonneg (by norm_num : 0 ≤ (4:ℝ)) hxl
  have ht2ge : ((13:ℝ)) ^ 2 ≤ t ^ 2 := sq_le_of_nonneg (by norm_num : 0 ≤ (13:ℝ)) htl
  have hQ3le : (185:ℝ) ≤ x ^ 2 + t ^ 2 := by
    have : ((4:ℝ)) ^ 2 + ((13:ℝ)) ^ 2 = (185:ℝ) := by norm_num
    nlinarith
  have hlogL : ((205713780384660156662651889:ℝ)/39406496739491840000000000) ≤ Real.log (x ^ 2 + t ^ 2) := by
    exact (vlog_lb_m185).trans (Real.log_le_log (by norm_num : 0 < (185:ℝ)) hQ3le)
  have hLDpos : 0 < ((205713780384660156662651889:ℝ)/39406496739491840000000000) := by norm_num
  -- arctan bound
  have htovx : t / x ≤ ((15:ℝ)/4) := by
    rw [div_le_iff₀ hxpos]
    have htu_le : (15:ℝ) ≤ ((15:ℝ)/4) * x := by
      calc
        (15:ℝ) = ((15:ℝ)/4) * (4:ℝ) := by norm_num
        _ ≤ ((15:ℝ)/4) * x := mul_le_mul_of_nonneg_left hxl (by norm_num : 0 ≤ ((15:ℝ)/4))
    nlinarith [htu_le]
  have hAT : Real.arctan (t / x) ≤ ((6268070671:ℝ)/4784062500) := (arctan_mono htovx).trans vatan_ub_m15_4
  have hθsq : (Real.arctan (t / x)) ^ 2 ≤ (((6268070671:ℝ)/4784062500)) ^ 2 := by
    have hθn : 0 ≤ Real.arctan (t / x) := Real.arctan_nonneg.mpr (div_nonneg (le_of_lt htpos) (le_of_lt hxpos))
    have hAn : 0 ≤ ((6268070671:ℝ)/4784062500) := by norm_num
    rw [sq_le_sq]
    rw [abs_of_nonneg hθn, abs_of_nonneg hAn]
    exact hAT
  have hQden : (Real.arctan (t / x)) ^ 2 / Real.log (x ^ 2 + t ^ 2) ≤
      (((6268070671:ℝ)/4784062500)) ^ 2 / (((205713780384660156662651889:ℝ)/39406496739491840000000000)) := by
    have h1 : (Real.arctan (t / x)) ^ 2 / Real.log (x ^ 2 + t ^ 2) ≤
        (Real.arctan (t / x)) ^ 2 / ((205713780384660156662651889:ℝ)/39406496739491840000000000) := by
      exact div_le_div_of_nonneg_left (sq_nonneg _) hLDpos (by linarith : ((205713780384660156662651889:ℝ)/39406496739491840000000000) ≤ Real.log (x ^ 2 + t ^ 2))
    have h2 : (Real.arctan (t / x)) ^ 2 / ((205713780384660156662651889:ℝ)/39406496739491840000000000) ≤ (((6268070671:ℝ)/4784062500)) ^ 2 / ((205713780384660156662651889:ℝ)/39406496739491840000000000) := by
      exact div_le_div_of_nonneg_right hθsq (le_of_lt hLDpos)
    exact h1.trans h2
  -- P bound
  have hP : (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) ≤ ((36761:ℝ)/1000000) := by
    have hsqrt : Real.sqrt (185:ℝ) ≤ Real.sqrt (x ^ 2 + t ^ 2) := Real.sqrt_le_sqrt hQ3le
    have hd1 : (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) ≤ (1 : ℝ) / (2 * Real.sqrt (185:ℝ)) := by
      have hdenpos : 0 < 2 * Real.sqrt (185:ℝ) := by positivity
      exact div_le_div_of_nonneg_left (by norm_num : 0 ≤ (1 : ℝ)) hdenpos (by nlinarith)
    exact hd1.trans (inv_two_sqrt_le (185:ℝ) (by norm_num) ((36761:ℝ)/1000000) (by norm_num) (by norm_num))
  -- S bound
  have hS : Real.log (x ^ 2 + t ^ 2) / 2 - Real.log (2 + t) ≤ (1 / 2) * ((27409781920459417610057797:ℝ)/4925812092436480000000000) - ((24846468902980723:ℝ)/9175040000000000) := by
    nlinarith [hlogU, hDL]
  exact combine x t hxpos htpos ((27409781920459417610057797:ℝ)/4925812092436480000000000) ((24846468902980723:ℝ)/9175040000000000) ((205713780384660156662651889:ℝ)/39406496739491840000000000) ((6268070671:ℝ)/4784062500) ((36761:ℝ)/1000000) hLDpos hS hQden hP (by norm_num)

private lemma box_7_0 (x t : ℝ) (hx1 : 1 ≤ x) (hx2 : x ≤ 8) (ht : 1 ≤ t)
    (hxl : (6:ℝ) ≤ x) (hxu : x ≤ (8:ℝ)) (htl : (1:ℝ) ≤ t) (htu : t ≤ ((3:ℝ)/2)) :
    Real.log (Real.sqrt (x ^ 2 + t ^ 2)) +
        (Real.arctan (t / x)) ^ 2 / (2 * Real.log (Real.sqrt (x ^ 2 + t ^ 2))) +
        (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) ≤
      Real.log (2 + t) + (3 : ℝ) / 2 := by
  have hxpos : 0 < x := by linarith
  have htpos : 0 < t := by linarith
  have hapos : 0 < x ^ 2 + t ^ 2 := by positivity
  -- upper square bound
  have hx2le : x ^ 2 ≤ ((8:ℝ)) ^ 2 := sq_le_of_nonneg (le_of_lt hxpos) hxu
  have ht2le : t ^ 2 ≤ (((3:ℝ)/2)) ^ 2 := sq_le_of_nonneg (le_of_lt htpos) htu
  have ha_le : x ^ 2 + t ^ 2 ≤ ((265:ℝ)/4) := by
    have : ((8:ℝ)) ^ 2 + (((3:ℝ)/2)) ^ 2 = ((265:ℝ)/4) := by norm_num
    nlinarith
  have hlogU : Real.log (x ^ 2 + t ^ 2) ≤ ((20656075128786747122094129:ℝ)/4925812092436480000000000) := by
    exact (Real.log_le_log hapos ha_le).trans vlog_ub_m265_4
  -- log(2+t) lower bound
  have hDmono : Real.log ((3:ℝ)) ≤ Real.log (2 + t) := by
    apply Real.log_le_log (by norm_num : 0 < (3:ℝ))
    linarith
  have hDL : ((153784745867:ℝ)/140000000000) ≤ Real.log (2 + t) := (vlog_lb_m3).trans hDmono
  -- lower square bound
  have hx2ge : ((6:ℝ)) ^ 2 ≤ x ^ 2 := sq_le_of_nonneg (by norm_num : 0 ≤ (6:ℝ)) hxl
  have ht2ge : ((1:ℝ)) ^ 2 ≤ t ^ 2 := sq_le_of_nonneg (by norm_num : 0 ≤ (1:ℝ)) htl
  have hQ3le : (37:ℝ) ≤ x ^ 2 + t ^ 2 := by
    have : ((6:ℝ)) ^ 2 + ((1:ℝ)) ^ 2 = (37:ℝ) := by norm_num
    nlinarith
  have hlogL : ((1302737042421079981271:ℝ)/360777252864000000000) ≤ Real.log (x ^ 2 + t ^ 2) := by
    exact (vlog_lb_m37).trans (Real.log_le_log (by norm_num : 0 < (37:ℝ)) hQ3le)
  have hLDpos : 0 < ((1302737042421079981271:ℝ)/360777252864000000000) := by norm_num
  -- arctan bound
  have htovx : t / x ≤ ((1:ℝ)/4) := by
    rw [div_le_iff₀ hxpos]
    have htu_le : ((3:ℝ)/2) ≤ ((1:ℝ)/4) * x := by
      calc
        ((3:ℝ)/2) = ((1:ℝ)/4) * (6:ℝ) := by norm_num
        _ ≤ ((1:ℝ)/4) * x := mul_le_mul_of_nonneg_left hxl (by norm_num : 0 ≤ ((1:ℝ)/4))
    nlinarith [htu_le]
  have hAT : Real.arctan (t / x) ≤ ((20229203:ℝ)/82575360) := (arctan_mono htovx).trans vatan_ub_m1_4
  have hθsq : (Real.arctan (t / x)) ^ 2 ≤ (((20229203:ℝ)/82575360)) ^ 2 := by
    have hθn : 0 ≤ Real.arctan (t / x) := Real.arctan_nonneg.mpr (div_nonneg (le_of_lt htpos) (le_of_lt hxpos))
    have hAn : 0 ≤ ((20229203:ℝ)/82575360) := by norm_num
    rw [sq_le_sq]
    rw [abs_of_nonneg hθn, abs_of_nonneg hAn]
    exact hAT
  have hQden : (Real.arctan (t / x)) ^ 2 / Real.log (x ^ 2 + t ^ 2) ≤
      (((20229203:ℝ)/82575360)) ^ 2 / (((1302737042421079981271:ℝ)/360777252864000000000)) := by
    have h1 : (Real.arctan (t / x)) ^ 2 / Real.log (x ^ 2 + t ^ 2) ≤
        (Real.arctan (t / x)) ^ 2 / ((1302737042421079981271:ℝ)/360777252864000000000) := by
      exact div_le_div_of_nonneg_left (sq_nonneg _) hLDpos (by linarith : ((1302737042421079981271:ℝ)/360777252864000000000) ≤ Real.log (x ^ 2 + t ^ 2))
    have h2 : (Real.arctan (t / x)) ^ 2 / ((1302737042421079981271:ℝ)/360777252864000000000) ≤ (((20229203:ℝ)/82575360)) ^ 2 / ((1302737042421079981271:ℝ)/360777252864000000000) := by
      exact div_le_div_of_nonneg_right hθsq (le_of_lt hLDpos)
    exact h1.trans h2
  -- P bound
  have hP : (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) ≤ ((411:ℝ)/5000) := by
    have hsqrt : Real.sqrt (37:ℝ) ≤ Real.sqrt (x ^ 2 + t ^ 2) := Real.sqrt_le_sqrt hQ3le
    have hd1 : (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) ≤ (1 : ℝ) / (2 * Real.sqrt (37:ℝ)) := by
      have hdenpos : 0 < 2 * Real.sqrt (37:ℝ) := by positivity
      exact div_le_div_of_nonneg_left (by norm_num : 0 ≤ (1 : ℝ)) hdenpos (by nlinarith)
    exact hd1.trans (inv_two_sqrt_le (37:ℝ) (by norm_num) ((411:ℝ)/5000) (by norm_num) (by norm_num))
  -- S bound
  have hS : Real.log (x ^ 2 + t ^ 2) / 2 - Real.log (2 + t) ≤ (1 / 2) * ((20656075128786747122094129:ℝ)/4925812092436480000000000) - ((153784745867:ℝ)/140000000000) := by
    nlinarith [hlogU, hDL]
  exact combine x t hxpos htpos ((20656075128786747122094129:ℝ)/4925812092436480000000000) ((153784745867:ℝ)/140000000000) ((1302737042421079981271:ℝ)/360777252864000000000) ((20229203:ℝ)/82575360) ((411:ℝ)/5000) hLDpos hS hQden hP (by norm_num)

private lemma box_7_1 (x t : ℝ) (hx1 : 1 ≤ x) (hx2 : x ≤ 8) (ht : 1 ≤ t)
    (hxl : (6:ℝ) ≤ x) (hxu : x ≤ (8:ℝ)) (htl : ((3:ℝ)/2) ≤ t) (htu : t ≤ (2:ℝ)) :
    Real.log (Real.sqrt (x ^ 2 + t ^ 2)) +
        (Real.arctan (t / x)) ^ 2 / (2 * Real.log (Real.sqrt (x ^ 2 + t ^ 2))) +
        (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) ≤
      Real.log (2 + t) + (3 : ℝ) / 2 := by
  have hxpos : 0 < x := by linarith
  have htpos : 0 < t := by linarith
  have hapos : 0 < x ^ 2 + t ^ 2 := by positivity
  -- upper square bound
  have hx2le : x ^ 2 ≤ ((8:ℝ)) ^ 2 := sq_le_of_nonneg (le_of_lt hxpos) hxu
  have ht2le : t ^ 2 ≤ ((2:ℝ)) ^ 2 := sq_le_of_nonneg (le_of_lt htpos) htu
  have ha_le : x ^ 2 + t ^ 2 ≤ (68:ℝ) := by
    have : ((8:ℝ)) ^ 2 + ((2:ℝ)) ^ 2 = (68:ℝ) := by norm_num
    nlinarith
  have hlogU : Real.log (x ^ 2 + t ^ 2) ≤ ((232284911932602227:ℝ)/55050240000000000) := by
    exact (Real.log_le_log hapos ha_le).trans vlog_ub_m68
  -- log(2+t) lower bound
  have hDmono : Real.log (((7:ℝ)/2)) ≤ Real.log (2 + t) := by
    apply Real.log_le_log (by norm_num : 0 < ((7:ℝ)/2))
    linarith
  have hDL : ((269394135787799:ℝ)/215040000000000) ≤ Real.log (2 + t) := (vlog_lb_m7_2).trans hDmono
  -- lower square bound
  have hx2ge : ((6:ℝ)) ^ 2 ≤ x ^ 2 := sq_le_of_nonneg (by norm_num : 0 ≤ (6:ℝ)) hxl
  have ht2ge : (((3:ℝ)/2)) ^ 2 ≤ t ^ 2 := sq_le_of_nonneg (by norm_num : 0 ≤ ((3:ℝ)/2)) htl
  have hQ3le : ((153:ℝ)/4) ≤ x ^ 2 + t ^ 2 := by
    have : ((6:ℝ)) ^ 2 + (((3:ℝ)/2)) ^ 2 = ((153:ℝ)/4) := by norm_num
    nlinarith
  have hlogL : ((28720585946874995412186877:ℝ)/7881299347898368000000000) ≤ Real.log (x ^ 2 + t ^ 2) := by
    exact (vlog_lb_m153_4).trans (Real.log_le_log (by norm_num : 0 < ((153:ℝ)/4)) hQ3le)
  have hLDpos : 0 < ((28720585946874995412186877:ℝ)/7881299347898368000000000) := by norm_num
  -- arctan bound
  have htovx : t / x ≤ ((1:ℝ)/3) := by
    rw [div_le_iff₀ hxpos]
    have htu_le : (2:ℝ) ≤ ((1:ℝ)/3) * x := by
      calc
        (2:ℝ) = ((1:ℝ)/3) * (6:ℝ) := by norm_num
        _ ≤ ((1:ℝ)/3) * x := mul_le_mul_of_nonneg_left hxl (by norm_num : 0 ≤ ((1:ℝ)/3))
    nlinarith [htu_le]
  have hAT : Real.arctan (t / x) ≤ ((1994903:ℝ)/6200145) := (arctan_mono htovx).trans vatan_ub_m1_3
  have hθsq : (Real.arctan (t / x)) ^ 2 ≤ (((1994903:ℝ)/6200145)) ^ 2 := by
    have hθn : 0 ≤ Real.arctan (t / x) := Real.arctan_nonneg.mpr (div_nonneg (le_of_lt htpos) (le_of_lt hxpos))
    have hAn : 0 ≤ ((1994903:ℝ)/6200145) := by norm_num
    rw [sq_le_sq]
    rw [abs_of_nonneg hθn, abs_of_nonneg hAn]
    exact hAT
  have hQden : (Real.arctan (t / x)) ^ 2 / Real.log (x ^ 2 + t ^ 2) ≤
      (((1994903:ℝ)/6200145)) ^ 2 / (((28720585946874995412186877:ℝ)/7881299347898368000000000)) := by
    have h1 : (Real.arctan (t / x)) ^ 2 / Real.log (x ^ 2 + t ^ 2) ≤
        (Real.arctan (t / x)) ^ 2 / ((28720585946874995412186877:ℝ)/7881299347898368000000000) := by
      exact div_le_div_of_nonneg_left (sq_nonneg _) hLDpos (by linarith : ((28720585946874995412186877:ℝ)/7881299347898368000000000) ≤ Real.log (x ^ 2 + t ^ 2))
    have h2 : (Real.arctan (t / x)) ^ 2 / ((28720585946874995412186877:ℝ)/7881299347898368000000000) ≤ (((1994903:ℝ)/6200145)) ^ 2 / ((28720585946874995412186877:ℝ)/7881299347898368000000000) := by
      exact div_le_div_of_nonneg_right hθsq (le_of_lt hLDpos)
    exact h1.trans h2
  -- P bound
  have hP : (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) ≤ ((40423:ℝ)/500000) := by
    have hsqrt : Real.sqrt ((153:ℝ)/4) ≤ Real.sqrt (x ^ 2 + t ^ 2) := Real.sqrt_le_sqrt hQ3le
    have hd1 : (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) ≤ (1 : ℝ) / (2 * Real.sqrt ((153:ℝ)/4)) := by
      have hdenpos : 0 < 2 * Real.sqrt ((153:ℝ)/4) := by positivity
      exact div_le_div_of_nonneg_left (by norm_num : 0 ≤ (1 : ℝ)) hdenpos (by nlinarith)
    exact hd1.trans (inv_two_sqrt_le ((153:ℝ)/4) (by norm_num) ((40423:ℝ)/500000) (by norm_num) (by norm_num))
  -- S bound
  have hS : Real.log (x ^ 2 + t ^ 2) / 2 - Real.log (2 + t) ≤ (1 / 2) * ((232284911932602227:ℝ)/55050240000000000) - ((269394135787799:ℝ)/215040000000000) := by
    nlinarith [hlogU, hDL]
  exact combine x t hxpos htpos ((232284911932602227:ℝ)/55050240000000000) ((269394135787799:ℝ)/215040000000000) ((28720585946874995412186877:ℝ)/7881299347898368000000000) ((1994903:ℝ)/6200145) ((40423:ℝ)/500000) hLDpos hS hQden hP (by norm_num)

private lemma box_7_2 (x t : ℝ) (hx1 : 1 ≤ x) (hx2 : x ≤ 8) (ht : 1 ≤ t)
    (hxl : (6:ℝ) ≤ x) (hxu : x ≤ (8:ℝ)) (htl : (2:ℝ) ≤ t) (htu : t ≤ (3:ℝ)) :
    Real.log (Real.sqrt (x ^ 2 + t ^ 2)) +
        (Real.arctan (t / x)) ^ 2 / (2 * Real.log (Real.sqrt (x ^ 2 + t ^ 2))) +
        (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) ≤
      Real.log (2 + t) + (3 : ℝ) / 2 := by
  have hxpos : 0 < x := by linarith
  have htpos : 0 < t := by linarith
  have hapos : 0 < x ^ 2 + t ^ 2 := by positivity
  -- upper square bound
  have hx2le : x ^ 2 ≤ ((8:ℝ)) ^ 2 := sq_le_of_nonneg (le_of_lt hxpos) hxu
  have ht2le : t ^ 2 ≤ ((3:ℝ)) ^ 2 := sq_le_of_nonneg (le_of_lt htpos) htu
  have ha_le : x ^ 2 + t ^ 2 ≤ (73:ℝ) := by
    have : ((8:ℝ)) ^ 2 + ((3:ℝ)) ^ 2 = (73:ℝ) := by norm_num
    nlinarith
  have hlogU : Real.log (x ^ 2 + t ^ 2) ≤ ((1289916814460870769681:ℝ)/300647710720000000000) := by
    exact (Real.log_le_log hapos ha_le).trans vlog_ub_m73
  -- log(2+t) lower bound
  have hDmono : Real.log ((4:ℝ)) ≤ Real.log (2 + t) := by
    apply Real.log_le_log (by norm_num : 0 < (4:ℝ))
    linarith
  have hDL : ((6931471803:ℝ)/5000000000) ≤ Real.log (2 + t) := (vlog_lb_m4).trans hDmono
  -- lower square bound
  have hx2ge : ((6:ℝ)) ^ 2 ≤ x ^ 2 := sq_le_of_nonneg (by norm_num : 0 ≤ (6:ℝ)) hxl
  have ht2ge : ((2:ℝ)) ^ 2 ≤ t ^ 2 := sq_le_of_nonneg (by norm_num : 0 ≤ (2:ℝ)) htl
  have hQ3le : (40:ℝ) ≤ x ^ 2 + t ^ 2 := by
    have : ((6:ℝ)) ^ 2 + ((2:ℝ)) ^ 2 = (40:ℝ) := by norm_num
    nlinarith
  have hlogL : ((79325656310231:ℝ)/21504000000000) ≤ Real.log (x ^ 2 + t ^ 2) := by
    exact (vlog_lb_m40).trans (Real.log_le_log (by norm_num : 0 < (40:ℝ)) hQ3le)
  have hLDpos : 0 < ((79325656310231:ℝ)/21504000000000) := by norm_num
  -- arctan bound
  have htovx : t / x ≤ ((1:ℝ)/2) := by
    rw [div_le_iff₀ hxpos]
    have htu_le : (3:ℝ) ≤ ((1:ℝ)/2) * x := by
      calc
        (3:ℝ) = ((1:ℝ)/2) * (6:ℝ) := by norm_num
        _ ≤ ((1:ℝ)/2) * x := mul_le_mul_of_nonneg_left hxl (by norm_num : 0 ≤ ((1:ℝ)/2))
    nlinarith [htu_le]
  have hAT : Real.arctan (t / x) ≤ ((74783:ℝ)/161280) := (arctan_mono htovx).trans vatan_ub_m1_2
  have hθsq : (Real.arctan (t / x)) ^ 2 ≤ (((74783:ℝ)/161280)) ^ 2 := by
    have hθn : 0 ≤ Real.arctan (t / x) := Real.arctan_nonneg.mpr (div_nonneg (le_of_lt htpos) (le_of_lt hxpos))
    have hAn : 0 ≤ ((74783:ℝ)/161280) := by norm_num
    rw [sq_le_sq]
    rw [abs_of_nonneg hθn, abs_of_nonneg hAn]
    exact hAT
  have hQden : (Real.arctan (t / x)) ^ 2 / Real.log (x ^ 2 + t ^ 2) ≤
      (((74783:ℝ)/161280)) ^ 2 / (((79325656310231:ℝ)/21504000000000)) := by
    have h1 : (Real.arctan (t / x)) ^ 2 / Real.log (x ^ 2 + t ^ 2) ≤
        (Real.arctan (t / x)) ^ 2 / ((79325656310231:ℝ)/21504000000000) := by
      exact div_le_div_of_nonneg_left (sq_nonneg _) hLDpos (by linarith : ((79325656310231:ℝ)/21504000000000) ≤ Real.log (x ^ 2 + t ^ 2))
    have h2 : (Real.arctan (t / x)) ^ 2 / ((79325656310231:ℝ)/21504000000000) ≤ (((74783:ℝ)/161280)) ^ 2 / ((79325656310231:ℝ)/21504000000000) := by
      exact div_le_div_of_nonneg_right hθsq (le_of_lt hLDpos)
    exact h1.trans h2
  -- P bound
  have hP : (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) ≤ ((79057:ℝ)/1000000) := by
    have hsqrt : Real.sqrt (40:ℝ) ≤ Real.sqrt (x ^ 2 + t ^ 2) := Real.sqrt_le_sqrt hQ3le
    have hd1 : (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) ≤ (1 : ℝ) / (2 * Real.sqrt (40:ℝ)) := by
      have hdenpos : 0 < 2 * Real.sqrt (40:ℝ) := by positivity
      exact div_le_div_of_nonneg_left (by norm_num : 0 ≤ (1 : ℝ)) hdenpos (by nlinarith)
    exact hd1.trans (inv_two_sqrt_le (40:ℝ) (by norm_num) ((79057:ℝ)/1000000) (by norm_num) (by norm_num))
  -- S bound
  have hS : Real.log (x ^ 2 + t ^ 2) / 2 - Real.log (2 + t) ≤ (1 / 2) * ((1289916814460870769681:ℝ)/300647710720000000000) - ((6931471803:ℝ)/5000000000) := by
    nlinarith [hlogU, hDL]
  exact combine x t hxpos htpos ((1289916814460870769681:ℝ)/300647710720000000000) ((6931471803:ℝ)/5000000000) ((79325656310231:ℝ)/21504000000000) ((74783:ℝ)/161280) ((79057:ℝ)/1000000) hLDpos hS hQden hP (by norm_num)

private lemma box_7_3 (x t : ℝ) (hx1 : 1 ≤ x) (hx2 : x ≤ 8) (ht : 1 ≤ t)
    (hxl : (6:ℝ) ≤ x) (hxu : x ≤ (8:ℝ)) (htl : (3:ℝ) ≤ t) (htu : t ≤ (4:ℝ)) :
    Real.log (Real.sqrt (x ^ 2 + t ^ 2)) +
        (Real.arctan (t / x)) ^ 2 / (2 * Real.log (Real.sqrt (x ^ 2 + t ^ 2))) +
        (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) ≤
      Real.log (2 + t) + (3 : ℝ) / 2 := by
  have hxpos : 0 < x := by linarith
  have htpos : 0 < t := by linarith
  have hapos : 0 < x ^ 2 + t ^ 2 := by positivity
  -- upper square bound
  have hx2le : x ^ 2 ≤ ((8:ℝ)) ^ 2 := sq_le_of_nonneg (le_of_lt hxpos) hxu
  have ht2le : t ^ 2 ≤ ((4:ℝ)) ^ 2 := sq_le_of_nonneg (le_of_lt htpos) htu
  have ha_le : x ^ 2 + t ^ 2 ≤ (80:ℝ) := by
    have : ((8:ℝ)) ^ 2 + ((4:ℝ)) ^ 2 = (80:ℝ) := by norm_num
    nlinarith
  have hlogU : Real.log (x ^ 2 + t ^ 2) ≤ ((14723614743053:ℝ)/3360000000000) := by
    exact (Real.log_le_log hapos ha_le).trans vlog_ub_m80
  -- log(2+t) lower bound
  have hDmono : Real.log ((5:ℝ)) ≤ Real.log (2 + t) := by
    apply Real.log_le_log (by norm_num : 0 < (5:ℝ))
    linarith
  have hDL : ((173046727073587:ℝ)/107520000000000) ≤ Real.log (2 + t) := (vlog_lb_m5).trans hDmono
  -- lower square bound
  have hx2ge : ((6:ℝ)) ^ 2 ≤ x ^ 2 := sq_le_of_nonneg (by norm_num : 0 ≤ (6:ℝ)) hxl
  have ht2ge : ((3:ℝ)) ^ 2 ≤ t ^ 2 := sq_le_of_nonneg (by norm_num : 0 ≤ (3:ℝ)) htl
  have hQ3le : (45:ℝ) ≤ x ^ 2 + t ^ 2 := by
    have : ((6:ℝ)) ^ 2 + ((3:ℝ)) ^ 2 = (45:ℝ) := by norm_num
    nlinarith
  have hlogL : ((457782793762884993757:ℝ)/120259084288000000000) ≤ Real.log (x ^ 2 + t ^ 2) := by
    exact (vlog_lb_m45).trans (Real.log_le_log (by norm_num : 0 < (45:ℝ)) hQ3le)
  have hLDpos : 0 < ((457782793762884993757:ℝ)/120259084288000000000) := by norm_num
  -- arctan bound
  have htovx : t / x ≤ ((2:ℝ)/3) := by
    rw [div_le_iff₀ hxpos]
    have htu_le : (4:ℝ) ≤ ((2:ℝ)/3) * x := by
      calc
        (4:ℝ) = ((2:ℝ)/3) * (6:ℝ) := by norm_num
        _ ≤ ((2:ℝ)/3) * x := mul_le_mul_of_nonneg_left hxl (by norm_num : 0 ≤ ((2:ℝ)/3))
    nlinarith [htu_le]
  have hAT : Real.arctan (t / x) ≤ ((3650446:ℝ)/6200145) := (arctan_mono htovx).trans vatan_ub_m2_3
  have hθsq : (Real.arctan (t / x)) ^ 2 ≤ (((3650446:ℝ)/6200145)) ^ 2 := by
    have hθn : 0 ≤ Real.arctan (t / x) := Real.arctan_nonneg.mpr (div_nonneg (le_of_lt htpos) (le_of_lt hxpos))
    have hAn : 0 ≤ ((3650446:ℝ)/6200145) := by norm_num
    rw [sq_le_sq]
    rw [abs_of_nonneg hθn, abs_of_nonneg hAn]
    exact hAT
  have hQden : (Real.arctan (t / x)) ^ 2 / Real.log (x ^ 2 + t ^ 2) ≤
      (((3650446:ℝ)/6200145)) ^ 2 / (((457782793762884993757:ℝ)/120259084288000000000)) := by
    have h1 : (Real.arctan (t / x)) ^ 2 / Real.log (x ^ 2 + t ^ 2) ≤
        (Real.arctan (t / x)) ^ 2 / ((457782793762884993757:ℝ)/120259084288000000000) := by
      exact div_le_div_of_nonneg_left (sq_nonneg _) hLDpos (by linarith : ((457782793762884993757:ℝ)/120259084288000000000) ≤ Real.log (x ^ 2 + t ^ 2))
    have h2 : (Real.arctan (t / x)) ^ 2 / ((457782793762884993757:ℝ)/120259084288000000000) ≤ (((3650446:ℝ)/6200145)) ^ 2 / ((457782793762884993757:ℝ)/120259084288000000000) := by
      exact div_le_div_of_nonneg_right hθsq (le_of_lt hLDpos)
    exact h1.trans h2
  -- P bound
  have hP : (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) ≤ ((9317:ℝ)/125000) := by
    have hsqrt : Real.sqrt (45:ℝ) ≤ Real.sqrt (x ^ 2 + t ^ 2) := Real.sqrt_le_sqrt hQ3le
    have hd1 : (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) ≤ (1 : ℝ) / (2 * Real.sqrt (45:ℝ)) := by
      have hdenpos : 0 < 2 * Real.sqrt (45:ℝ) := by positivity
      exact div_le_div_of_nonneg_left (by norm_num : 0 ≤ (1 : ℝ)) hdenpos (by nlinarith)
    exact hd1.trans (inv_two_sqrt_le (45:ℝ) (by norm_num) ((9317:ℝ)/125000) (by norm_num) (by norm_num))
  -- S bound
  have hS : Real.log (x ^ 2 + t ^ 2) / 2 - Real.log (2 + t) ≤ (1 / 2) * ((14723614743053:ℝ)/3360000000000) - ((173046727073587:ℝ)/107520000000000) := by
    nlinarith [hlogU, hDL]
  exact combine x t hxpos htpos ((14723614743053:ℝ)/3360000000000) ((173046727073587:ℝ)/107520000000000) ((457782793762884993757:ℝ)/120259084288000000000) ((3650446:ℝ)/6200145) ((9317:ℝ)/125000) hLDpos hS hQden hP (by norm_num)

private lemma box_7_4 (x t : ℝ) (hx1 : 1 ≤ x) (hx2 : x ≤ 8) (ht : 1 ≤ t)
    (hxl : (6:ℝ) ≤ x) (hxu : x ≤ (8:ℝ)) (htl : (4:ℝ) ≤ t) (htu : t ≤ (6:ℝ)) :
    Real.log (Real.sqrt (x ^ 2 + t ^ 2)) +
        (Real.arctan (t / x)) ^ 2 / (2 * Real.log (Real.sqrt (x ^ 2 + t ^ 2))) +
        (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) ≤
      Real.log (2 + t) + (3 : ℝ) / 2 := by
  have hxpos : 0 < x := by linarith
  have htpos : 0 < t := by linarith
  have hapos : 0 < x ^ 2 + t ^ 2 := by positivity
  -- upper square bound
  have hx2le : x ^ 2 ≤ ((8:ℝ)) ^ 2 := sq_le_of_nonneg (le_of_lt hxpos) hxu
  have ht2le : t ^ 2 ≤ ((6:ℝ)) ^ 2 := sq_le_of_nonneg (le_of_lt htpos) htu
  have ha_le : x ^ 2 + t ^ 2 ≤ (100:ℝ) := by
    have : ((8:ℝ)) ^ 2 + ((6:ℝ)) ^ 2 = (100:ℝ) := by norm_num
    nlinarith
  have hlogU : Real.log (x ^ 2 + t ^ 2) ≤ ((289732522725891511:ℝ)/62914560000000000) := by
    exact (Real.log_le_log hapos ha_le).trans vlog_ub_m100
  -- log(2+t) lower bound
  have hDmono : Real.log ((6:ℝ)) ≤ Real.log (2 + t) := by
    apply Real.log_le_log (by norm_num : 0 < (6:ℝ))
    linarith
  have hDL : ((250825351109:ℝ)/140000000000) ≤ Real.log (2 + t) := (vlog_lb_m6).trans hDmono
  -- lower square bound
  have hx2ge : ((6:ℝ)) ^ 2 ≤ x ^ 2 := sq_le_of_nonneg (by norm_num : 0 ≤ (6:ℝ)) hxl
  have ht2ge : ((4:ℝ)) ^ 2 ≤ t ^ 2 := sq_le_of_nonneg (by norm_num : 0 ≤ (4:ℝ)) htl
  have hQ3le : (52:ℝ) ≤ x ^ 2 + t ^ 2 := by
    have : ((6:ℝ)) ^ 2 + ((4:ℝ)) ^ 2 = (52:ℝ) := by norm_num
    nlinarith
  have hlogL : ((36252810578103897:ℝ)/9175040000000000) ≤ Real.log (x ^ 2 + t ^ 2) := by
    exact (vlog_lb_m52).trans (Real.log_le_log (by norm_num : 0 < (52:ℝ)) hQ3le)
  have hLDpos : 0 < ((36252810578103897:ℝ)/9175040000000000) := by norm_num
  -- arctan bound
  have htovx : t / x ≤ (1:ℝ) := by
    rw [div_le_iff₀ hxpos]
    have htu_le : (6:ℝ) ≤ (1:ℝ) * x := by
      calc
        (6:ℝ) = (1:ℝ) * (6:ℝ) := by norm_num
        _ ≤ (1:ℝ) * x := mul_le_mul_of_nonneg_left hxl (by norm_num : 0 ≤ (1:ℝ))
    nlinarith [htu_le]
  have hAT : Real.arctan (t / x) ≤ ((263:ℝ)/315) := (arctan_mono htovx).trans vatan_ub_m1
  have hθsq : (Real.arctan (t / x)) ^ 2 ≤ (((263:ℝ)/315)) ^ 2 := by
    have hθn : 0 ≤ Real.arctan (t / x) := Real.arctan_nonneg.mpr (div_nonneg (le_of_lt htpos) (le_of_lt hxpos))
    have hAn : 0 ≤ ((263:ℝ)/315) := by norm_num
    rw [sq_le_sq]
    rw [abs_of_nonneg hθn, abs_of_nonneg hAn]
    exact hAT
  have hQden : (Real.arctan (t / x)) ^ 2 / Real.log (x ^ 2 + t ^ 2) ≤
      (((263:ℝ)/315)) ^ 2 / (((36252810578103897:ℝ)/9175040000000000)) := by
    have h1 : (Real.arctan (t / x)) ^ 2 / Real.log (x ^ 2 + t ^ 2) ≤
        (Real.arctan (t / x)) ^ 2 / ((36252810578103897:ℝ)/9175040000000000) := by
      exact div_le_div_of_nonneg_left (sq_nonneg _) hLDpos (by linarith : ((36252810578103897:ℝ)/9175040000000000) ≤ Real.log (x ^ 2 + t ^ 2))
    have h2 : (Real.arctan (t / x)) ^ 2 / ((36252810578103897:ℝ)/9175040000000000) ≤ (((263:ℝ)/315)) ^ 2 / ((36252810578103897:ℝ)/9175040000000000) := by
      exact div_le_div_of_nonneg_right hθsq (le_of_lt hLDpos)
    exact h1.trans h2
  -- P bound
  have hP : (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) ≤ ((34669:ℝ)/500000) := by
    have hsqrt : Real.sqrt (52:ℝ) ≤ Real.sqrt (x ^ 2 + t ^ 2) := Real.sqrt_le_sqrt hQ3le
    have hd1 : (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) ≤ (1 : ℝ) / (2 * Real.sqrt (52:ℝ)) := by
      have hdenpos : 0 < 2 * Real.sqrt (52:ℝ) := by positivity
      exact div_le_div_of_nonneg_left (by norm_num : 0 ≤ (1 : ℝ)) hdenpos (by nlinarith)
    exact hd1.trans (inv_two_sqrt_le (52:ℝ) (by norm_num) ((34669:ℝ)/500000) (by norm_num) (by norm_num))
  -- S bound
  have hS : Real.log (x ^ 2 + t ^ 2) / 2 - Real.log (2 + t) ≤ (1 / 2) * ((289732522725891511:ℝ)/62914560000000000) - ((250825351109:ℝ)/140000000000) := by
    nlinarith [hlogU, hDL]
  exact combine x t hxpos htpos ((289732522725891511:ℝ)/62914560000000000) ((250825351109:ℝ)/140000000000) ((36252810578103897:ℝ)/9175040000000000) ((263:ℝ)/315) ((34669:ℝ)/500000) hLDpos hS hQden hP (by norm_num)

private lemma box_7_5 (x t : ℝ) (hx1 : 1 ≤ x) (hx2 : x ≤ 8) (ht : 1 ≤ t)
    (hxl : (6:ℝ) ≤ x) (hxu : x ≤ (8:ℝ)) (htl : (6:ℝ) ≤ t) (htu : t ≤ (9:ℝ)) :
    Real.log (Real.sqrt (x ^ 2 + t ^ 2)) +
        (Real.arctan (t / x)) ^ 2 / (2 * Real.log (Real.sqrt (x ^ 2 + t ^ 2))) +
        (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) ≤
      Real.log (2 + t) + (3 : ℝ) / 2 := by
  have hxpos : 0 < x := by linarith
  have htpos : 0 < t := by linarith
  have hapos : 0 < x ^ 2 + t ^ 2 := by positivity
  -- upper square bound
  have hx2le : x ^ 2 ≤ ((8:ℝ)) ^ 2 := sq_le_of_nonneg (le_of_lt hxpos) hxu
  have ht2le : t ^ 2 ≤ ((9:ℝ)) ^ 2 := sq_le_of_nonneg (le_of_lt htpos) htu
  have ha_le : x ^ 2 + t ^ 2 ≤ (145:ℝ) := by
    have : ((8:ℝ)) ^ 2 + ((9:ℝ)) ^ 2 = (145:ℝ) := by norm_num
    nlinarith
  have hlogU : Real.log (x ^ 2 + t ^ 2) ≤ ((574557546348049165363963:ℝ)/115448720916480000000000) := by
    exact (Real.log_le_log hapos ha_le).trans vlog_ub_m145
  -- log(2+t) lower bound
  have hDmono : Real.log ((8:ℝ)) ≤ Real.log (2 + t) := by
    apply Real.log_le_log (by norm_num : 0 < (8:ℝ))
    linarith
  have hDL : ((20794415409:ℝ)/10000000000) ≤ Real.log (2 + t) := (vlog_lb_m8).trans hDmono
  -- lower square bound
  have hx2ge : ((6:ℝ)) ^ 2 ≤ x ^ 2 := sq_le_of_nonneg (by norm_num : 0 ≤ (6:ℝ)) hxl
  have ht2ge : ((6:ℝ)) ^ 2 ≤ t ^ 2 := sq_le_of_nonneg (by norm_num : 0 ≤ (6:ℝ)) htl
  have hQ3le : (72:ℝ) ≤ x ^ 2 + t ^ 2 := by
    have : ((6:ℝ)) ^ 2 + ((6:ℝ)) ^ 2 = (72:ℝ) := by norm_num
    nlinarith
  have hlogL : ((39238582687478897:ℝ)/9175040000000000) ≤ Real.log (x ^ 2 + t ^ 2) := by
    exact (vlog_lb_m72).trans (Real.log_le_log (by norm_num : 0 < (72:ℝ)) hQ3le)
  have hLDpos : 0 < ((39238582687478897:ℝ)/9175040000000000) := by norm_num
  -- arctan bound
  have htovx : t / x ≤ ((3:ℝ)/2) := by
    rw [div_le_iff₀ hxpos]
    have htu_le : (9:ℝ) ≤ ((3:ℝ)/2) * x := by
      calc
        (9:ℝ) = ((3:ℝ)/2) * (6:ℝ) := by norm_num
        _ ≤ ((3:ℝ)/2) * x := mul_le_mul_of_nonneg_left hxl (by norm_num : 0 ≤ ((3:ℝ)/2))
    nlinarith [htu_le]
  have hAT : Real.arctan (t / x) ≤ ((37695443:ℝ)/38272500) := (arctan_mono htovx).trans vatan_ub_m3_2
  have hθsq : (Real.arctan (t / x)) ^ 2 ≤ (((37695443:ℝ)/38272500)) ^ 2 := by
    have hθn : 0 ≤ Real.arctan (t / x) := Real.arctan_nonneg.mpr (div_nonneg (le_of_lt htpos) (le_of_lt hxpos))
    have hAn : 0 ≤ ((37695443:ℝ)/38272500) := by norm_num
    rw [sq_le_sq]
    rw [abs_of_nonneg hθn, abs_of_nonneg hAn]
    exact hAT
  have hQden : (Real.arctan (t / x)) ^ 2 / Real.log (x ^ 2 + t ^ 2) ≤
      (((37695443:ℝ)/38272500)) ^ 2 / (((39238582687478897:ℝ)/9175040000000000)) := by
    have h1 : (Real.arctan (t / x)) ^ 2 / Real.log (x ^ 2 + t ^ 2) ≤
        (Real.arctan (t / x)) ^ 2 / ((39238582687478897:ℝ)/9175040000000000) := by
      exact div_le_div_of_nonneg_left (sq_nonneg _) hLDpos (by linarith : ((39238582687478897:ℝ)/9175040000000000) ≤ Real.log (x ^ 2 + t ^ 2))
    have h2 : (Real.arctan (t / x)) ^ 2 / ((39238582687478897:ℝ)/9175040000000000) ≤ (((37695443:ℝ)/38272500)) ^ 2 / ((39238582687478897:ℝ)/9175040000000000) := by
      exact div_le_div_of_nonneg_right hθsq (le_of_lt hLDpos)
    exact h1.trans h2
  -- P bound
  have hP : (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) ≤ ((29463:ℝ)/500000) := by
    have hsqrt : Real.sqrt (72:ℝ) ≤ Real.sqrt (x ^ 2 + t ^ 2) := Real.sqrt_le_sqrt hQ3le
    have hd1 : (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) ≤ (1 : ℝ) / (2 * Real.sqrt (72:ℝ)) := by
      have hdenpos : 0 < 2 * Real.sqrt (72:ℝ) := by positivity
      exact div_le_div_of_nonneg_left (by norm_num : 0 ≤ (1 : ℝ)) hdenpos (by nlinarith)
    exact hd1.trans (inv_two_sqrt_le (72:ℝ) (by norm_num) ((29463:ℝ)/500000) (by norm_num) (by norm_num))
  -- S bound
  have hS : Real.log (x ^ 2 + t ^ 2) / 2 - Real.log (2 + t) ≤ (1 / 2) * ((574557546348049165363963:ℝ)/115448720916480000000000) - ((20794415409:ℝ)/10000000000) := by
    nlinarith [hlogU, hDL]
  exact combine x t hxpos htpos ((574557546348049165363963:ℝ)/115448720916480000000000) ((20794415409:ℝ)/10000000000) ((39238582687478897:ℝ)/9175040000000000) ((37695443:ℝ)/38272500) ((29463:ℝ)/500000) hLDpos hS hQden hP (by norm_num)

private lemma box_7_6 (x t : ℝ) (hx1 : 1 ≤ x) (hx2 : x ≤ 8) (ht : 1 ≤ t)
    (hxl : (6:ℝ) ≤ x) (hxu : x ≤ (8:ℝ)) (htl : (9:ℝ) ≤ t) (htu : t ≤ (13:ℝ)) :
    Real.log (Real.sqrt (x ^ 2 + t ^ 2)) +
        (Real.arctan (t / x)) ^ 2 / (2 * Real.log (Real.sqrt (x ^ 2 + t ^ 2))) +
        (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) ≤
      Real.log (2 + t) + (3 : ℝ) / 2 := by
  have hxpos : 0 < x := by linarith
  have htpos : 0 < t := by linarith
  have hapos : 0 < x ^ 2 + t ^ 2 := by positivity
  -- upper square bound
  have hx2le : x ^ 2 ≤ ((8:ℝ)) ^ 2 := sq_le_of_nonneg (le_of_lt hxpos) hxu
  have ht2le : t ^ 2 ≤ ((13:ℝ)) ^ 2 := sq_le_of_nonneg (le_of_lt htpos) htu
  have ha_le : x ^ 2 + t ^ 2 ≤ (233:ℝ) := by
    have : ((8:ℝ)) ^ 2 + ((13:ℝ)) ^ 2 = (233:ℝ) := by norm_num
    nlinarith
  have hlogU : Real.log (x ^ 2 + t ^ 2) ≤ ((89902202599758426352471:ℝ)/16492674416640000000000) := by
    exact (Real.log_le_log hapos ha_le).trans vlog_ub_m233
  -- log(2+t) lower bound
  have hDmono : Real.log ((11:ℝ)) ≤ Real.log (2 + t) := by
    apply Real.log_le_log (by norm_num : 0 < (11:ℝ))
    linarith
  have hDL : ((22000673184559761:ℝ)/9175040000000000) ≤ Real.log (2 + t) := (vlog_lb_m11).trans hDmono
  -- lower square bound
  have hx2ge : ((6:ℝ)) ^ 2 ≤ x ^ 2 := sq_le_of_nonneg (by norm_num : 0 ≤ (6:ℝ)) hxl
  have ht2ge : ((9:ℝ)) ^ 2 ≤ t ^ 2 := sq_le_of_nonneg (by norm_num : 0 ≤ (9:ℝ)) htl
  have hQ3le : (117:ℝ) ≤ x ^ 2 + t ^ 2 := by
    have : ((6:ℝ)) ^ 2 + ((9:ℝ)) ^ 2 = (117:ℝ) := by norm_num
    nlinarith
  have hlogL : ((91631148136616734304693:ℝ)/19241453486080000000000) ≤ Real.log (x ^ 2 + t ^ 2) := by
    exact (vlog_lb_m117).trans (Real.log_le_log (by norm_num : 0 < (117:ℝ)) hQ3le)
  have hLDpos : 0 < ((91631148136616734304693:ℝ)/19241453486080000000000) := by norm_num
  -- arctan bound
  have htovx : t / x ≤ ((13:ℝ)/6) := by
    rw [div_le_iff₀ hxpos]
    have htu_le : (13:ℝ) ≤ ((13:ℝ)/6) * x := by
      calc
        (13:ℝ) = ((13:ℝ)/6) * (6:ℝ) := by norm_num
        _ ≤ ((13:ℝ)/6) * x := mul_le_mul_of_nonneg_left hxl (by norm_num : 0 ≤ ((13:ℝ)/6))
    nlinarith [htu_le]
  have hAT : Real.arctan (t / x) ≤ ((1250166234813:ℝ)/1098099047500) := (arctan_mono htovx).trans vatan_ub_m13_6
  have hθsq : (Real.arctan (t / x)) ^ 2 ≤ (((1250166234813:ℝ)/1098099047500)) ^ 2 := by
    have hθn : 0 ≤ Real.arctan (t / x) := Real.arctan_nonneg.mpr (div_nonneg (le_of_lt htpos) (le_of_lt hxpos))
    have hAn : 0 ≤ ((1250166234813:ℝ)/1098099047500) := by norm_num
    rw [sq_le_sq]
    rw [abs_of_nonneg hθn, abs_of_nonneg hAn]
    exact hAT
  have hQden : (Real.arctan (t / x)) ^ 2 / Real.log (x ^ 2 + t ^ 2) ≤
      (((1250166234813:ℝ)/1098099047500)) ^ 2 / (((91631148136616734304693:ℝ)/19241453486080000000000)) := by
    have h1 : (Real.arctan (t / x)) ^ 2 / Real.log (x ^ 2 + t ^ 2) ≤
        (Real.arctan (t / x)) ^ 2 / ((91631148136616734304693:ℝ)/19241453486080000000000) := by
      exact div_le_div_of_nonneg_left (sq_nonneg _) hLDpos (by linarith : ((91631148136616734304693:ℝ)/19241453486080000000000) ≤ Real.log (x ^ 2 + t ^ 2))
    have h2 : (Real.arctan (t / x)) ^ 2 / ((91631148136616734304693:ℝ)/19241453486080000000000) ≤ (((1250166234813:ℝ)/1098099047500)) ^ 2 / ((91631148136616734304693:ℝ)/19241453486080000000000) := by
      exact div_le_div_of_nonneg_right hθsq (le_of_lt hLDpos)
    exact h1.trans h2
  -- P bound
  have hP : (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) ≤ ((23113:ℝ)/500000) := by
    have hsqrt : Real.sqrt (117:ℝ) ≤ Real.sqrt (x ^ 2 + t ^ 2) := Real.sqrt_le_sqrt hQ3le
    have hd1 : (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) ≤ (1 : ℝ) / (2 * Real.sqrt (117:ℝ)) := by
      have hdenpos : 0 < 2 * Real.sqrt (117:ℝ) := by positivity
      exact div_le_div_of_nonneg_left (by norm_num : 0 ≤ (1 : ℝ)) hdenpos (by nlinarith)
    exact hd1.trans (inv_two_sqrt_le (117:ℝ) (by norm_num) ((23113:ℝ)/500000) (by norm_num) (by norm_num))
  -- S bound
  have hS : Real.log (x ^ 2 + t ^ 2) / 2 - Real.log (2 + t) ≤ (1 / 2) * ((89902202599758426352471:ℝ)/16492674416640000000000) - ((22000673184559761:ℝ)/9175040000000000) := by
    nlinarith [hlogU, hDL]
  exact combine x t hxpos htpos ((89902202599758426352471:ℝ)/16492674416640000000000) ((22000673184559761:ℝ)/9175040000000000) ((91631148136616734304693:ℝ)/19241453486080000000000) ((1250166234813:ℝ)/1098099047500) ((23113:ℝ)/500000) hLDpos hS hQden hP (by norm_num)

private lemma box_7_7 (x t : ℝ) (hx1 : 1 ≤ x) (hx2 : x ≤ 8) (ht : 1 ≤ t)
    (hxl : (6:ℝ) ≤ x) (hxu : x ≤ (8:ℝ)) (htl : (13:ℝ) ≤ t) (htu : t ≤ (15:ℝ)) :
    Real.log (Real.sqrt (x ^ 2 + t ^ 2)) +
        (Real.arctan (t / x)) ^ 2 / (2 * Real.log (Real.sqrt (x ^ 2 + t ^ 2))) +
        (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) ≤
      Real.log (2 + t) + (3 : ℝ) / 2 := by
  have hxpos : 0 < x := by linarith
  have htpos : 0 < t := by linarith
  have hapos : 0 < x ^ 2 + t ^ 2 := by positivity
  -- upper square bound
  have hx2le : x ^ 2 ≤ ((8:ℝ)) ^ 2 := sq_le_of_nonneg (le_of_lt hxpos) hxu
  have ht2le : t ^ 2 ≤ ((15:ℝ)) ^ 2 := sq_le_of_nonneg (le_of_lt htpos) htu
  have ha_le : x ^ 2 + t ^ 2 ≤ (289:ℝ) := by
    have : ((8:ℝ)) ^ 2 + ((15:ℝ)) ^ 2 = (289:ℝ) := by norm_num
    nlinarith
  have hlogU : Real.log (x ^ 2 + t ^ 2) ≤ ((27911753152792324867870297:ℝ)/4925812092436480000000000) := by
    exact (Real.log_le_log hapos ha_le).trans vlog_ub_m289
  -- log(2+t) lower bound
  have hDmono : Real.log ((15:ℝ)) ≤ Real.log (2 + t) := by
    apply Real.log_le_log (by norm_num : 0 < (15:ℝ))
    linarith
  have hDL : ((24846468902980723:ℝ)/9175040000000000) ≤ Real.log (2 + t) := (vlog_lb_m15).trans hDmono
  -- lower square bound
  have hx2ge : ((6:ℝ)) ^ 2 ≤ x ^ 2 := sq_le_of_nonneg (by norm_num : 0 ≤ (6:ℝ)) hxl
  have ht2ge : ((13:ℝ)) ^ 2 ≤ t ^ 2 := sq_le_of_nonneg (by norm_num : 0 ≤ (13:ℝ)) htl
  have hQ3le : (205:ℝ) ≤ x ^ 2 + t ^ 2 := by
    have : ((6:ℝ)) ^ 2 + ((13:ℝ)) ^ 2 = (205:ℝ) := by norm_num
    nlinarith
  have hlogL : ((13110070003415114261757501:ℝ)/2462906046218240000000000) ≤ Real.log (x ^ 2 + t ^ 2) := by
    exact (vlog_lb_m205).trans (Real.log_le_log (by norm_num : 0 < (205:ℝ)) hQ3le)
  have hLDpos : 0 < ((13110070003415114261757501:ℝ)/2462906046218240000000000) := by norm_num
  -- arctan bound
  have htovx : t / x ≤ ((5:ℝ)/2) := by
    rw [div_le_iff₀ hxpos]
    have htu_le : (15:ℝ) ≤ ((5:ℝ)/2) * x := by
      calc
        (15:ℝ) = ((5:ℝ)/2) * (6:ℝ) := by norm_num
        _ ≤ ((5:ℝ)/2) * x := mul_le_mul_of_nonneg_left hxl (by norm_num : 0 ≤ ((5:ℝ)/2))
    nlinarith [htu_le]
  have hAT : Real.arctan (t / x) ≤ ((7811471:ℝ)/6562500) := (arctan_mono htovx).trans vatan_ub_m5_2
  have hθsq : (Real.arctan (t / x)) ^ 2 ≤ (((7811471:ℝ)/6562500)) ^ 2 := by
    have hθn : 0 ≤ Real.arctan (t / x) := Real.arctan_nonneg.mpr (div_nonneg (le_of_lt htpos) (le_of_lt hxpos))
    have hAn : 0 ≤ ((7811471:ℝ)/6562500) := by norm_num
    rw [sq_le_sq]
    rw [abs_of_nonneg hθn, abs_of_nonneg hAn]
    exact hAT
  have hQden : (Real.arctan (t / x)) ^ 2 / Real.log (x ^ 2 + t ^ 2) ≤
      (((7811471:ℝ)/6562500)) ^ 2 / (((13110070003415114261757501:ℝ)/2462906046218240000000000)) := by
    have h1 : (Real.arctan (t / x)) ^ 2 / Real.log (x ^ 2 + t ^ 2) ≤
        (Real.arctan (t / x)) ^ 2 / ((13110070003415114261757501:ℝ)/2462906046218240000000000) := by
      exact div_le_div_of_nonneg_left (sq_nonneg _) hLDpos (by linarith : ((13110070003415114261757501:ℝ)/2462906046218240000000000) ≤ Real.log (x ^ 2 + t ^ 2))
    have h2 : (Real.arctan (t / x)) ^ 2 / ((13110070003415114261757501:ℝ)/2462906046218240000000000) ≤ (((7811471:ℝ)/6562500)) ^ 2 / ((13110070003415114261757501:ℝ)/2462906046218240000000000) := by
      exact div_le_div_of_nonneg_right hθsq (le_of_lt hLDpos)
    exact h1.trans h2
  -- P bound
  have hP : (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) ≤ ((17461:ℝ)/500000) := by
    have hsqrt : Real.sqrt (205:ℝ) ≤ Real.sqrt (x ^ 2 + t ^ 2) := Real.sqrt_le_sqrt hQ3le
    have hd1 : (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) ≤ (1 : ℝ) / (2 * Real.sqrt (205:ℝ)) := by
      have hdenpos : 0 < 2 * Real.sqrt (205:ℝ) := by positivity
      exact div_le_div_of_nonneg_left (by norm_num : 0 ≤ (1 : ℝ)) hdenpos (by nlinarith)
    exact hd1.trans (inv_two_sqrt_le (205:ℝ) (by norm_num) ((17461:ℝ)/500000) (by norm_num) (by norm_num))
  -- S bound
  have hS : Real.log (x ^ 2 + t ^ 2) / 2 - Real.log (2 + t) ≤ (1 / 2) * ((27911753152792324867870297:ℝ)/4925812092436480000000000) - ((24846468902980723:ℝ)/9175040000000000) := by
    nlinarith [hlogU, hDL]
  exact combine x t hxpos htpos ((27911753152792324867870297:ℝ)/4925812092436480000000000) ((24846468902980723:ℝ)/9175040000000000) ((13110070003415114261757501:ℝ)/2462906046218240000000000) ((7811471:ℝ)/6562500) ((17461:ℝ)/500000) hLDpos hS hQden hP (by norm_num)

private lemma log15_gt_two : (2:ℝ) < Real.log (15:ℝ) := by
  have he : Real.exp 1 < 3 := by
    have h := exp_one_lt_d9
    norm_num at h
    linarith
  have hlog3 : (1:ℝ) < Real.log (3:ℝ) := by
    have hlt := Real.log_lt_log (by positivity : 0 < Real.exp 1) he
    simpa using hlt
  have h915 : (9:ℝ) < (15:ℝ) := by norm_num
  have hl : Real.log (9:ℝ) < Real.log (15:ℝ) := Real.log_lt_log (by norm_num : (0:ℝ) < (9:ℝ)) h915
  have hlog9 : Real.log (9:ℝ) = 2 * Real.log (3:ℝ) := by
    calc
      Real.log (9:ℝ) = Real.log ((3:ℝ) ^ 2) := by rw [show (9:ℝ) = (3:ℝ)^2 by norm_num]
      _ = (2:ℕ) * Real.log 3 := by rw [Real.log_pow]
      _ = 2 * Real.log (3:ℝ) := by norm_num
  nlinarith

private lemma tail (x t : ℝ) (hx1 : 1 ≤ x) (hx2 : x ≤ 8) (ht : 1 ≤ t) (h15 : 15 ≤ t) :
    Real.log (Real.sqrt (x ^ 2 + t ^ 2)) +
        (Real.arctan (t / x)) ^ 2 / (2 * Real.log (Real.sqrt (x ^ 2 + t ^ 2))) +
        (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) ≤
      Real.log (2 + t) + (3 : ℝ) / 2 := by
  have hxpos : 0 < x := by linarith
  have htpos : 0 < t := by linarith
  have hρ_le : Real.sqrt (x ^ 2 + t ^ 2) ≤ 2 + t := by
    have hx2sq : x ^ 2 ≤ 64 := by
      have h8 : x ^ 2 ≤ (8:ℝ) ^ 2 := sq_le_of_nonneg (le_of_lt hxpos) hx2
      nlinarith
    have hsq1 : x ^ 2 + t ^ 2 ≤ 64 + t ^ 2 := by nlinarith
    have hsq2 : 64 + t ^ 2 ≤ (2 + t) ^ 2 := by nlinarith
    calc
      Real.sqrt (x ^ 2 + t ^ 2) ≤ Real.sqrt ((2 + t) ^ 2) := Real.sqrt_le_sqrt (hsq1.trans hsq2)
      _ = 2 + t := by
        rw [Real.sqrt_sq_eq_abs]
        rw [abs_of_nonneg (by linarith : 0 ≤ 2 + t)]
  have hlogle : Real.log (Real.sqrt (x ^ 2 + t ^ 2)) ≤ Real.log (2 + t) := by
    exact Real.log_le_log (by positivity) hρ_le
  have hlogρ2 : (2:ℝ) ≤ Real.log (Real.sqrt (x ^ 2 + t ^ 2)) := by
    have ht2 : t ^ 2 ≤ x ^ 2 + t ^ 2 := by nlinarith
    have hsqrt : Real.sqrt (t ^ 2) ≤ Real.sqrt (x ^ 2 + t ^ 2) := Real.sqrt_le_sqrt ht2
    have hsqrt_t : Real.sqrt (t ^ 2) = t := by
      rw [Real.sqrt_sq_eq_abs]
      rw [abs_of_nonneg (le_of_lt htpos)]
    have hle_t : t ≤ Real.sqrt (x ^ 2 + t ^ 2) := by
      calc
        t = Real.sqrt (t ^ 2) := hsqrt_t.symm
        _ ≤ Real.sqrt (x ^ 2 + t ^ 2) := hsqrt
    have hlogt2 : Real.log t ≤ Real.log (Real.sqrt (x ^ 2 + t ^ 2)) := by
      exact Real.log_le_log (by positivity : 0 < t) hle_t
    have hlog15_le_logt : Real.log (15:ℝ) ≤ Real.log t := by
      exact Real.log_le_log (by norm_num : (0:ℝ) < (15:ℝ)) (by linarith)
    have h15 : (2:ℝ) ≤ Real.log (15:ℝ) := le_of_lt log15_gt_two
    nlinarith
  have hQ : (Real.arctan (t / x)) ^ 2 / (2 * Real.log (Real.sqrt (x ^ 2 + t ^ 2))) ≤ 1 := by
    have hden : 0 < 2 * Real.log (Real.sqrt (x ^ 2 + t ^ 2)) := by
      have h : 0 < Real.log (Real.sqrt (x ^ 2 + t ^ 2)) := by linarith
      positivity
    have hθ2 : (Real.arctan (t / x)) ^ 2 ≤ 4 := by
      have hθ : Real.arctan (t / x) ≤ Real.pi / 2 := (Real.arctan_lt_pi_div_two (t / x)).le
      have hθn : 0 ≤ Real.arctan (t / x) := Real.arctan_nonneg.mpr (div_nonneg (le_of_lt htpos) (le_of_lt hxpos))
      have hpi2lt : Real.pi / 2 < 2 := by linarith [Real.pi_lt_four]
      have h1 : (Real.arctan (t / x)) ^ 2 ≤ (Real.pi / 2) ^ 2 := by
        rw [sq_le_sq]
        rw [abs_of_nonneg hθn, abs_of_nonneg (by positivity : 0 ≤ Real.pi / 2)]
        exact hθ
      have h2 : (Real.pi / 2) ^ 2 ≤ 4 := by
        nlinarith [sq_le_of_nonneg (by positivity : 0 ≤ Real.pi / 2) (le_of_lt hpi2lt)]
      nlinarith
    have hmain : (Real.arctan (t / x)) ^ 2 ≤ 2 * Real.log (Real.sqrt (x ^ 2 + t ^ 2)) := by
      nlinarith [hθ2, hlogρ2]
    exact (div_le_iff₀ hden).2 (by simpa using hmain)
  have hP : (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) ≤ (1 : ℝ) / 30 := by
    have hsq_t : Real.sqrt (t ^ 2) ≤ Real.sqrt (x ^ 2 + t ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
    have hsqrt_t : Real.sqrt (t ^ 2) = t := by
      rw [Real.sqrt_sq_eq_abs]
      rw [abs_of_nonneg (le_of_lt htpos)]
    have hρ15 : 15 ≤ Real.sqrt (x ^ 2 + t ^ 2) := by
      have hle_t : t ≤ Real.sqrt (x ^ 2 + t ^ 2) := by
        calc
          t = Real.sqrt (t ^ 2) := hsqrt_t.symm
          _ ≤ Real.sqrt (x ^ 2 + t ^ 2) := hsq_t
      linarith
    have hdenle : 30 ≤ 2 * Real.sqrt (x ^ 2 + t ^ 2) := by nlinarith
    exact div_le_div_of_nonneg_left (by norm_num : (0:ℝ) ≤ 1) (by norm_num : (0:ℝ) < (30:ℝ)) (by nlinarith)
  have hsum : (Real.arctan (t / x)) ^ 2 / (2 * Real.log (Real.sqrt (x ^ 2 + t ^ 2))) +
      (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) ≤ (3 : ℝ) / 2 := by
    have : (1:ℝ) + (1:ℝ)/30 ≤ (3:ℝ)/2 := by norm_num
    nlinarith
  calc
    Real.log (Real.sqrt (x ^ 2 + t ^ 2)) +
        (Real.arctan (t / x)) ^ 2 / (2 * Real.log (Real.sqrt (x ^ 2 + t ^ 2))) +
        (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2))
        ≤ Real.log (2 + t) + (Real.arctan (t / x)) ^ 2 / (2 * Real.log (Real.sqrt (x ^ 2 + t ^ 2))) +
            (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) := by
            nlinarith [hlogle]
    _ ≤ Real.log (2 + t) + (3 : ℝ) / 2 := by
            nlinarith [hsum]



theorem log_strip_quad (x t : ℝ) (hx1 : 1 ≤ x) (hx2 : x ≤ 8) (ht : 1 ≤ t) :
    Real.log (Real.sqrt (x ^ 2 + t ^ 2)) +
        (Real.arctan (t / x)) ^ 2 / (2 * Real.log (Real.sqrt (x ^ 2 + t ^ 2))) +
        (1 : ℝ) / (2 * Real.sqrt (x ^ 2 + t ^ 2)) ≤
      Real.log (2 + t) + (3 : ℝ) / 2 := by
  by_cases ht15 : 15 ≤ t
  · exact tail x t hx1 hx2 ht (by linarith)
  · have htlt : t ≤ 15 := by linarith

    by_cases hx_0 : x <= ((6:ℝ)/5)
    ·
      by_cases ht_0_0 : t <= ((3:ℝ)/2)
      ·
        exact box_0_0 x t hx1 hx2 ht (by linarith) (by linarith) (by linarith) (by linarith)
      ·
        by_cases ht_0_1 : t <= (2:ℝ)
        ·
          exact box_0_1 x t hx1 hx2 ht (by linarith) (by linarith) (by linarith) (by linarith)
        ·
          by_cases ht_0_2 : t <= (3:ℝ)
          ·
            exact box_0_2 x t hx1 hx2 ht (by linarith) (by linarith) (by linarith) (by linarith)
          ·
            by_cases ht_0_3 : t <= (4:ℝ)
            ·
              exact box_0_3 x t hx1 hx2 ht (by linarith) (by linarith) (by linarith) (by linarith)
            ·
              by_cases ht_0_4 : t <= (6:ℝ)
              ·
                exact box_0_4 x t hx1 hx2 ht (by linarith) (by linarith) (by linarith) (by linarith)
              ·
                by_cases ht_0_5 : t <= (9:ℝ)
                ·
                  exact box_0_5 x t hx1 hx2 ht (by linarith) (by linarith) (by linarith) (by linarith)
                ·
                  by_cases ht_0_6 : t <= (13:ℝ)
                  ·
                    exact box_0_6 x t hx1 hx2 ht (by linarith) (by linarith) (by linarith) (by linarith)
                  ·
                    exact box_0_7 x t hx1 hx2 ht (by linarith) (by linarith) (by linarith) (by linarith)
    ·
      by_cases hx_1 : x <= ((3:ℝ)/2)
      ·
        by_cases ht_1_0 : t <= ((3:ℝ)/2)
        ·
          exact box_1_0 x t hx1 hx2 ht (by linarith) (by linarith) (by linarith) (by linarith)
        ·
          by_cases ht_1_1 : t <= (2:ℝ)
          ·
            exact box_1_1 x t hx1 hx2 ht (by linarith) (by linarith) (by linarith) (by linarith)
          ·
            by_cases ht_1_2 : t <= (3:ℝ)
            ·
              exact box_1_2 x t hx1 hx2 ht (by linarith) (by linarith) (by linarith) (by linarith)
            ·
              by_cases ht_1_3 : t <= (4:ℝ)
              ·
                exact box_1_3 x t hx1 hx2 ht (by linarith) (by linarith) (by linarith) (by linarith)
              ·
                by_cases ht_1_4 : t <= (6:ℝ)
                ·
                  exact box_1_4 x t hx1 hx2 ht (by linarith) (by linarith) (by linarith) (by linarith)
                ·
                  by_cases ht_1_5 : t <= (9:ℝ)
                  ·
                    exact box_1_5 x t hx1 hx2 ht (by linarith) (by linarith) (by linarith) (by linarith)
                  ·
                    by_cases ht_1_6 : t <= (13:ℝ)
                    ·
                      exact box_1_6 x t hx1 hx2 ht (by linarith) (by linarith) (by linarith) (by linarith)
                    ·
                      exact box_1_7 x t hx1 hx2 ht (by linarith) (by linarith) (by linarith) (by linarith)
      ·
        by_cases hx_2 : x <= (2:ℝ)
        ·
          by_cases ht_2_0 : t <= ((3:ℝ)/2)
          ·
            exact box_2_0 x t hx1 hx2 ht (by linarith) (by linarith) (by linarith) (by linarith)
          ·
            by_cases ht_2_1 : t <= (2:ℝ)
            ·
              exact box_2_1 x t hx1 hx2 ht (by linarith) (by linarith) (by linarith) (by linarith)
            ·
              by_cases ht_2_2 : t <= (3:ℝ)
              ·
                exact box_2_2 x t hx1 hx2 ht (by linarith) (by linarith) (by linarith) (by linarith)
              ·
                by_cases ht_2_3 : t <= (4:ℝ)
                ·
                  exact box_2_3 x t hx1 hx2 ht (by linarith) (by linarith) (by linarith) (by linarith)
                ·
                  by_cases ht_2_4 : t <= (6:ℝ)
                  ·
                    exact box_2_4 x t hx1 hx2 ht (by linarith) (by linarith) (by linarith) (by linarith)
                  ·
                    by_cases ht_2_5 : t <= (9:ℝ)
                    ·
                      exact box_2_5 x t hx1 hx2 ht (by linarith) (by linarith) (by linarith) (by linarith)
                    ·
                      by_cases ht_2_6 : t <= (13:ℝ)
                      ·
                        exact box_2_6 x t hx1 hx2 ht (by linarith) (by linarith) (by linarith) (by linarith)
                      ·
                        exact box_2_7 x t hx1 hx2 ht (by linarith) (by linarith) (by linarith) (by linarith)
        ·
          by_cases hx_3 : x <= ((5:ℝ)/2)
          ·
            by_cases ht_3_0 : t <= ((3:ℝ)/2)
            ·
              exact box_3_0 x t hx1 hx2 ht (by linarith) (by linarith) (by linarith) (by linarith)
            ·
              by_cases ht_3_1 : t <= (2:ℝ)
              ·
                exact box_3_1 x t hx1 hx2 ht (by linarith) (by linarith) (by linarith) (by linarith)
              ·
                by_cases ht_3_2 : t <= (3:ℝ)
                ·
                  exact box_3_2 x t hx1 hx2 ht (by linarith) (by linarith) (by linarith) (by linarith)
                ·
                  by_cases ht_3_3 : t <= (4:ℝ)
                  ·
                    exact box_3_3 x t hx1 hx2 ht (by linarith) (by linarith) (by linarith) (by linarith)
                  ·
                    by_cases ht_3_4 : t <= (6:ℝ)
                    ·
                      exact box_3_4 x t hx1 hx2 ht (by linarith) (by linarith) (by linarith) (by linarith)
                    ·
                      by_cases ht_3_5 : t <= (9:ℝ)
                      ·
                        exact box_3_5 x t hx1 hx2 ht (by linarith) (by linarith) (by linarith) (by linarith)
                      ·
                        by_cases ht_3_6 : t <= (13:ℝ)
                        ·
                          exact box_3_6 x t hx1 hx2 ht (by linarith) (by linarith) (by linarith) (by linarith)
                        ·
                          exact box_3_7 x t hx1 hx2 ht (by linarith) (by linarith) (by linarith) (by linarith)
          ·
            by_cases hx_4 : x <= (3:ℝ)
            ·
              by_cases ht_4_0 : t <= ((3:ℝ)/2)
              ·
                exact box_4_0 x t hx1 hx2 ht (by linarith) (by linarith) (by linarith) (by linarith)
              ·
                by_cases ht_4_1 : t <= (2:ℝ)
                ·
                  exact box_4_1 x t hx1 hx2 ht (by linarith) (by linarith) (by linarith) (by linarith)
                ·
                  by_cases ht_4_2 : t <= (3:ℝ)
                  ·
                    exact box_4_2 x t hx1 hx2 ht (by linarith) (by linarith) (by linarith) (by linarith)
                  ·
                    by_cases ht_4_3 : t <= (4:ℝ)
                    ·
                      exact box_4_3 x t hx1 hx2 ht (by linarith) (by linarith) (by linarith) (by linarith)
                    ·
                      by_cases ht_4_4 : t <= (6:ℝ)
                      ·
                        exact box_4_4 x t hx1 hx2 ht (by linarith) (by linarith) (by linarith) (by linarith)
                      ·
                        by_cases ht_4_5 : t <= (9:ℝ)
                        ·
                          exact box_4_5 x t hx1 hx2 ht (by linarith) (by linarith) (by linarith) (by linarith)
                        ·
                          by_cases ht_4_6 : t <= (13:ℝ)
                          ·
                            exact box_4_6 x t hx1 hx2 ht (by linarith) (by linarith) (by linarith) (by linarith)
                          ·
                            exact box_4_7 x t hx1 hx2 ht (by linarith) (by linarith) (by linarith) (by linarith)
            ·
              by_cases hx_5 : x <= (4:ℝ)
              ·
                by_cases ht_5_0 : t <= ((3:ℝ)/2)
                ·
                  exact box_5_0 x t hx1 hx2 ht (by linarith) (by linarith) (by linarith) (by linarith)
                ·
                  by_cases ht_5_1 : t <= (2:ℝ)
                  ·
                    exact box_5_1 x t hx1 hx2 ht (by linarith) (by linarith) (by linarith) (by linarith)
                  ·
                    by_cases ht_5_2 : t <= (3:ℝ)
                    ·
                      exact box_5_2 x t hx1 hx2 ht (by linarith) (by linarith) (by linarith) (by linarith)
                    ·
                      by_cases ht_5_3 : t <= (4:ℝ)
                      ·
                        exact box_5_3 x t hx1 hx2 ht (by linarith) (by linarith) (by linarith) (by linarith)
                      ·
                        by_cases ht_5_4 : t <= (6:ℝ)
                        ·
                          exact box_5_4 x t hx1 hx2 ht (by linarith) (by linarith) (by linarith) (by linarith)
                        ·
                          by_cases ht_5_5 : t <= (9:ℝ)
                          ·
                            exact box_5_5 x t hx1 hx2 ht (by linarith) (by linarith) (by linarith) (by linarith)
                          ·
                            by_cases ht_5_6 : t <= (13:ℝ)
                            ·
                              exact box_5_6 x t hx1 hx2 ht (by linarith) (by linarith) (by linarith) (by linarith)
                            ·
                              exact box_5_7 x t hx1 hx2 ht (by linarith) (by linarith) (by linarith) (by linarith)
              ·
                by_cases hx_6 : x <= (6:ℝ)
                ·
                  by_cases ht_6_0 : t <= ((3:ℝ)/2)
                  ·
                    exact box_6_0 x t hx1 hx2 ht (by linarith) (by linarith) (by linarith) (by linarith)
                  ·
                    by_cases ht_6_1 : t <= (2:ℝ)
                    ·
                      exact box_6_1 x t hx1 hx2 ht (by linarith) (by linarith) (by linarith) (by linarith)
                    ·
                      by_cases ht_6_2 : t <= (3:ℝ)
                      ·
                        exact box_6_2 x t hx1 hx2 ht (by linarith) (by linarith) (by linarith) (by linarith)
                      ·
                        by_cases ht_6_3 : t <= (4:ℝ)
                        ·
                          exact box_6_3 x t hx1 hx2 ht (by linarith) (by linarith) (by linarith) (by linarith)
                        ·
                          by_cases ht_6_4 : t <= (6:ℝ)
                          ·
                            exact box_6_4 x t hx1 hx2 ht (by linarith) (by linarith) (by linarith) (by linarith)
                          ·
                            by_cases ht_6_5 : t <= (9:ℝ)
                            ·
                              exact box_6_5 x t hx1 hx2 ht (by linarith) (by linarith) (by linarith) (by linarith)
                            ·
                              by_cases ht_6_6 : t <= (13:ℝ)
                              ·
                                exact box_6_6 x t hx1 hx2 ht (by linarith) (by linarith) (by linarith) (by linarith)
                              ·
                                exact box_6_7 x t hx1 hx2 ht (by linarith) (by linarith) (by linarith) (by linarith)
                ·
                  by_cases ht_7_0 : t <= ((3:ℝ)/2)
                  ·
                    exact box_7_0 x t hx1 hx2 ht (by linarith) (by linarith) (by linarith) (by linarith)
                  ·
                    by_cases ht_7_1 : t <= (2:ℝ)
                    ·
                      exact box_7_1 x t hx1 hx2 ht (by linarith) (by linarith) (by linarith) (by linarith)
                    ·
                      by_cases ht_7_2 : t <= (3:ℝ)
                      ·
                        exact box_7_2 x t hx1 hx2 ht (by linarith) (by linarith) (by linarith) (by linarith)
                      ·
                        by_cases ht_7_3 : t <= (4:ℝ)
                        ·
                          exact box_7_3 x t hx1 hx2 ht (by linarith) (by linarith) (by linarith) (by linarith)
                        ·
                          by_cases ht_7_4 : t <= (6:ℝ)
                          ·
                            exact box_7_4 x t hx1 hx2 ht (by linarith) (by linarith) (by linarith) (by linarith)
                          ·
                            by_cases ht_7_5 : t <= (9:ℝ)
                            ·
                              exact box_7_5 x t hx1 hx2 ht (by linarith) (by linarith) (by linarith) (by linarith)
                            ·
                              by_cases ht_7_6 : t <= (13:ℝ)
                              ·
                                exact box_7_6 x t hx1 hx2 ht (by linarith) (by linarith) (by linarith) (by linarith)
                              ·
                                exact box_7_7 x t hx1 hx2 ht (by linarith) (by linarith) (by linarith) (by linarith)
end Commons.Analysis.SpecialFunctions.Log