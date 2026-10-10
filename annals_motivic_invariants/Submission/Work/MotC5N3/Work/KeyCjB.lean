import Mathlib
import Submission.Work.MotC5N3.Work.KeyDefs
import Submission.Work.MotC5N3.Work.KeyTDefsB
import Submission.Work.Reflect.PolyId

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 1000000

namespace Work.MotC5N3.Work

open Polynomial

theorem cj_10 {K : Type} [Field K] [CharP K 5] (a b g : K) : AsL10 a b g = AsZ10 a b g := by
  have h5 : (5 : K) = 0 := CharP.cast_eq_zero K 5
  have h : AsL10 a b g - AsZ10 a b g = 5 * T10 a b g := by
    simp only [AsL10, AsZ10, T10,
    AsCoef0,
    Work.MotV5.ASLocal.cshp27_10,
    AsCoef1,
    Work.MotV5.ASLocal.cshp20_10,
    AsCoef2,
    Work.MotV5.ASLocal.cshp22_10,
    AsCoef3,
    Work.MotV5.ASLocal.cshp24_10,
    AsCoef4,
    Work.MotV5.ASLocal.cshp15_10,
    AsCoef5,
    Work.MotV5.ASLocal.cshp12_10,
    AsCoef6,
    Work.MotV5.ASLocal.cshp13_10,
    AsCoef7,
    Work.MotV5.ASLocal.cshp17_10,
    AsCoef8,
    Work.MotV5.ASLocal.cshp7_10,
    AsCoef9,
    Work.MotV5.ASLocal.cshp3_10,
    AsCoef10,
    Work.MotV5.ASLocal.cshp5_10,
    AsCoef11,
    Work.MotV5.ASLocal.cshp0_10,
    AsCoef12,
    Work.MotV5.ASLocal.cshp2_10,
    AsCoef13,
    Work.MotV5.ASLocal.cshp9_10,
    AsCoef14,
    Work.MotV5.ASLocal.cshp11_10,
    Work.MotV5.ASLocal.asQ5,
    Work.MotV5.ASLocal.asQ9,
    Work.MotV5.ASLocal.asQ10,]
    refl_ring1
  rw [h5, zero_mul] at h
  exact sub_eq_zero.mp h

theorem cj_11 {K : Type} [Field K] [CharP K 5] (a b g : K) : AsL11 a b g = AsZ11 a b g := by
  have h5 : (5 : K) = 0 := CharP.cast_eq_zero K 5
  have h : AsL11 a b g - AsZ11 a b g = 5 * T11 a b g := by
    simp only [AsL11, AsZ11, T11,
    AsCoef0,
    Work.MotV5.ASLocal.cshp27_11,
    AsCoef1,
    Work.MotV5.ASLocal.cshp20_11,
    AsCoef2,
    Work.MotV5.ASLocal.cshp22_11,
    AsCoef3,
    Work.MotV5.ASLocal.cshp24_11,
    AsCoef4,
    Work.MotV5.ASLocal.cshp15_11,
    AsCoef5,
    Work.MotV5.ASLocal.cshp12_11,
    AsCoef6,
    Work.MotV5.ASLocal.cshp13_11,
    AsCoef7,
    Work.MotV5.ASLocal.cshp17_11,
    AsCoef8,
    Work.MotV5.ASLocal.cshp7_11,
    AsCoef9,
    Work.MotV5.ASLocal.cshp3_11,
    AsCoef10,
    Work.MotV5.ASLocal.cshp5_11,
    AsCoef11,
    Work.MotV5.ASLocal.cshp0_11,
    AsCoef12,
    Work.MotV5.ASLocal.cshp2_11,
    AsCoef13,
    Work.MotV5.ASLocal.cshp9_11,
    AsCoef14,
    Work.MotV5.ASLocal.cshp11_11,
    Work.MotV5.ASLocal.asQ6,
    Work.MotV5.ASLocal.asQ10,
    Work.MotV5.ASLocal.asQ11,]
    refl_ring1
  rw [h5, zero_mul] at h
  exact sub_eq_zero.mp h

theorem cj_12 {K : Type} [Field K] [CharP K 5] (a b g : K) : AsL12 a b g = AsZ12 a b g := by
  have h5 : (5 : K) = 0 := CharP.cast_eq_zero K 5
  have h : AsL12 a b g - AsZ12 a b g = 5 * T12 a b g := by
    simp only [AsL12, AsZ12, T12,
    AsCoef0,
    Work.MotV5.ASLocal.cshp27_12,
    AsCoef1,
    Work.MotV5.ASLocal.cshp20_12,
    AsCoef2,
    Work.MotV5.ASLocal.cshp22_12,
    AsCoef3,
    Work.MotV5.ASLocal.cshp24_12,
    AsCoef4,
    Work.MotV5.ASLocal.cshp15_12,
    AsCoef5,
    Work.MotV5.ASLocal.cshp12_12,
    AsCoef6,
    Work.MotV5.ASLocal.cshp13_12,
    AsCoef7,
    Work.MotV5.ASLocal.cshp17_12,
    AsCoef8,
    Work.MotV5.ASLocal.cshp7_12,
    AsCoef9,
    Work.MotV5.ASLocal.cshp3_12,
    AsCoef10,
    Work.MotV5.ASLocal.cshp5_12,
    AsCoef11,
    Work.MotV5.ASLocal.cshp0_12,
    AsCoef12,
    Work.MotV5.ASLocal.cshp2_12,
    AsCoef13,
    Work.MotV5.ASLocal.cshp9_12,
    AsCoef14,
    Work.MotV5.ASLocal.cshp11_12,
    Work.MotV5.ASLocal.asQ7,
    Work.MotV5.ASLocal.asQ11,
    Work.MotV5.ASLocal.asQ12,]
    refl_ring1
  rw [h5, zero_mul] at h
  exact sub_eq_zero.mp h

theorem cj_13 {K : Type} [Field K] [CharP K 5] (a b g : K) : AsL13 a b g = AsZ13 a b g := by
  have h5 : (5 : K) = 0 := CharP.cast_eq_zero K 5
  have h : AsL13 a b g - AsZ13 a b g = 5 * T13 a b g := by
    simp only [AsL13, AsZ13, T13,
    AsCoef0,
    Work.MotV5.ASLocal.cshp27_13,
    AsCoef1,
    Work.MotV5.ASLocal.cshp20_13,
    AsCoef2,
    Work.MotV5.ASLocal.cshp22_13,
    AsCoef3,
    Work.MotV5.ASLocal.cshp24_13,
    AsCoef4,
    Work.MotV5.ASLocal.cshp15_13,
    AsCoef5,
    Work.MotV5.ASLocal.cshp12_13,
    AsCoef6,
    Work.MotV5.ASLocal.cshp13_13,
    AsCoef7,
    Work.MotV5.ASLocal.cshp17_13,
    AsCoef8,
    Work.MotV5.ASLocal.cshp7_13,
    AsCoef9,
    Work.MotV5.ASLocal.cshp3_13,
    AsCoef10,
    Work.MotV5.ASLocal.cshp5_13,
    AsCoef11,
    Work.MotV5.ASLocal.cshp0_13,
    AsCoef12,
    Work.MotV5.ASLocal.cshp2_13,
    AsCoef13,
    Work.MotV5.ASLocal.cshp9_13,
    AsCoef14,
    Work.MotV5.ASLocal.cshp11_13,
    Work.MotV5.ASLocal.asQ8,
    Work.MotV5.ASLocal.asQ12,
    Work.MotV5.ASLocal.asQ13,]
    refl_ring1
  rw [h5, zero_mul] at h
  exact sub_eq_zero.mp h

theorem cj_14 {K : Type} [Field K] [CharP K 5] (a b g : K) : AsL14 a b g = AsZ14 a b g := by
  have h5 : (5 : K) = 0 := CharP.cast_eq_zero K 5
  have h : AsL14 a b g - AsZ14 a b g = 5 * T14 a b g := by
    simp only [AsL14, AsZ14, T14,
    AsCoef0,
    Work.MotV5.ASLocal.cshp27_14,
    AsCoef1,
    Work.MotV5.ASLocal.cshp20_14,
    AsCoef2,
    Work.MotV5.ASLocal.cshp22_14,
    AsCoef3,
    Work.MotV5.ASLocal.cshp24_14,
    AsCoef4,
    Work.MotV5.ASLocal.cshp15_14,
    AsCoef5,
    Work.MotV5.ASLocal.cshp12_14,
    AsCoef6,
    Work.MotV5.ASLocal.cshp13_14,
    AsCoef7,
    Work.MotV5.ASLocal.cshp17_14,
    AsCoef8,
    Work.MotV5.ASLocal.cshp7_14,
    AsCoef9,
    Work.MotV5.ASLocal.cshp3_14,
    AsCoef10,
    Work.MotV5.ASLocal.cshp5_14,
    AsCoef11,
    Work.MotV5.ASLocal.cshp0_14,
    AsCoef12,
    Work.MotV5.ASLocal.cshp2_14,
    AsCoef13,
    Work.MotV5.ASLocal.cshp9_14,
    AsCoef14,
    Work.MotV5.ASLocal.cshp11_14,
    Work.MotV5.ASLocal.asQ9,
    Work.MotV5.ASLocal.asQ13,]
    refl_ring1
  rw [h5, zero_mul] at h
  exact sub_eq_zero.mp h

theorem cj_15 {K : Type} [Field K] [CharP K 5] (a b g : K) : AsL15 a b g = AsZ15 a b g := by
  have h5 : (5 : K) = 0 := CharP.cast_eq_zero K 5
  have h : AsL15 a b g - AsZ15 a b g = 5 * T15 a b g := by
    simp only [AsL15, AsZ15, T15,
    AsCoef0,
    Work.MotV5.ASLocal.cshp27_15,
    AsCoef1,
    Work.MotV5.ASLocal.cshp20_15,
    AsCoef2,
    Work.MotV5.ASLocal.cshp22_15,
    AsCoef3,
    Work.MotV5.ASLocal.cshp24_15,
    AsCoef4,
    Work.MotV5.ASLocal.cshp15_15,
    AsCoef5,
    Work.MotV5.ASLocal.cshp12_15,
    AsCoef6,
    Work.MotV5.ASLocal.cshp13_15,
    AsCoef7,
    Work.MotV5.ASLocal.cshp17_15,
    AsCoef8,
    Work.MotV5.ASLocal.cshp7_15,
    AsCoef9,
    Work.MotV5.ASLocal.cshp3_15,
    AsCoef10,
    Work.MotV5.ASLocal.cshp5_15,
    AsCoef11,
    Work.MotV5.ASLocal.cshp0_15,
    AsCoef12,
    Work.MotV5.ASLocal.cshp2_15,
    AsCoef13,
    Work.MotV5.ASLocal.cshp9_15,
    AsCoef14,
    Work.MotV5.ASLocal.cshp11_15,
    Work.MotV5.ASLocal.asQ10,]
    refl_ring1
  rw [h5, zero_mul] at h
  exact sub_eq_zero.mp h

theorem cj_16 {K : Type} [Field K] [CharP K 5] (a b g : K) : AsL16 a b g = AsZ16 a b g := by
  have h5 : (5 : K) = 0 := CharP.cast_eq_zero K 5
  have h : AsL16 a b g - AsZ16 a b g = 5 * T16 a b g := by
    simp only [AsL16, AsZ16, T16,
    AsCoef1,
    Work.MotV5.ASLocal.cshp20_16,
    AsCoef2,
    Work.MotV5.ASLocal.cshp22_16,
    AsCoef3,
    Work.MotV5.ASLocal.cshp24_16,
    AsCoef4,
    Work.MotV5.ASLocal.cshp15_16,
    AsCoef5,
    Work.MotV5.ASLocal.cshp12_16,
    AsCoef6,
    Work.MotV5.ASLocal.cshp13_16,
    AsCoef7,
    Work.MotV5.ASLocal.cshp17_16,
    AsCoef8,
    Work.MotV5.ASLocal.cshp7_16,
    AsCoef9,
    Work.MotV5.ASLocal.cshp3_16,
    AsCoef10,
    Work.MotV5.ASLocal.cshp5_16,
    AsCoef11,
    Work.MotV5.ASLocal.cshp0_16,
    AsCoef12,
    Work.MotV5.ASLocal.cshp2_16,
    AsCoef13,
    Work.MotV5.ASLocal.cshp9_16,
    AsCoef14,
    Work.MotV5.ASLocal.cshp11_16,
    Work.MotV5.ASLocal.asQ11,]
    refl_ring1
  rw [h5, zero_mul] at h
  exact sub_eq_zero.mp h

theorem cj_17 {K : Type} [Field K] [CharP K 5] (a b g : K) : AsL17 a b g = AsZ17 a b g := by
  have h5 : (5 : K) = 0 := CharP.cast_eq_zero K 5
  have h : AsL17 a b g - AsZ17 a b g = 5 * T17 a b g := by
    simp only [AsL17, AsZ17, T17,
    AsCoef2,
    Work.MotV5.ASLocal.cshp22_17,
    AsCoef3,
    Work.MotV5.ASLocal.cshp24_17,
    AsCoef5,
    Work.MotV5.ASLocal.cshp12_17,
    AsCoef6,
    Work.MotV5.ASLocal.cshp13_17,
    AsCoef7,
    Work.MotV5.ASLocal.cshp17_17,
    AsCoef9,
    Work.MotV5.ASLocal.cshp3_17,
    AsCoef10,
    Work.MotV5.ASLocal.cshp5_17,
    AsCoef11,
    Work.MotV5.ASLocal.cshp0_17,
    AsCoef12,
    Work.MotV5.ASLocal.cshp2_17,
    AsCoef13,
    Work.MotV5.ASLocal.cshp9_17,
    AsCoef14,
    Work.MotV5.ASLocal.cshp11_17,
    Work.MotV5.ASLocal.asQ12,]
    refl_ring1
  rw [h5, zero_mul] at h
  exact sub_eq_zero.mp h

theorem cj_18 {K : Type} [Field K] [CharP K 5] (a b g : K) : AsL18 a b g = AsZ18 a b g := by
  have h5 : (5 : K) = 0 := CharP.cast_eq_zero K 5
  have h : AsL18 a b g - AsZ18 a b g = 5 * T18 a b g := by
    simp only [AsL18, AsZ18, T18,
    AsCoef3,
    Work.MotV5.ASLocal.cshp24_18,
    AsCoef6,
    Work.MotV5.ASLocal.cshp13_18,
    AsCoef10,
    Work.MotV5.ASLocal.cshp5_18,
    AsCoef12,
    Work.MotV5.ASLocal.cshp2_18,
    AsCoef13,
    Work.MotV5.ASLocal.cshp9_18,
    AsCoef14,
    Work.MotV5.ASLocal.cshp11_18,
    Work.MotV5.ASLocal.asQ13,]
    refl_ring1
  rw [h5, zero_mul] at h
  exact sub_eq_zero.mp h

end Work.MotC5N3.Work
