import Mathlib
import Submission.Work.MotC5N3.Work.KeyDefs
import Submission.Work.MotC5N3.Work.KeyTDefsA
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

theorem cj_0 {K : Type} [Field K] [CharP K 5] (a b g : K) : AsL0 a b g = AsZ0 a b g := by
  have h5 : (5 : K) = 0 := CharP.cast_eq_zero K 5
  have h : AsL0 a b g - AsZ0 a b g = 5 * T0 a b g := by
    simp only [AsL0, AsZ0, T0,
    AsCoef0,
    Work.MotV5.ASLocal.cshp27_0,
    AsCoef1,
    Work.MotV5.ASLocal.cshp20_0,
    AsCoef2,
    Work.MotV5.ASLocal.cshp22_0,
    AsCoef3,
    Work.MotV5.ASLocal.cshp24_0,
    AsCoef4,
    Work.MotV5.ASLocal.cshp15_0,
    AsCoef5,
    Work.MotV5.ASLocal.cshp12_0,
    AsCoef6,
    Work.MotV5.ASLocal.cshp13_0,
    AsCoef7,
    Work.MotV5.ASLocal.cshp17_0,
    AsCoef8,
    Work.MotV5.ASLocal.cshp7_0,
    AsCoef9,
    Work.MotV5.ASLocal.cshp3_0,
    AsCoef10,
    Work.MotV5.ASLocal.cshp5_0,
    AsCoef11,
    Work.MotV5.ASLocal.cshp0_0,
    AsCoef12,
    Work.MotV5.ASLocal.cshp2_0,
    AsCoef13,
    Work.MotV5.ASLocal.cshp9_0,
    AsCoef14,
    Work.MotV5.ASLocal.cshp11_0,
    Work.MotV5.ASLocal.asN0,
    Work.MotV5.ASLocal.asQ0,]
    refl_ring1
  rw [h5, zero_mul] at h
  exact sub_eq_zero.mp h

theorem cj_1 {K : Type} [Field K] [CharP K 5] (a b g : K) : AsL1 a b g = AsZ1 a b g := by
  have h5 : (5 : K) = 0 := CharP.cast_eq_zero K 5
  have h : AsL1 a b g - AsZ1 a b g = 5 * T1 a b g := by
    simp only [AsL1, AsZ1, T1,
    AsCoef0,
    Work.MotV5.ASLocal.cshp27_1,
    AsCoef1,
    Work.MotV5.ASLocal.cshp20_1,
    AsCoef2,
    Work.MotV5.ASLocal.cshp22_1,
    AsCoef3,
    Work.MotV5.ASLocal.cshp24_1,
    AsCoef4,
    Work.MotV5.ASLocal.cshp15_1,
    AsCoef5,
    Work.MotV5.ASLocal.cshp12_1,
    AsCoef6,
    Work.MotV5.ASLocal.cshp13_1,
    AsCoef7,
    Work.MotV5.ASLocal.cshp17_1,
    AsCoef8,
    Work.MotV5.ASLocal.cshp7_1,
    AsCoef9,
    Work.MotV5.ASLocal.cshp3_1,
    AsCoef10,
    Work.MotV5.ASLocal.cshp5_1,
    AsCoef11,
    Work.MotV5.ASLocal.cshp0_1,
    AsCoef12,
    Work.MotV5.ASLocal.cshp2_1,
    AsCoef13,
    Work.MotV5.ASLocal.cshp9_1,
    AsCoef14,
    Work.MotV5.ASLocal.cshp11_1,
    Work.MotV5.ASLocal.asN1,
    Work.MotV5.ASLocal.asQ0,
    Work.MotV5.ASLocal.asQ1,]
    refl_ring1
  rw [h5, zero_mul] at h
  exact sub_eq_zero.mp h

theorem cj_2 {K : Type} [Field K] [CharP K 5] (a b g : K) : AsL2 a b g = AsZ2 a b g := by
  have h5 : (5 : K) = 0 := CharP.cast_eq_zero K 5
  have h : AsL2 a b g - AsZ2 a b g = 5 * T2 a b g := by
    simp only [AsL2, AsZ2, T2,
    AsCoef0,
    Work.MotV5.ASLocal.cshp27_2,
    AsCoef1,
    Work.MotV5.ASLocal.cshp20_2,
    AsCoef2,
    Work.MotV5.ASLocal.cshp22_2,
    AsCoef3,
    Work.MotV5.ASLocal.cshp24_2,
    AsCoef4,
    Work.MotV5.ASLocal.cshp15_2,
    AsCoef5,
    Work.MotV5.ASLocal.cshp12_2,
    AsCoef6,
    Work.MotV5.ASLocal.cshp13_2,
    AsCoef7,
    Work.MotV5.ASLocal.cshp17_2,
    AsCoef8,
    Work.MotV5.ASLocal.cshp7_2,
    AsCoef9,
    Work.MotV5.ASLocal.cshp3_2,
    AsCoef10,
    Work.MotV5.ASLocal.cshp5_2,
    AsCoef11,
    Work.MotV5.ASLocal.cshp0_2,
    AsCoef12,
    Work.MotV5.ASLocal.cshp2_2,
    AsCoef13,
    Work.MotV5.ASLocal.cshp9_2,
    AsCoef14,
    Work.MotV5.ASLocal.cshp11_2,
    Work.MotV5.ASLocal.asN2,
    Work.MotV5.ASLocal.asQ1,
    Work.MotV5.ASLocal.asQ2,]
    refl_ring1
  rw [h5, zero_mul] at h
  exact sub_eq_zero.mp h

theorem cj_3 {K : Type} [Field K] [CharP K 5] (a b g : K) : AsL3 a b g = AsZ3 a b g := by
  have h5 : (5 : K) = 0 := CharP.cast_eq_zero K 5
  have h : AsL3 a b g - AsZ3 a b g = 5 * T3 a b g := by
    simp only [AsL3, AsZ3, T3,
    AsCoef0,
    Work.MotV5.ASLocal.cshp27_3,
    AsCoef1,
    Work.MotV5.ASLocal.cshp20_3,
    AsCoef2,
    Work.MotV5.ASLocal.cshp22_3,
    AsCoef3,
    Work.MotV5.ASLocal.cshp24_3,
    AsCoef4,
    Work.MotV5.ASLocal.cshp15_3,
    AsCoef5,
    Work.MotV5.ASLocal.cshp12_3,
    AsCoef6,
    Work.MotV5.ASLocal.cshp13_3,
    AsCoef7,
    Work.MotV5.ASLocal.cshp17_3,
    AsCoef8,
    Work.MotV5.ASLocal.cshp7_3,
    AsCoef9,
    Work.MotV5.ASLocal.cshp3_3,
    AsCoef10,
    Work.MotV5.ASLocal.cshp5_3,
    AsCoef11,
    Work.MotV5.ASLocal.cshp0_3,
    AsCoef12,
    Work.MotV5.ASLocal.cshp2_3,
    AsCoef13,
    Work.MotV5.ASLocal.cshp9_3,
    AsCoef14,
    Work.MotV5.ASLocal.cshp11_3,
    Work.MotV5.ASLocal.asN3,
    Work.MotV5.ASLocal.asQ2,
    Work.MotV5.ASLocal.asQ3,]
    refl_ring1
  rw [h5, zero_mul] at h
  exact sub_eq_zero.mp h

theorem cj_4 {K : Type} [Field K] [CharP K 5] (a b g : K) : AsL4 a b g = AsZ4 a b g := by
  have h5 : (5 : K) = 0 := CharP.cast_eq_zero K 5
  have h : AsL4 a b g - AsZ4 a b g = 5 * T4 a b g := by
    simp only [AsL4, AsZ4, T4,
    AsCoef0,
    Work.MotV5.ASLocal.cshp27_4,
    AsCoef1,
    Work.MotV5.ASLocal.cshp20_4,
    AsCoef2,
    Work.MotV5.ASLocal.cshp22_4,
    AsCoef3,
    Work.MotV5.ASLocal.cshp24_4,
    AsCoef4,
    Work.MotV5.ASLocal.cshp15_4,
    AsCoef5,
    Work.MotV5.ASLocal.cshp12_4,
    AsCoef6,
    Work.MotV5.ASLocal.cshp13_4,
    AsCoef7,
    Work.MotV5.ASLocal.cshp17_4,
    AsCoef8,
    Work.MotV5.ASLocal.cshp7_4,
    AsCoef9,
    Work.MotV5.ASLocal.cshp3_4,
    AsCoef10,
    Work.MotV5.ASLocal.cshp5_4,
    AsCoef11,
    Work.MotV5.ASLocal.cshp0_4,
    AsCoef12,
    Work.MotV5.ASLocal.cshp2_4,
    AsCoef13,
    Work.MotV5.ASLocal.cshp9_4,
    AsCoef14,
    Work.MotV5.ASLocal.cshp11_4,
    Work.MotV5.ASLocal.asN4,
    Work.MotV5.ASLocal.asQ3,
    Work.MotV5.ASLocal.asQ4,]
    refl_ring1
  rw [h5, zero_mul] at h
  exact sub_eq_zero.mp h

theorem cj_5 {K : Type} [Field K] [CharP K 5] (a b g : K) : AsL5 a b g = AsZ5 a b g := by
  have h5 : (5 : K) = 0 := CharP.cast_eq_zero K 5
  have h : AsL5 a b g - AsZ5 a b g = 5 * T5 a b g := by
    simp only [AsL5, AsZ5, T5,
    AsCoef0,
    Work.MotV5.ASLocal.cshp27_5,
    AsCoef1,
    Work.MotV5.ASLocal.cshp20_5,
    AsCoef2,
    Work.MotV5.ASLocal.cshp22_5,
    AsCoef3,
    Work.MotV5.ASLocal.cshp24_5,
    AsCoef4,
    Work.MotV5.ASLocal.cshp15_5,
    AsCoef5,
    Work.MotV5.ASLocal.cshp12_5,
    AsCoef6,
    Work.MotV5.ASLocal.cshp13_5,
    AsCoef7,
    Work.MotV5.ASLocal.cshp17_5,
    AsCoef8,
    Work.MotV5.ASLocal.cshp7_5,
    AsCoef9,
    Work.MotV5.ASLocal.cshp3_5,
    AsCoef10,
    Work.MotV5.ASLocal.cshp5_5,
    AsCoef11,
    Work.MotV5.ASLocal.cshp0_5,
    AsCoef12,
    Work.MotV5.ASLocal.cshp2_5,
    AsCoef13,
    Work.MotV5.ASLocal.cshp9_5,
    AsCoef14,
    Work.MotV5.ASLocal.cshp11_5,
    Work.MotV5.ASLocal.asQ0,
    Work.MotV5.ASLocal.asQ4,
    Work.MotV5.ASLocal.asQ5,]
    refl_ring1
  rw [h5, zero_mul] at h
  exact sub_eq_zero.mp h

theorem cj_6 {K : Type} [Field K] [CharP K 5] (a b g : K) : AsL6 a b g = AsZ6 a b g := by
  have h5 : (5 : K) = 0 := CharP.cast_eq_zero K 5
  have h : AsL6 a b g - AsZ6 a b g = 5 * T6 a b g := by
    simp only [AsL6, AsZ6, T6,
    AsCoef0,
    Work.MotV5.ASLocal.cshp27_6,
    AsCoef1,
    Work.MotV5.ASLocal.cshp20_6,
    AsCoef2,
    Work.MotV5.ASLocal.cshp22_6,
    AsCoef3,
    Work.MotV5.ASLocal.cshp24_6,
    AsCoef4,
    Work.MotV5.ASLocal.cshp15_6,
    AsCoef5,
    Work.MotV5.ASLocal.cshp12_6,
    AsCoef6,
    Work.MotV5.ASLocal.cshp13_6,
    AsCoef7,
    Work.MotV5.ASLocal.cshp17_6,
    AsCoef8,
    Work.MotV5.ASLocal.cshp7_6,
    AsCoef9,
    Work.MotV5.ASLocal.cshp3_6,
    AsCoef10,
    Work.MotV5.ASLocal.cshp5_6,
    AsCoef11,
    Work.MotV5.ASLocal.cshp0_6,
    AsCoef12,
    Work.MotV5.ASLocal.cshp2_6,
    AsCoef13,
    Work.MotV5.ASLocal.cshp9_6,
    AsCoef14,
    Work.MotV5.ASLocal.cshp11_6,
    Work.MotV5.ASLocal.asQ1,
    Work.MotV5.ASLocal.asQ5,
    Work.MotV5.ASLocal.asQ6,]
    refl_ring1
  rw [h5, zero_mul] at h
  exact sub_eq_zero.mp h

theorem cj_7 {K : Type} [Field K] [CharP K 5] (a b g : K) : AsL7 a b g = AsZ7 a b g := by
  have h5 : (5 : K) = 0 := CharP.cast_eq_zero K 5
  have h : AsL7 a b g - AsZ7 a b g = 5 * T7 a b g := by
    simp only [AsL7, AsZ7, T7,
    AsCoef0,
    Work.MotV5.ASLocal.cshp27_7,
    AsCoef1,
    Work.MotV5.ASLocal.cshp20_7,
    AsCoef2,
    Work.MotV5.ASLocal.cshp22_7,
    AsCoef3,
    Work.MotV5.ASLocal.cshp24_7,
    AsCoef4,
    Work.MotV5.ASLocal.cshp15_7,
    AsCoef5,
    Work.MotV5.ASLocal.cshp12_7,
    AsCoef6,
    Work.MotV5.ASLocal.cshp13_7,
    AsCoef7,
    Work.MotV5.ASLocal.cshp17_7,
    AsCoef8,
    Work.MotV5.ASLocal.cshp7_7,
    AsCoef9,
    Work.MotV5.ASLocal.cshp3_7,
    AsCoef10,
    Work.MotV5.ASLocal.cshp5_7,
    AsCoef11,
    Work.MotV5.ASLocal.cshp0_7,
    AsCoef12,
    Work.MotV5.ASLocal.cshp2_7,
    AsCoef13,
    Work.MotV5.ASLocal.cshp9_7,
    AsCoef14,
    Work.MotV5.ASLocal.cshp11_7,
    Work.MotV5.ASLocal.asQ2,
    Work.MotV5.ASLocal.asQ6,
    Work.MotV5.ASLocal.asQ7,]
    refl_ring1
  rw [h5, zero_mul] at h
  exact sub_eq_zero.mp h

theorem cj_8 {K : Type} [Field K] [CharP K 5] (a b g : K) : AsL8 a b g = AsZ8 a b g := by
  have h5 : (5 : K) = 0 := CharP.cast_eq_zero K 5
  have h : AsL8 a b g - AsZ8 a b g = 5 * T8 a b g := by
    simp only [AsL8, AsZ8, T8,
    AsCoef0,
    Work.MotV5.ASLocal.cshp27_8,
    AsCoef1,
    Work.MotV5.ASLocal.cshp20_8,
    AsCoef2,
    Work.MotV5.ASLocal.cshp22_8,
    AsCoef3,
    Work.MotV5.ASLocal.cshp24_8,
    AsCoef4,
    Work.MotV5.ASLocal.cshp15_8,
    AsCoef5,
    Work.MotV5.ASLocal.cshp12_8,
    AsCoef6,
    Work.MotV5.ASLocal.cshp13_8,
    AsCoef7,
    Work.MotV5.ASLocal.cshp17_8,
    AsCoef8,
    Work.MotV5.ASLocal.cshp7_8,
    AsCoef9,
    Work.MotV5.ASLocal.cshp3_8,
    AsCoef10,
    Work.MotV5.ASLocal.cshp5_8,
    AsCoef11,
    Work.MotV5.ASLocal.cshp0_8,
    AsCoef12,
    Work.MotV5.ASLocal.cshp2_8,
    AsCoef13,
    Work.MotV5.ASLocal.cshp9_8,
    AsCoef14,
    Work.MotV5.ASLocal.cshp11_8,
    Work.MotV5.ASLocal.asQ3,
    Work.MotV5.ASLocal.asQ7,
    Work.MotV5.ASLocal.asQ8,]
    refl_ring1
  rw [h5, zero_mul] at h
  exact sub_eq_zero.mp h

theorem cj_9 {K : Type} [Field K] [CharP K 5] (a b g : K) : AsL9 a b g = AsZ9 a b g := by
  have h5 : (5 : K) = 0 := CharP.cast_eq_zero K 5
  have h : AsL9 a b g - AsZ9 a b g = 5 * T9 a b g := by
    simp only [AsL9, AsZ9, T9,
    AsCoef0,
    Work.MotV5.ASLocal.cshp27_9,
    AsCoef1,
    Work.MotV5.ASLocal.cshp20_9,
    AsCoef2,
    Work.MotV5.ASLocal.cshp22_9,
    AsCoef3,
    Work.MotV5.ASLocal.cshp24_9,
    AsCoef4,
    Work.MotV5.ASLocal.cshp15_9,
    AsCoef5,
    Work.MotV5.ASLocal.cshp12_9,
    AsCoef6,
    Work.MotV5.ASLocal.cshp13_9,
    AsCoef7,
    Work.MotV5.ASLocal.cshp17_9,
    AsCoef8,
    Work.MotV5.ASLocal.cshp7_9,
    AsCoef9,
    Work.MotV5.ASLocal.cshp3_9,
    AsCoef10,
    Work.MotV5.ASLocal.cshp5_9,
    AsCoef11,
    Work.MotV5.ASLocal.cshp0_9,
    AsCoef12,
    Work.MotV5.ASLocal.cshp2_9,
    AsCoef13,
    Work.MotV5.ASLocal.cshp9_9,
    AsCoef14,
    Work.MotV5.ASLocal.cshp11_9,
    Work.MotV5.ASLocal.asQ4,
    Work.MotV5.ASLocal.asQ8,
    Work.MotV5.ASLocal.asQ9,]
    refl_ring1
  rw [h5, zero_mul] at h
  exact sub_eq_zero.mp h

end Work.MotC5N3.Work
