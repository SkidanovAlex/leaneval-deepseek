import Submission.Work.MotC5N3.SatCert2.hB1hB3_c3_b
import Submission.Work.Reflect.PolyId

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.unusedVariables false

namespace Work.MotC5N3.CertDemo

open MvPolynomial Work.MotC5N3

variable {K : Type} [Field K] [CharP K 5]

lemma e3_11 (a b g : K) : E3_11 a b g = 0 := by
  simp only [E3_11, cd3_0_11, fd30_1, fd31_0, fd32_0, fd33_0, kD3_0, kD3_1, kD3_2, kP3_2, kP3_5, kR3_0, kR3_1, kR3_3, kR3_4, sd3_0, sd3_1]
  refl_ring1

lemma e3_12 (a b g : K) : E3_12 a b g = 0 := by
  simp only [E3_12, cd3_0_12, fd31_0, fd32_0, fd33_0, kD3_0, kD3_1, kD3_2, kP3_6, kR3_0, kR3_1, kR3_2, kR3_3, kR3_4, sd3_0]
  refl_ring1

lemma e3_13 (a b g : K) : E3_13 a b g = 0 := by
  simp only [E3_13, cd3_0_13, fd31_0, fd32_0, fd33_0, kD3_0, kD3_1, kD3_2, kP3_3, kR3_0, kR3_1, kR3_2, kR3_3, kR3_4, sd3_1]
  refl_ring1

lemma e3_14 (a b g : K) : E3_14 a b g = 0 := by
  simp only [E3_14, cd3_1_0, fd32_0, fd33_0, kD3_1, kD3_2, kR3_1, kR3_2, kR3_3, kR3_4]
  refl_ring1

lemma e3_15 (a b g : K) : E3_15 a b g = 0 := by
  simp only [E3_15, cd3_1_1, fd32_0, fd33_0, kD3_2, kR3_2, kR3_4]
  refl_ring1

lemma e3_16 (a b g : K) : E3_16 a b g = 0 := by
  simp only [E3_16, cd3_1_2, fd30_0, fd30_2, fd30_4, fd31_1, fd31_2, kD3_0, kD3_1, kD3_3, kP3_0, kP3_7, kR3_0, kR3_3, sd3_0, sd3_2]
  refl_ring1

lemma e3_17 (a b g : K) : E3_17 a b g = 0 := by
  simp only [E3_17, cd3_1_3, fd30_0, fd30_2, fd30_3, fd31_1, fd31_2, kD3_0, kD3_1, kD3_2, kR3_0, kR3_1, kR3_4]
  refl_ring1

lemma e3_18 (a b g : K) : E3_18 a b g = 0 := by
  simp only [E3_18, cd3_1_4, fd30_0, fd30_1, fd30_3, fd31_0, fd31_1, fd31_2, fd32_0, fd33_0, kD3_0, kD3_1, kD3_2, kD3_3, kP3_1, kP3_4, kP3_8, kR3_0, kR3_1, kR3_2, kR3_3, kR3_5, sd3_0, sd3_1, sd3_2]
  refl_ring1

lemma e3_19 (a b g : K) : E3_19 a b g = 0 := by
  simp only [E3_19, cd3_1_5, fd30_1, fd31_0, fd31_1, fd32_0, fd33_0, kD3_0, kD3_1, kD3_2, kD3_3, kP3_2, kP3_5, kP3_9, kR3_0, kR3_1, kR3_2, kR3_3, kR3_4, kR3_5, sd3_0, sd3_1, sd3_2]
  refl_ring1

lemma e3_20 (a b g : K) : E3_20 a b g = 0 := by
  simp only [E3_20, cd3_1_6, fd30_1, fd31_0, fd32_0, fd33_0, kD3_0, kD3_1, kD3_2, kD3_3, kP3_6, kR3_0, kR3_1, kR3_2, kR3_3, kR3_4, kR3_5, sd3_1]
  refl_ring1

lemma e3_21 (a b g : K) : E3_21 a b g = 0 := by
  simp only [E3_21, cd3_1_7, fd31_0, fd32_0, fd33_0, kD3_1, kD3_2, kD3_3, kP3_3, kR3_1, kR3_2, kR3_3, kR3_4, kR3_5, sd3_2]
  refl_ring1

lemma e3_22 (a b g : K) : E3_22 a b g = 0 := by
  simp only [E3_22, cd3_1_8, fd31_0, fd32_0, fd33_0, kD3_2, kD3_3, kR3_2, kR3_4, kR3_5]
  refl_ring1

lemma e3_23 (a b g : K) : E3_23 a b g = 0 := by
  simp only [E3_23, cd3_1_9, fd30_0, fd30_2, fd30_4, fd31_1, fd31_2, kD3_0, kD3_1, kD3_3, kP3_0, kP3_10, kP3_7, kR3_0, kR3_3, kR3_5, sd3_0, sd3_1, sd3_3]
  refl_ring1

lemma e3_24 (a b g : K) : E3_24 a b g = 0 := by
  simp only [E3_24, cd3_1_10, fd30_0, fd30_2, fd30_3, fd30_4, fd31_0, fd31_1, fd31_2, fd32_0, fd33_0, kD3_0, kD3_1, kD3_2, kD3_3, kP3_11, kR3_0, kR3_1, kR3_3, kR3_4, kR3_6, sd3_0]
  refl_ring1

lemma e3_25 (a b g : K) : E3_25 a b g = 0 := by
  simp only [E3_25, cd3_1_11, fd30_0, fd30_1, fd30_2, fd30_3, fd31_0, fd31_1, fd31_2, fd32_0, fd33_0, kD3_0, kD3_1, kD3_2, kD3_3, kP3_1, kP3_12, kP3_4, kP3_8, kR3_0, kR3_1, kR3_2, kR3_3, kR3_4, kR3_5, kR3_6, sd3_0, sd3_1, sd3_2, sd3_3]
  refl_ring1

lemma e3_26 (a b g : K) : E3_26 a b g = 0 := by
  simp only [E3_26, cd3_1_12, fd30_0, fd30_1, fd30_3, fd31_0, fd31_1, fd31_2, fd32_0, fd33_0, kD3_0, kD3_1, kD3_2, kD3_3, kP3_2, kP3_5, kP3_9, kR3_0, kR3_1, kR3_2, kR3_3, kR3_4, kR3_5, kR3_6, sd3_1, sd3_2, sd3_3]
  refl_ring1

lemma e3_27 (a b g : K) : E3_27 a b g = 0 := by
  simp only [E3_27, cd3_1_13, fd30_1, fd31_0, fd31_1, fd32_0, fd33_0, kD3_1, kD3_2, kD3_3, kP3_6, kR3_1, kR3_2, kR3_3, kR3_4, kR3_5, kR3_6, sd3_2]
  refl_ring1

lemma e3_28 (a b g : K) : E3_28 a b g = 0 := by
  simp only [E3_28, cd3_2_0, fd30_1, fd31_0, fd32_0, fd33_0, kD3_2, kD3_3, kP3_3, kR3_2, kR3_4, kR3_5, kR3_6, sd3_3]
  refl_ring1

lemma e3_29 (a b g : K) : E3_29 a b g = 0 := by
  simp only [E3_29, cd3_2_1, fd31_1, kD3_0, kP3_0, kR3_6, sd3_4]
  refl_ring1

lemma e3_30 (a b g : K) : E3_30 a b g = 0 := by
  simp only [E3_30, cd3_2_2, fd30_0, fd30_2, fd30_4, fd31_1, fd31_2, kD3_0, kD3_1, kD3_3, kP3_10, kP3_13, kP3_7, kR3_0, kR3_3, kR3_5, sd3_0, sd3_1, sd3_2]
  refl_ring1

lemma e3_31 (a b g : K) : E3_31 a b g = 0 := by
  simp only [E3_31, cd3_2_3, fd30_0, fd30_2, fd30_3, fd30_4, fd31_0, fd31_1, fd31_2, fd32_0, fd33_0, kD3_0, kD3_1, kD3_2, kD3_3, kP3_1, kP3_11, kR3_0, kR3_1, kR3_3, kR3_4, kR3_5, kR3_6, sd3_1, sd3_4]
  refl_ring1

lemma e3_32 (a b g : K) : E3_32 a b g = 0 := by
  simp only [E3_32, cd3_2_4, fd30_0, fd30_1, fd30_2, fd30_3, fd30_4, fd31_0, fd31_1, fd31_2, fd32_0, fd33_0, kD3_0, kD3_1, kD3_2, kD3_3, kP3_12, kP3_2, kP3_4, kP3_8, kR3_0, kR3_1, kR3_2, kR3_3, kR3_4, kR3_5, kR3_6, sd3_1, sd3_2, sd3_3, sd3_4]
  refl_ring1

lemma e3_33 (a b g : K) : E3_33 a b g = 0 := by
  simp only [E3_33, cd3_2_5, fd30_1, fd30_2, fd30_3, fd31_0, fd31_1, fd31_2, fd32_0, fd33_0, kD3_1, kD3_2, kD3_3, kP3_5, kP3_9, kR3_1, kR3_2, kR3_3, kR3_4, kR3_5, kR3_6, sd3_2, sd3_3]
  refl_ring1

lemma e3_34 (a b g : K) : E3_34 a b g = 0 := by
  simp only [E3_34, cd3_2_6, fd30_1, fd30_3, fd31_0, fd31_2, fd32_0, fd33_0, kD3_2, kD3_3, kP3_3, kP3_6, kR3_2, kR3_4, kR3_5, kR3_6, sd3_3, sd3_4]
  refl_ring1

lemma e3_35 (a b g : K) : E3_35 a b g = 0 := by
  simp only [E3_35, cd3_2_7, fd31_1, fd31_2, kD3_0, kD3_1, kR3_6]
  refl_ring1

lemma e3_36 (a b g : K) : E3_36 a b g = 0 := by
  simp only [E3_36, cd3_2_8, fd30_0, fd30_2, fd30_4, fd31_1, fd31_2, kD3_0, kD3_1, kD3_2, kD3_3, kP3_10, kP3_13, kP3_14, kP3_7, kR3_0, kR3_3, kR3_5, kR3_6, sd3_0, sd3_1, sd3_2, sd3_3]
  refl_ring1

lemma e3_37 (a b g : K) : E3_37 a b g = 0 := by
  simp only [E3_37, cd3_2_9, fd30_0, fd30_2, fd30_3, fd30_4, fd31_0, fd31_1, fd31_2, fd32_0, fd33_0, kD3_0, kD3_1, kD3_2, kD3_3, kP3_11, kP3_4, kR3_0, kR3_1, kR3_3, kR3_4, kR3_5, kR3_6, sd3_2, sd3_4]
  refl_ring1

lemma e3_38 (a b g : K) : E3_38 a b g = 0 := by
  simp only [E3_38, cd3_2_10, fd30_1, fd30_2, fd30_3, fd30_4, fd31_0, fd31_1, fd31_2, fd32_0, fd33_0, kD3_1, kD3_2, kD3_3, kP3_12, kP3_5, kP3_8, kR3_1, kR3_2, kR3_3, kR3_4, kR3_5, kR3_6, sd3_2, sd3_3, sd3_4]
  refl_ring1

lemma e3_39 (a b g : K) : E3_39 a b g = 0 := by
  simp only [E3_39, cd3_2_11, fd30_1, fd30_3, fd30_4, fd31_0, fd31_2, fd32_0, fd33_0, kD3_2, kD3_3, kP3_6, kP3_9, kR3_2, kR3_4, kR3_5, kR3_6, sd3_3, sd3_4]
  refl_ring1

lemma e3_40 (a b g : K) : E3_40 a b g = 0 := by
  simp only [E3_40, cd3_2_12, fd31_1, fd31_2, kD3_0, kD3_1, kD3_3, kP3_7, kR3_6, sd3_4]
  refl_ring1

lemma e3_41 (a b g : K) : E3_41 a b g = 0 := by
  simp only [E3_41, cd3_2_13, fd30_0, fd30_2, fd30_4, fd31_1, fd31_2, fd32_0, fd33_0, kD3_0, kD3_1, kD3_2, kD3_3, kP3_10, kP3_13, kP3_14, kR3_0, kR3_3, kR3_5, kR3_6, sd3_1, sd3_2, sd3_3]
  refl_ring1

lemma e3_42 (a b g : K) : E3_42 a b g = 0 := by
  simp only [E3_42, cd3_3_0, fd30_2, fd30_3, fd30_4, fd31_0, fd31_1, fd31_2, fd32_0, fd33_0, kD3_1, kD3_2, kD3_3, kP3_11, kP3_8, kR3_1, kR3_3, kR3_4, kR3_5, kR3_6, sd3_3, sd3_4]
  refl_ring1

lemma e3_43 (a b g : K) : E3_43 a b g = 0 := by
  simp only [E3_43, cd3_3_1, fd30_1, fd30_3, fd30_4, fd31_0, fd31_2, fd32_0, fd33_0, kD3_2, kD3_3, kP3_12, kP3_9, kR3_2, kR3_4, kR3_5, kR3_6, sd3_3, sd3_4]
  refl_ring1

lemma e3_44 (a b g : K) : E3_44 a b g = 0 := by
  simp only [E3_44, cd3_3_2, fd31_1, fd31_2, kD3_0, kD3_1, kD3_3, kP3_10, kR3_6, sd3_4]
  refl_ring1

lemma e3_45 (a b g : K) : E3_45 a b g = 0 := by
  simp only [E3_45, cd3_3_3, fd30_2, fd30_4, fd31_1, fd31_2, fd32_0, fd33_0, kD3_1, kD3_2, kD3_3, kP3_11, kP3_13, kP3_14, kR3_3, kR3_5, kR3_6, sd3_2, sd3_3, sd3_4]
  refl_ring1

lemma e3_46 (a b g : K) : E3_46 a b g = 0 := by
  simp only [E3_46, cd3_3_4, fd30_3, fd30_4, fd31_0, fd31_2, fd32_0, fd33_0, kD3_2, kD3_3, kP3_12, kR3_4, kR3_5, kR3_6, sd3_4]
  refl_ring1

lemma e3_47 (a b g : K) : E3_47 a b g = 0 := by
  simp only [E3_47, cd3_3_5, fd31_1, fd31_2, kD3_1, kD3_3, kP3_13, kR3_6, sd3_4]
  refl_ring1

lemma e3_48 (a b g : K) : E3_48 a b g = 0 := by
  simp only [E3_48, cd3_3_6, fd30_4, fd31_2, fd32_0, fd33_0, kD3_2, kD3_3, kP3_14, kR3_5, kR3_6, sd3_3]
  refl_ring1

lemma e3_49 (a b g : K) : E3_49 a b g = 0 := by
  simp only [E3_49, cd3_3_7, fd31_2, fd33_0, kD3_3, kP3_14, kR3_6, sd3_4]
  refl_ring1

theorem hB3 (a b g : K) :
    N3 a b g - X2AuxInputs.Pemb a b g * S3 a b g = (5 : MvPolynomial (Fin 3) K) * C3 a b g := by
  rw [← sub_eq_zero, struct3]
  simp only [e3_0, e3_1, e3_2, e3_3, e3_4, e3_5, e3_6, e3_7, e3_8, e3_9, e3_10, e3_11, e3_12, e3_13, e3_14, e3_15, e3_16, e3_17, e3_18, e3_19, e3_20, e3_21, e3_22, e3_23, e3_24, e3_25, e3_26, e3_27, e3_28, e3_29, e3_30, e3_31, e3_32, e3_33, e3_34, e3_35, e3_36, e3_37, e3_38, e3_39, e3_40, e3_41, e3_42, e3_43, e3_44, e3_45, e3_46, e3_47, e3_48, e3_49, map_zero, zero_mul, add_zero]

#print axioms Work.MotC5N3.CertDemo.hB3

end Work.MotC5N3.CertDemo
