import Submission.Work.MotC5N3.SatCert2.hB1hB3_c1_b
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

noncomputable def E1_50 (a b g : K) : K :=
  (-5) * cd1_3_6 a b g + (1) * fd10_5 a b g * kD1_3 a b g ^(3:ℕ) + (-1) * kP1_14 a b g * sd1_3 a b g + (1) * fd12_0 a b g * kD1_3 a b g * kR1_6 a b g ^(2:ℕ) + (-1) * fd11_2 a b g * kR1_6 a b g * kD1_3 a b g ^(2:ℕ) + (-1) * fd11_3 a b g * kR1_5 a b g * kD1_3 a b g ^(2:ℕ) + (-3) * fd13_0 a b g * kR1_5 a b g * kR1_6 a b g ^(2:ℕ) + (3) * fd10_6 a b g * kD1_2 a b g * kD1_3 a b g ^(2:ℕ) + (-2) * fd11_3 a b g * kD1_2 a b g * kD1_3 a b g * kR1_6 a b g

noncomputable def E1_51 (a b g : K) : K :=
  (-5) * cd1_3_7 a b g + (1) * fd10_6 a b g * kD1_3 a b g ^(3:ℕ) + (-1) * fd13_0 a b g * kR1_6 a b g ^(3:ℕ) + (-1) * kP1_14 a b g * sd1_4 a b g + (-1) * fd11_3 a b g * kR1_6 a b g * kD1_3 a b g ^(2:ℕ)

lemma hD1 (a b g : K) : X2AuxInputs.D a b g =
    C (kD1_0 a b g)
    + C (kD1_1 a b g) * X 1
    + C (kD1_2 a b g) * X 1 * X 2
    + C (kD1_3 a b g) * X 1^(2:ℕ) := by
  simp only [X2AuxInputs.D, kD1_0, kD1_1, kD1_2, kD1_3,
    map_add, map_mul, map_pow, map_neg, map_one, map_ofNat]
  refl_ring1

lemma hR1 (a b g : K) : X2AuxInputs.R a b g =
    C (kR1_0 a b g) * X 2
    + C (kR1_1 a b g) * X 2^(2:ℕ)
    + C (kR1_2 a b g) * X 2^(3:ℕ)
    + C (kR1_3 a b g) * X 1 * X 2
    + C (kR1_4 a b g) * X 1 * X 2^(2:ℕ)
    + C (kR1_5 a b g) * X 1^(2:ℕ) * X 2
    + C (kR1_6 a b g) * X 1^(3:ℕ) := by
  simp only [X2AuxInputs.R, kR1_0, kR1_1, kR1_2, kR1_3, kR1_4, kR1_5, kR1_6,
    map_add, map_mul, map_pow, map_neg, map_one, map_ofNat]
  refl_ring1

lemma hP1 (a b g : K) : X2AuxInputs.Pemb a b g =
    C (kP1_0 a b g)
    + C (kP1_1 a b g) * X 2^(2:ℕ)
    + C (kP1_2 a b g) * X 2^(3:ℕ)
    + C (kP1_3 a b g) * X 2^(5:ℕ)
    + C (kP1_4 a b g) * X 1 * X 2^(2:ℕ)
    + C (kP1_5 a b g) * X 1 * X 2^(3:ℕ)
    + C (kP1_6 a b g) * X 1 * X 2^(4:ℕ)
    + C (kP1_7 a b g) * X 1^(2:ℕ)
    + C (kP1_8 a b g) * X 1^(2:ℕ) * X 2^(2:ℕ)
    + C (kP1_9 a b g) * X 1^(2:ℕ) * X 2^(3:ℕ)
    + C (kP1_10 a b g) * X 1^(3:ℕ)
    + C (kP1_11 a b g) * X 1^(3:ℕ) * X 2
    + C (kP1_12 a b g) * X 1^(3:ℕ) * X 2^(2:ℕ)
    + C (kP1_13 a b g) * X 1^(4:ℕ)
    + C (kP1_14 a b g) * X 1^(5:ℕ) := by
  have h0 : (Fin.succ (0 : Fin 2) : Fin 3) = 1 := by decide
  have h1 : (Fin.succ (1 : Fin 2) : Fin 3) = 2 := by decide
  simp only [X2AuxInputs.Pemb, Work.MotAS.ASZElim.P, map_add, map_mul, map_pow,
    MvPolynomial.rename_C, MvPolynomial.rename_X, h0, h1, kP1_0, kP1_1, kP1_2, kP1_3, kP1_4, kP1_5, kP1_6, kP1_7, kP1_8, kP1_9, kP1_10, kP1_11, kP1_12, kP1_13, kP1_14]
  refl_ring1

lemma struct1 (a b g : K) :
    N1 a b g - X2AuxInputs.Pemb a b g * S1 a b g - 5 * C1 a b g =
    C (E1_0 a b g) * X 2
    + C (E1_1 a b g) * X 2^(2:ℕ)
    + C (E1_2 a b g) * X 2^(3:ℕ)
    + C (E1_3 a b g) * X 2^(4:ℕ)
    + C (E1_4 a b g) * X 2^(5:ℕ)
    + C (E1_5 a b g) * X 2^(6:ℕ)
    + C (E1_6 a b g) * X 2^(7:ℕ)
    + C (E1_7 a b g) * X 2^(8:ℕ)
    + C (E1_8 a b g) * X 2^(9:ℕ)
    + C (E1_9 a b g) * X 1 * X 2
    + C (E1_10 a b g) * X 1 * X 2^(2:ℕ)
    + C (E1_11 a b g) * X 1 * X 2^(3:ℕ)
    + C (E1_12 a b g) * X 1 * X 2^(4:ℕ)
    + C (E1_13 a b g) * X 1 * X 2^(5:ℕ)
    + C (E1_14 a b g) * X 1 * X 2^(6:ℕ)
    + C (E1_15 a b g) * X 1 * X 2^(7:ℕ)
    + C (E1_16 a b g) * X 1 * X 2^(8:ℕ)
    + C (E1_17 a b g) * X 1^(2:ℕ) * X 2
    + C (E1_18 a b g) * X 1^(2:ℕ) * X 2^(2:ℕ)
    + C (E1_19 a b g) * X 1^(2:ℕ) * X 2^(3:ℕ)
    + C (E1_20 a b g) * X 1^(2:ℕ) * X 2^(4:ℕ)
    + C (E1_21 a b g) * X 1^(2:ℕ) * X 2^(5:ℕ)
    + C (E1_22 a b g) * X 1^(2:ℕ) * X 2^(6:ℕ)
    + C (E1_23 a b g) * X 1^(2:ℕ) * X 2^(7:ℕ)
    + C (E1_24 a b g) * X 1^(3:ℕ)
    + C (E1_25 a b g) * X 1^(3:ℕ) * X 2
    + C (E1_26 a b g) * X 1^(3:ℕ) * X 2^(2:ℕ)
    + C (E1_27 a b g) * X 1^(3:ℕ) * X 2^(3:ℕ)
    + C (E1_28 a b g) * X 1^(3:ℕ) * X 2^(4:ℕ)
    + C (E1_29 a b g) * X 1^(3:ℕ) * X 2^(5:ℕ)
    + C (E1_30 a b g) * X 1^(3:ℕ) * X 2^(6:ℕ)
    + C (E1_31 a b g) * X 1^(4:ℕ)
    + C (E1_32 a b g) * X 1^(4:ℕ) * X 2
    + C (E1_33 a b g) * X 1^(4:ℕ) * X 2^(2:ℕ)
    + C (E1_34 a b g) * X 1^(4:ℕ) * X 2^(3:ℕ)
    + C (E1_35 a b g) * X 1^(4:ℕ) * X 2^(4:ℕ)
    + C (E1_36 a b g) * X 1^(4:ℕ) * X 2^(5:ℕ)
    + C (E1_37 a b g) * X 1^(5:ℕ)
    + C (E1_38 a b g) * X 1^(5:ℕ) * X 2
    + C (E1_39 a b g) * X 1^(5:ℕ) * X 2^(2:ℕ)
    + C (E1_40 a b g) * X 1^(5:ℕ) * X 2^(3:ℕ)
    + C (E1_41 a b g) * X 1^(5:ℕ) * X 2^(4:ℕ)
    + C (E1_42 a b g) * X 1^(6:ℕ)
    + C (E1_43 a b g) * X 1^(6:ℕ) * X 2
    + C (E1_44 a b g) * X 1^(6:ℕ) * X 2^(2:ℕ)
    + C (E1_45 a b g) * X 1^(6:ℕ) * X 2^(3:ℕ)
    + C (E1_46 a b g) * X 1^(7:ℕ)
    + C (E1_47 a b g) * X 1^(7:ℕ) * X 2
    + C (E1_48 a b g) * X 1^(7:ℕ) * X 2^(2:ℕ)
    + C (E1_49 a b g) * X 1^(8:ℕ)
    + C (E1_50 a b g) * X 1^(8:ℕ) * X 2
    + C (E1_51 a b g) * X 1^(9:ℕ) := by
  rw [N1, hD1, hR1, hP1]
  simp only [S1, C1, C1_0, C1_1, C1_2, C1_3, f10, f11, f12, f13,
    E1_0, E1_1, E1_2, E1_3, E1_4, E1_5, E1_6, E1_7, E1_8, E1_9, E1_10, E1_11, E1_12, E1_13, E1_14, E1_15, E1_16, E1_17, E1_18, E1_19, E1_20, E1_21, E1_22, E1_23, E1_24, E1_25, E1_26, E1_27, E1_28, E1_29, E1_30, E1_31, E1_32, E1_33, E1_34, E1_35, E1_36, E1_37, E1_38, E1_39, E1_40, E1_41, E1_42, E1_43, E1_44, E1_45, E1_46, E1_47, E1_48, E1_49, E1_50, E1_51,
    map_add, map_sub, map_mul, map_pow, map_neg, map_one, map_ofNat]
  refl_ring1

lemma e1_0 (a b g : K) : E1_0 a b g = 0 := by
  simp only [E1_0, cd1_0_0, fd10_0, fd11_0, kD1_0, kP1_0, kR1_0, sd1_0]
  refl_ring1

lemma e1_1 (a b g : K) : E1_1 a b g = 0 := by
  simp only [E1_1, fd10_1, fd11_0, kD1_0, kR1_1]
  refl_ring1

lemma e1_2 (a b g : K) : E1_2 a b g = 0 := by
  simp only [E1_2, cd1_0_1, fd10_2, fd11_0, fd11_1, fd12_0, fd13_0, kD1_0, kP1_1, kR1_0, kR1_2, sd1_0]
  refl_ring1

lemma e1_3 (a b g : K) : E1_3 a b g = 0 := by
  simp only [E1_3, cd1_0_2, fd11_1, fd12_0, fd13_0, kD1_0, kP1_2, kR1_0, kR1_1, sd1_0]
  refl_ring1

lemma e1_4 (a b g : K) : E1_4 a b g = 0 := by
  simp only [E1_4, cd1_0_3, fd11_1, fd12_0, fd13_0, kD1_0, kR1_0, kR1_1, kR1_2]
  refl_ring1

lemma e1_5 (a b g : K) : E1_5 a b g = 0 := by
  simp only [E1_5, cd1_0_4, fd12_0, fd13_0, kD1_0, kP1_3, kR1_0, kR1_1, kR1_2, sd1_0]
  refl_ring1

lemma e1_6 (a b g : K) : E1_6 a b g = 0 := by
  simp only [E1_6, cd1_0_5, fd12_0, fd13_0, kD1_0, kR1_0, kR1_1, kR1_2]
  refl_ring1

lemma e1_7 (a b g : K) : E1_7 a b g = 0 := by
  simp only [E1_7, cd1_0_6, fd13_0, kR1_1, kR1_2]
  refl_ring1

lemma e1_8 (a b g : K) : E1_8 a b g = 0 := by
  simp only [E1_8, cd1_0_7, fd13_0, kR1_2]
  refl_ring1

lemma e1_9 (a b g : K) : E1_9 a b g = 0 := by
  simp only [E1_9, cd1_0_8, fd10_0, fd10_3, fd11_0, kD1_0, kD1_1, kP1_0, kR1_0, kR1_3, sd1_1]
  refl_ring1

lemma e1_10 (a b g : K) : E1_10 a b g = 0 := by
  simp only [E1_10, cd1_0_9, fd10_0, fd10_1, fd10_4, fd11_0, fd11_2, kD1_0, kD1_1, kD1_2, kR1_0, kR1_1, kR1_4]
  refl_ring1

lemma e1_11 (a b g : K) : E1_11 a b g = 0 := by
  simp only [E1_11, cd1_0_10, fd10_1, fd10_2, fd11_0, fd11_1, fd11_2, fd12_0, fd13_0, kD1_0, kD1_1, kD1_2, kP1_1, kP1_4, kR1_0, kR1_1, kR1_2, kR1_3, sd1_0, sd1_1]
  refl_ring1

lemma e1_12 (a b g : K) : E1_12 a b g = 0 := by
  simp only [E1_12, cd1_0_11, fd10_2, fd11_0, fd11_1, fd11_2, fd12_0, fd13_0, kD1_0, kD1_1, kD1_2, kP1_2, kP1_5, kR1_0, kR1_1, kR1_2, kR1_3, kR1_4, sd1_0, sd1_1]
  refl_ring1

lemma e1_13 (a b g : K) : E1_13 a b g = 0 := by
  simp only [E1_13, cd1_0_12, fd11_1, fd12_0, fd13_0, kD1_0, kD1_1, kD1_2, kP1_6, kR1_0, kR1_1, kR1_2, kR1_3, kR1_4, sd1_0]
  refl_ring1

lemma e1_14 (a b g : K) : E1_14 a b g = 0 := by
  simp only [E1_14, cd1_0_13, fd11_1, fd12_0, fd13_0, kD1_0, kD1_1, kD1_2, kP1_3, kR1_0, kR1_1, kR1_2, kR1_3, kR1_4, sd1_1]
  refl_ring1

lemma e1_15 (a b g : K) : E1_15 a b g = 0 := by
  simp only [E1_15, cd1_1_0, fd12_0, fd13_0, kD1_1, kD1_2, kR1_1, kR1_2, kR1_3, kR1_4]
  refl_ring1

lemma e1_16 (a b g : K) : E1_16 a b g = 0 := by
  simp only [E1_16, cd1_1_1, fd12_0, fd13_0, kD1_2, kR1_2, kR1_4]
  refl_ring1

lemma e1_17 (a b g : K) : E1_17 a b g = 0 := by
  simp only [E1_17, cd1_1_2, fd10_0, fd10_3, fd10_5, fd11_0, fd11_3, kD1_0, kD1_1, kD1_3, kP1_0, kP1_7, kR1_0, kR1_3, kR1_5, sd1_0, sd1_2]
  refl_ring1

lemma e1_18 (a b g : K) : E1_18 a b g = 0 := by
  simp only [E1_18, cd1_1_3, fd10_0, fd10_1, fd10_3, fd10_4, fd11_0, fd11_2, fd11_3, kD1_0, kD1_1, kD1_2, kD1_3, kR1_0, kR1_1, kR1_3, kR1_4]
  refl_ring1

lemma e1_19 (a b g : K) : E1_19 a b g = 0 := by
  simp only [E1_19, cd1_1_4, fd10_0, fd10_1, fd10_2, fd10_4, fd11_0, fd11_1, fd11_2, fd11_3, fd12_0, fd13_0, kD1_0, kD1_1, kD1_2, kD1_3, kP1_1, kP1_4, kP1_8, kR1_0, kR1_1, kR1_2, kR1_3, kR1_4, kR1_5, sd1_0, sd1_1, sd1_2]
  refl_ring1

lemma e1_20 (a b g : K) : E1_20 a b g = 0 := by
  simp only [E1_20, cd1_1_5, fd10_1, fd10_2, fd11_0, fd11_1, fd11_2, fd12_0, fd13_0, kD1_0, kD1_1, kD1_2, kD1_3, kP1_2, kP1_5, kP1_9, kR1_0, kR1_1, kR1_2, kR1_3, kR1_4, kR1_5, sd1_0, sd1_1, sd1_2]
  refl_ring1

lemma e1_21 (a b g : K) : E1_21 a b g = 0 := by
  simp only [E1_21, cd1_1_6, fd10_2, fd11_0, fd11_1, fd11_2, fd12_0, fd13_0, kD1_0, kD1_1, kD1_2, kD1_3, kP1_6, kR1_0, kR1_1, kR1_2, kR1_3, kR1_4, kR1_5, sd1_1]
  refl_ring1

lemma e1_22 (a b g : K) : E1_22 a b g = 0 := by
  simp only [E1_22, cd1_1_7, fd11_1, fd12_0, fd13_0, kD1_1, kD1_2, kD1_3, kP1_3, kR1_1, kR1_2, kR1_3, kR1_4, kR1_5, sd1_2]
  refl_ring1

lemma e1_23 (a b g : K) : E1_23 a b g = 0 := by
  simp only [E1_23, cd1_1_8, fd11_1, fd12_0, fd13_0, kD1_2, kD1_3, kR1_2, kR1_4, kR1_5]
  refl_ring1

lemma e1_24 (a b g : K) : E1_24 a b g = 0 := by
  simp only [E1_24, fd10_6, fd11_0, kD1_0, kR1_6]
  refl_ring1

lemma e1_25 (a b g : K) : E1_25 a b g = 0 := by
  simp only [E1_25, cd1_1_9, fd10_0, fd10_3, fd10_5, fd11_0, fd11_3, kD1_0, kD1_1, kD1_3, kP1_0, kP1_10, kP1_7, kR1_0, kR1_3, kR1_5, sd1_0, sd1_1, sd1_3]
  refl_ring1

lemma e1_26 (a b g : K) : E1_26 a b g = 0 := by
  simp only [E1_26, cd1_1_10, fd10_0, fd10_1, fd10_3, fd10_4, fd10_5, fd11_0, fd11_1, fd11_2, fd11_3, fd12_0, fd13_0, kD1_0, kD1_1, kD1_2, kD1_3, kP1_11, kR1_0, kR1_1, kR1_3, kR1_4, kR1_5, kR1_6, sd1_0]
  refl_ring1

lemma e1_27 (a b g : K) : E1_27 a b g = 0 := by
  simp only [E1_27, cd1_1_11, fd10_0, fd10_1, fd10_2, fd10_3, fd10_4, fd11_0, fd11_1, fd11_2, fd11_3, fd12_0, fd13_0, kD1_0, kD1_1, kD1_2, kD1_3, kP1_1, kP1_12, kP1_4, kP1_8, kR1_0, kR1_1, kR1_2, kR1_3, kR1_4, kR1_5, kR1_6, sd1_0, sd1_1, sd1_2, sd1_3]
  refl_ring1

lemma e1_28 (a b g : K) : E1_28 a b g = 0 := by
  simp only [E1_28, cd1_1_12, fd10_0, fd10_1, fd10_2, fd10_4, fd11_0, fd11_1, fd11_2, fd11_3, fd12_0, fd13_0, kD1_0, kD1_1, kD1_2, kD1_3, kP1_2, kP1_5, kP1_9, kR1_0, kR1_1, kR1_2, kR1_3, kR1_4, kR1_5, kR1_6, sd1_1, sd1_2, sd1_3]
  refl_ring1

lemma e1_29 (a b g : K) : E1_29 a b g = 0 := by
  simp only [E1_29, cd1_1_13, fd10_1, fd10_2, fd11_1, fd11_2, fd12_0, fd13_0, kD1_1, kD1_2, kD1_3, kP1_6, kR1_1, kR1_2, kR1_3, kR1_4, kR1_5, kR1_6, sd1_2]
  refl_ring1

lemma e1_30 (a b g : K) : E1_30 a b g = 0 := by
  simp only [E1_30, cd1_2_0, fd10_2, fd11_1, fd11_2, fd12_0, fd13_0, kD1_2, kD1_3, kP1_3, kR1_2, kR1_4, kR1_5, kR1_6, sd1_3]
  refl_ring1

lemma e1_31 (a b g : K) : E1_31 a b g = 0 := by
  simp only [E1_31, cd1_2_1, fd10_6, fd11_0, kD1_0, kD1_1, kP1_0, kR1_6, sd1_4]
  refl_ring1

lemma e1_32 (a b g : K) : E1_32 a b g = 0 := by
  simp only [E1_32, cd1_2_2, fd10_0, fd10_3, fd10_5, fd10_6, fd11_0, fd11_2, fd11_3, kD1_0, kD1_1, kD1_2, kD1_3, kP1_10, kP1_13, kP1_7, kR1_0, kR1_3, kR1_5, kR1_6, sd1_0, sd1_1, sd1_2]
  refl_ring1

lemma e1_33 (a b g : K) : E1_33 a b g = 0 := by
  simp only [E1_33, cd1_2_3, fd10_0, fd10_1, fd10_3, fd10_4, fd10_5, fd11_0, fd11_1, fd11_2, fd11_3, fd12_0, fd13_0, kD1_0, kD1_1, kD1_2, kD1_3, kP1_1, kP1_11, kR1_0, kR1_1, kR1_3, kR1_4, kR1_5, kR1_6, sd1_1, sd1_4]
  refl_ring1

lemma e1_34 (a b g : K) : E1_34 a b g = 0 := by
  simp only [E1_34, cd1_2_4, fd10_0, fd10_1, fd10_2, fd10_3, fd10_4, fd10_5, fd11_0, fd11_1, fd11_2, fd11_3, fd12_0, fd13_0, kD1_0, kD1_1, kD1_2, kD1_3, kP1_12, kP1_2, kP1_4, kP1_8, kR1_0, kR1_1, kR1_2, kR1_3, kR1_4, kR1_5, kR1_6, sd1_1, sd1_2, sd1_3, sd1_4]
  refl_ring1

lemma e1_35 (a b g : K) : E1_35 a b g = 0 := by
  simp only [E1_35, cd1_2_5, fd10_1, fd10_2, fd10_3, fd10_4, fd11_1, fd11_2, fd11_3, fd12_0, fd13_0, kD1_1, kD1_2, kD1_3, kP1_5, kP1_9, kR1_1, kR1_2, kR1_3, kR1_4, kR1_5, kR1_6, sd1_2, sd1_3]
  refl_ring1

lemma e1_36 (a b g : K) : E1_36 a b g = 0 := by
  simp only [E1_36, cd1_2_6, fd10_2, fd10_4, fd11_1, fd11_2, fd11_3, fd12_0, fd13_0, kD1_2, kD1_3, kP1_3, kP1_6, kR1_2, kR1_4, kR1_5, kR1_6, sd1_3, sd1_4]
  refl_ring1

lemma e1_37 (a b g : K) : E1_37 a b g = 0 := by
  simp only [E1_37, cd1_2_7, fd10_6, fd11_0, fd11_3, kD1_0, kD1_1, kD1_3, kR1_6]
  refl_ring1

lemma e1_38 (a b g : K) : E1_38 a b g = 0 := by
  simp only [E1_38, cd1_2_8, fd10_0, fd10_3, fd10_5, fd10_6, fd11_0, fd11_2, fd11_3, kD1_0, kD1_1, kD1_2, kD1_3, kP1_10, kP1_13, kP1_14, kP1_7, kR1_0, kR1_3, kR1_5, kR1_6, sd1_0, sd1_1, sd1_2, sd1_3]
  refl_ring1

lemma e1_39 (a b g : K) : E1_39 a b g = 0 := by
  simp only [E1_39, cd1_2_9, fd10_0, fd10_1, fd10_3, fd10_4, fd10_5, fd10_6, fd11_0, fd11_1, fd11_2, fd11_3, fd12_0, fd13_0, kD1_0, kD1_1, kD1_2, kD1_3, kP1_11, kP1_4, kR1_0, kR1_1, kR1_3, kR1_4, kR1_5, kR1_6, sd1_2, sd1_4]
  refl_ring1

lemma e1_40 (a b g : K) : E1_40 a b g = 0 := by
  simp only [E1_40, cd1_2_10, fd10_1, fd10_2, fd10_3, fd10_4, fd10_5, fd11_1, fd11_2, fd11_3, fd12_0, fd13_0, kD1_1, kD1_2, kD1_3, kP1_12, kP1_5, kP1_8, kR1_1, kR1_2, kR1_3, kR1_4, kR1_5, kR1_6, sd1_2, sd1_3, sd1_4]
  refl_ring1

lemma e1_41 (a b g : K) : E1_41 a b g = 0 := by
  simp only [E1_41, cd1_2_11, fd10_2, fd10_4, fd10_5, fd11_1, fd11_2, fd11_3, fd12_0, fd13_0, kD1_2, kD1_3, kP1_6, kP1_9, kR1_2, kR1_4, kR1_5, kR1_6, sd1_3, sd1_4]
  refl_ring1

lemma e1_42 (a b g : K) : E1_42 a b g = 0 := by
  simp only [E1_42, cd1_2_12, fd10_6, fd11_0, fd11_3, kD1_0, kD1_1, kD1_3, kP1_7, kR1_6, sd1_4]
  refl_ring1

lemma e1_43 (a b g : K) : E1_43 a b g = 0 := by
  simp only [E1_43, cd1_2_13, fd10_0, fd10_3, fd10_5, fd10_6, fd11_0, fd11_2, fd11_3, fd12_0, fd13_0, kD1_0, kD1_1, kD1_2, kD1_3, kP1_10, kP1_13, kP1_14, kR1_0, kR1_3, kR1_5, kR1_6, sd1_1, sd1_2, sd1_3]
  refl_ring1

lemma e1_44 (a b g : K) : E1_44 a b g = 0 := by
  simp only [E1_44, cd1_3_0, fd10_1, fd10_3, fd10_4, fd10_5, fd10_6, fd11_1, fd11_2, fd11_3, fd12_0, fd13_0, kD1_1, kD1_2, kD1_3, kP1_11, kP1_8, kR1_1, kR1_3, kR1_4, kR1_5, kR1_6, sd1_3, sd1_4]
  refl_ring1

lemma e1_45 (a b g : K) : E1_45 a b g = 0 := by
  simp only [E1_45, cd1_3_1, fd10_2, fd10_4, fd10_5, fd10_6, fd11_1, fd11_2, fd11_3, fd12_0, fd13_0, kD1_2, kD1_3, kP1_12, kP1_9, kR1_2, kR1_4, kR1_5, kR1_6, sd1_3, sd1_4]
  refl_ring1

lemma e1_46 (a b g : K) : E1_46 a b g = 0 := by
  simp only [E1_46, cd1_3_2, fd10_6, fd11_0, fd11_3, kD1_0, kD1_1, kD1_3, kP1_10, kR1_6, sd1_4]
  refl_ring1

lemma e1_47 (a b g : K) : E1_47 a b g = 0 := by
  simp only [E1_47, cd1_3_3, fd10_3, fd10_5, fd10_6, fd11_2, fd11_3, fd12_0, fd13_0, kD1_1, kD1_2, kD1_3, kP1_11, kP1_13, kP1_14, kR1_3, kR1_5, kR1_6, sd1_2, sd1_3, sd1_4]
  refl_ring1

lemma e1_48 (a b g : K) : E1_48 a b g = 0 := by
  simp only [E1_48, cd1_3_4, fd10_4, fd10_5, fd10_6, fd11_1, fd11_2, fd11_3, fd12_0, fd13_0, kD1_2, kD1_3, kP1_12, kR1_4, kR1_5, kR1_6, sd1_4]
  refl_ring1

lemma e1_49 (a b g : K) : E1_49 a b g = 0 := by
  simp only [E1_49, cd1_3_5, fd10_6, fd11_3, kD1_1, kD1_3, kP1_13, kR1_6, sd1_4]
  refl_ring1

lemma e1_50 (a b g : K) : E1_50 a b g = 0 := by
  simp only [E1_50, cd1_3_6, fd10_5, fd10_6, fd11_2, fd11_3, fd12_0, fd13_0, kD1_2, kD1_3, kP1_14, kR1_5, kR1_6, sd1_3]
  refl_ring1

lemma e1_51 (a b g : K) : E1_51 a b g = 0 := by
  simp only [E1_51, cd1_3_7, fd10_6, fd11_3, fd13_0, kD1_3, kP1_14, kR1_6, sd1_4]
  refl_ring1

theorem hB1 (a b g : K) :
    N1 a b g - X2AuxInputs.Pemb a b g * S1 a b g = (5 : MvPolynomial (Fin 3) K) * C1 a b g := by
  rw [← sub_eq_zero, struct1]
  simp only [e1_0, e1_1, e1_2, e1_3, e1_4, e1_5, e1_6, e1_7, e1_8, e1_9, e1_10, e1_11, e1_12, e1_13, e1_14, e1_15, e1_16, e1_17, e1_18, e1_19, e1_20, e1_21, e1_22, e1_23, e1_24, e1_25, e1_26, e1_27, e1_28, e1_29, e1_30, e1_31, e1_32, e1_33, e1_34, e1_35, e1_36, e1_37, e1_38, e1_39, e1_40, e1_41, e1_42, e1_43, e1_44, e1_45, e1_46, e1_47, e1_48, e1_49, e1_50, e1_51, map_zero, zero_mul, add_zero]

#print axioms Work.MotC5N3.CertDemo.hB1

end Work.MotC5N3.CertDemo
