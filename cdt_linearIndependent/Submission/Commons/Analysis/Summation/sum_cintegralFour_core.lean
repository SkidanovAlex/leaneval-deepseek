import Mathlib.Data.Nat.Choose.Cast
import Submission.Commons.Analysis.Summation.sum_cintegralOne_core
import Submission.Commons.Analysis.Summation.sum_cintegralTwo_core_corrected

noncomputable section
open scoped BigOperators Nat
open Filter Topology

namespace Commons.Analysis.Summation
namespace CdtFourCore

/-! ## Binomial `(m+8 choose 8)` as a degree-8 polynomial -/

lemma asc8 (n : ℕ) : n.ascFactorial 8 =
    n * (n + 1) * (n + 2) * (n + 3) * (n + 4) * (n + 5) * (n + 6) * (n + 7) := by
  simp [Nat.ascFactorial_succ, Nat.ascFactorial_zero]
  ring

lemma factorial_add_eight (m : ℕ) : (m + 8)! =
    m ! * (m + 1) * (m + 2) * (m + 3) * (m + 4) * (m + 5) * (m + 6) * (m + 7) * (m + 8) := by
  rw [← Nat.factorial_mul_ascFactorial m 8]
  have h := asc8 (m + 1)
  rw [h]
  ring

lemma choose28 (m : ℕ) :
    (Nat.choose (m + 8) 8 : ℝ) =
      (1 / 40320 : ℝ) *
        (((m : ℝ) + 1) * ((m : ℝ) + 2) * ((m : ℝ) + 3) * ((m : ℝ) + 4) *
          ((m : ℝ) + 5) * ((m : ℝ) + 6) * ((m : ℝ) + 7) * ((m : ℝ) + 8)) := by
  have hcast := Nat.cast_choose ℝ (a := 8) (b := m + 8) (by omega : 8 ≤ m + 8)
  rw [hcast]
  have h8 : ((8 : ℕ)! : ℝ) = 40320 := by norm_num
  have hsub : ((m + 8 - 8) : ℕ) = m := by omega
  rw [h8, hsub]
  have hfacR : ((m + 8)! : ℝ) = (m ! : ℝ) *
      (((m : ℝ) + 1) * ((m : ℝ) + 2) * ((m : ℝ) + 3) * ((m : ℝ) + 4) *
        ((m : ℝ) + 5) * ((m : ℝ) + 6) * ((m : ℝ) + 7) * ((m : ℝ) + 8)) := by
    norm_num [factorial_add_eight, Nat.cast_mul]
    ring
  rw [hfacR]
  have hm : (m ! : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_ne_zero m)
  field_simp [hm]

@[simp] lemma c9_0 : (Nat.choose 9 0 : ℝ) = 1 := by
  rw [Nat.cast_choose ℝ (by decide : 0 ≤ 9)]; norm_num
@[simp] lemma c9_1 : (Nat.choose 9 1 : ℝ) = 9 := by
  rw [Nat.cast_choose ℝ (by decide : 1 ≤ 9)]; norm_num
@[simp] lemma c9_2 : (Nat.choose 9 2 : ℝ) = 36 := by
  rw [Nat.cast_choose ℝ (by decide : 2 ≤ 9)]; norm_num
@[simp] lemma c9_3 : (Nat.choose 9 3 : ℝ) = 84 := by
  rw [Nat.cast_choose ℝ (by decide : 3 ≤ 9)]; norm_num
@[simp] lemma c9_4 : (Nat.choose 9 4 : ℝ) = 126 := by
  rw [Nat.cast_choose ℝ (by decide : 4 ≤ 9)]; norm_num
@[simp] lemma c9_5 : (Nat.choose 9 5 : ℝ) = 126 := by
  rw [Nat.cast_choose ℝ (by decide : 5 ≤ 9)]; norm_num
@[simp] lemma c9_6 : (Nat.choose 9 6 : ℝ) = 84 := by
  rw [Nat.cast_choose ℝ (by decide : 6 ≤ 9)]; norm_num
@[simp] lemma c9_7 : (Nat.choose 9 7 : ℝ) = 36 := by
  rw [Nat.cast_choose ℝ (by decide : 7 ≤ 9)]; norm_num
@[simp] lemma c9_8 : (Nat.choose 9 8 : ℝ) = 9 := by
  rw [Nat.cast_choose ℝ (by decide : 8 ≤ 9)]; norm_num
@[simp] lemma c9_9 : (Nat.choose 9 9 : ℝ) = 1 := by
  rw [Nat.cast_choose ℝ (by decide : 9 ≤ 9)]; norm_num

/-! ## The `m`-summand and its pointwise closed-form decomposition -/

/-- The `m`-summand of the four-core sum. -/
def Vm4 (m : ℕ) : ℝ :=
  (6561 : ℝ) * (Nat.choose (m + 8) 8 : ℝ) *
    (∑ i ∈ Finset.range 10,
      ((-1 : ℝ) ^ i * (Nat.choose 9 i : ℝ)) *
        (1944 / (xm m (5 + i) * xm m (8 + i) * xm m (11 + i) * xm m (14 + i) * xm m (17 + i))) ^ 2)

/-- Squared-term part of the closed-form decomposition. -/
def W14 (m : ℕ) : ℝ :=
  (748 : ℝ) * (1 / (xm m 7)^2) - (3850 : ℝ) * (1 / (xm m 10)^2)
    - (4345 : ℝ) * (1 / (xm m 13)^2) + (27560 : ℝ) * (1 / (xm m 16)^2)
    - (23920 : ℝ) * (1 / (xm m 19)^2) - (988 : ℝ) * (1 / (xm m 22)^2)
    + (5434 : ℝ) * (1 / (xm m 25)^2)
    - (494/9 : ℝ) * (1 / (xm m 5)^2) - (8840/9 : ℝ) * (1 / (xm m 8)^2)
    + (8840 : ℝ) * (1 / (xm m 11)^2) - (10175 : ℝ) * (1 / (xm m 14)^2)
    - (14245 : ℝ) * (1 / (xm m 17)^2) + (25432 : ℝ) * (1 / (xm m 20)^2)
    - (63580/9 : ℝ) * (1 / (xm m 23)^2) - (21505/9 : ℝ) * (1 / (xm m 26)^2)

/-- Telescoping-pair part of the closed-form decomposition. -/
def W24 (m : ℕ) : ℝ :=
  (253927/22680 : ℝ) * (1 / xm m 5 - 1 / xm m 8) + (19683/56 : ℝ) * (1 / xm m 6 - 1 / xm m 9)
    - (750557/630 : ℝ) * (1 / xm m 7 - 1 / xm m 10) + (14793707/22680 : ℝ) * (1 / xm m 8 - 1 / xm m 11)
    + (6561/56 : ℝ) * (1 / xm m 9 - 1 / xm m 12) + (676387/420 : ℝ) * (1 / xm m 10 - 1 / xm m 13)
    + (60921587/22680 : ℝ) * (1 / xm m 11 - 1 / xm m 14) - (3588867/280 : ℝ) * (1 / xm m 12 - 1 / xm m 15)
    + (27431057/2520 : ℝ) * (1 / xm m 13 - 1 / xm m 16) - (29047273/3780 : ℝ) * (1 / xm m 14 - 1 / xm m 17)
    + (951345/56 : ℝ) * (1 / xm m 15 - 1 / xm m 18) - (4094689/360 : ℝ) * (1 / xm m 16 - 1 / xm m 19)
    - (162408593/22680 : ℝ) * (1 / xm m 17 - 1 / xm m 20) + (216513/28 : ℝ) * (1 / xm m 18 - 1 / xm m 21)
    - (3804821/840 : ℝ) * (1 / xm m 19 - 1 / xm m 22) + (7201325/648 : ℝ) * (1 / xm m 20 - 1 / xm m 23)
    - (19683/2 : ℝ) * (1 / xm m 21 - 1 / xm m 24) + (4676083/2520 : ℝ) * (1 / xm m 22 - 1 / xm m 25)
    + (2701495/4536 : ℝ) * (1 / xm m 23 - 1 / xm m 26)

/-- The closed-form decomposition of the summand (as `W1 + W2`). -/
def Vd4 (m : ℕ) : ℝ := W14 m + W24 m

set_option maxHeartbeats 8000000 in
lemma vm4_decomp (m : ℕ) : Vm4 m = Vd4 m := by
  unfold Vm4 Vd4 W14 W24
  rw [choose28]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero,
    c9_0, c9_1, c9_2, c9_3, c9_4, c9_5, c9_6, c9_7, c9_8, c9_9]
  norm_num
  simp_rw [xm_eq]
  norm_num
  have h5 : (3 * (m : ℝ) + 5) ≠ 0 := by positivity
  have h6 : (3 * (m : ℝ) + 6) ≠ 0 := by positivity
  have h7 : (3 * (m : ℝ) + 7) ≠ 0 := by positivity
  have h8 : (3 * (m : ℝ) + 8) ≠ 0 := by positivity
  have h9 : (3 * (m : ℝ) + 9) ≠ 0 := by positivity
  have h10 : (3 * (m : ℝ) + 10) ≠ 0 := by positivity
  have h11 : (3 * (m : ℝ) + 11) ≠ 0 := by positivity
  have h12 : (3 * (m : ℝ) + 12) ≠ 0 := by positivity
  have h13 : (3 * (m : ℝ) + 13) ≠ 0 := by positivity
  have h14 : (3 * (m : ℝ) + 14) ≠ 0 := by positivity
  have h15 : (3 * (m : ℝ) + 15) ≠ 0 := by positivity
  have h16 : (3 * (m : ℝ) + 16) ≠ 0 := by positivity
  have h17 : (3 * (m : ℝ) + 17) ≠ 0 := by positivity
  have h18 : (3 * (m : ℝ) + 18) ≠ 0 := by positivity
  have h19 : (3 * (m : ℝ) + 19) ≠ 0 := by positivity
  have h20 : (3 * (m : ℝ) + 20) ≠ 0 := by positivity
  have h21 : (3 * (m : ℝ) + 21) ≠ 0 := by positivity
  have h22 : (3 * (m : ℝ) + 22) ≠ 0 := by positivity
  have h23 : (3 * (m : ℝ) + 23) ≠ 0 := by positivity
  have h24 : (3 * (m : ℝ) + 24) ≠ 0 := by positivity
  have h25 : (3 * (m : ℝ) + 25) ≠ 0 := by positivity
  have h26 : (3 * (m : ℝ) + 26) ≠ 0 := by positivity
  have hm1 : (m : ℝ) + 1 ≠ 0 := by positivity
  have hm2 : (m : ℝ) + 2 ≠ 0 := by positivity
  have hm3 : (m : ℝ) + 3 ≠ 0 := by positivity
  have hm4 : (m : ℝ) + 4 ≠ 0 := by positivity
  have hm5 : (m : ℝ) + 5 ≠ 0 := by positivity
  have hm6 : (m : ℝ) + 6 ≠ 0 := by positivity
  have hm7 : (m : ℝ) + 7 ≠ 0 := by positivity
  have hm8 : (m : ℝ) + 8 ≠ 0 := by positivity
  field_simp
  ring

/-! ## The statement denominators equal the `xm` denominators -/

lemma denom_statement4 (m : ℕ) : ∀ i : ℕ,
    ((((3 * m + 5 + i : ℕ) : ℝ) * ((3 * m + 8 + i : ℕ) : ℝ) *
        ((3 * m + 11 + i : ℕ) : ℝ) * ((3 * m + 14 + i : ℕ) : ℝ) *
          ((3 * m + 17 + i : ℕ) : ℝ)))
      = xm m (5 + i) * xm m (8 + i) * xm m (11 + i) * xm m (14 + i) * xm m (17 + i) := by
  intro i
  have h1 : (((3 * m + 5 + i : ℕ) : ℝ)) = xm m (5 + i) := by
    unfold xm
    congr 1
    omega
  have h2 : (((3 * m + 8 + i : ℕ) : ℝ)) = xm m (8 + i) := by
    unfold xm
    congr 1
    omega
  have h3 : (((3 * m + 11 + i : ℕ) : ℝ)) = xm m (11 + i) := by
    unfold xm
    congr 1
    omega
  have h4 : (((3 * m + 14 + i : ℕ) : ℝ)) = xm m (14 + i) := by
    unfold xm
    congr 1
    omega
  have h5 : (((3 * m + 17 + i : ℕ) : ℝ)) = xm m (17 + i) := by
    unfold xm
    congr 1
    omega
  rw [h1, h2, h3, h4, h5]

/-- The inner `i`-sum in the statement's form equals the `xm` form. -/
lemma inner_sum_statement4 (m : ℕ) :
    (∑ i ∈ Finset.range 10,
      ((-1 : ℝ) ^ i * (Nat.choose 9 i : ℝ)) *
        (1944 / ((((3 * m + 5 + i : ℕ) : ℝ) * ((3 * m + 8 + i : ℕ) : ℝ) *
          ((3 * m + 11 + i : ℕ) : ℝ) * ((3 * m + 14 + i : ℕ) : ℝ) *
            ((3 * m + 17 + i : ℕ) : ℝ)))) ^ 2)
    = (∑ i ∈ Finset.range 10,
      ((-1 : ℝ) ^ i * (Nat.choose 9 i : ℝ)) *
        (1944 / (xm m (5 + i) * xm m (8 + i) * xm m (11 + i) * xm m (14 + i) * xm m (17 + i))) ^ 2) := by
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  rw [denom_statement4 m i]

/-- The `m`-summand of the four-core sum, in the statement's form. -/
lemma vm4_eq_statement (m : ℕ) :
    (6561 : ℝ) * (Nat.choose (m + 8) 8 : ℝ) *
      (∑ i ∈ Finset.range 10,
        ((-1 : ℝ) ^ i * (Nat.choose 9 i : ℝ)) *
          (1944 / ((((3 * m + 5 + i : ℕ) : ℝ) * ((3 * m + 8 + i : ℕ) : ℝ) *
            ((3 * m + 11 + i : ℕ) : ℝ) * ((3 * m + 14 + i : ℕ) : ℝ) *
              ((3 * m + 17 + i : ℕ) : ℝ)))) ^ 2) =
      Vm4 m := by
  unfold Vm4
  rw [inner_sum_statement4 m]

/-! ## Small partial sums needed for the shifts -/

@[simp] lemma asum5 : Asum 5 = 3639749 / 3312400 := by norm_num [Asum, f1, xm]
@[simp] lemma asum6 : Asum 6 = 58443009 / 52998400 := by norm_num [Asum, f1, xm]
@[simp] lemma asum7 : Asum 7 = 21150924649 / 19132422400 := by norm_num [Asum, f1, xm]
@[simp] lemma asum8 : Asum 8 = 2564044988129 / 2315023110400 := by norm_num [Asum, f1, xm]
@[simp] lemma bsum5 : Bsum 5 = 3026081 / 9486400 := by norm_num [Bsum, f2, xm]
@[simp] lemma bsum6 : Bsum 6 = 884023809 / 2741569600 := by norm_num [Bsum, f2, xm]
@[simp] lemma bsum7 : Bsum 7 = 890877733 / 2741569600 := by norm_num [Bsum, f2, xm]
@[simp] lemma bsum8 : Bsum 8 = 474015890357 / 1450290318400 := by norm_num [Bsum, f2, xm]

/-! ## The values of the two pieces -/

/-- The value of the `W14`-sum. -/
noncomputable def V1val4 : ℝ :=
  (748 : ℝ) * (A - Asum 2) - (3850 : ℝ) * (A - Asum 3) - (4345 : ℝ) * (A - Asum 4)
    + (27560 : ℝ) * (A - Asum 5) - (23920 : ℝ) * (A - Asum 6) - (988 : ℝ) * (A - Asum 7)
    + (5434 : ℝ) * (A - Asum 8)
    - (494/9 : ℝ) * (B - Bsum 1) - (8840/9 : ℝ) * (B - Bsum 2) + (8840 : ℝ) * (B - Bsum 3)
    - (10175 : ℝ) * (B - Bsum 4) - (14245 : ℝ) * (B - Bsum 5) + (25432 : ℝ) * (B - Bsum 6)
    - (63580/9 : ℝ) * (B - Bsum 7) - (21505/9 : ℝ) * (B - Bsum 8)

/-- The value of the `W24`-sum. -/
noncomputable def V2val4 : ℝ :=
  (253927/22680 : ℝ) * (1 / xm 0 5) + (19683/56 : ℝ) * (1 / xm 0 6)
    - (750557/630 : ℝ) * (1 / xm 0 7) + (14793707/22680 : ℝ) * (1 / xm 0 8)
    + (6561/56 : ℝ) * (1 / xm 0 9) + (676387/420 : ℝ) * (1 / xm 0 10)
    + (60921587/22680 : ℝ) * (1 / xm 0 11) - (3588867/280 : ℝ) * (1 / xm 0 12)
    + (27431057/2520 : ℝ) * (1 / xm 0 13) - (29047273/3780 : ℝ) * (1 / xm 0 14)
    + (951345/56 : ℝ) * (1 / xm 0 15) - (4094689/360 : ℝ) * (1 / xm 0 16)
    - (162408593/22680 : ℝ) * (1 / xm 0 17) + (216513/28 : ℝ) * (1 / xm 0 18)
    - (3804821/840 : ℝ) * (1 / xm 0 19) + (7201325/648 : ℝ) * (1 / xm 0 20)
    - (19683/2 : ℝ) * (1 / xm 0 21) + (4676083/2520 : ℝ) * (1 / xm 0 22)
    + (2701495/4536 : ℝ) * (1 / xm 0 23)

/-- The value of the whole sum. -/
noncomputable def Vval4 : ℝ := V1val4 + V2val4

/-! ## `HasSum` of the two pieces of the decomposition -/

lemma hasSum_W14 : HasSum W14 V1val4 := by
  have h7 : HasSum (fun m : ℕ => (748 : ℝ) * (1 / (xm m 7)^2))
      ((748 : ℝ) * (A - Asum 2)) := by
    simpa using (CdtTwoCore.hasSum_sq1 2).mul_left (748 : ℝ)
  have h10 : HasSum (fun m : ℕ => (3850 : ℝ) * (1 / (xm m 10)^2))
      ((3850 : ℝ) * (A - Asum 3)) := by
    simpa using (CdtTwoCore.hasSum_sq1 3).mul_left (3850 : ℝ)
  have h13 : HasSum (fun m : ℕ => (4345 : ℝ) * (1 / (xm m 13)^2))
      ((4345 : ℝ) * (A - Asum 4)) := by
    simpa using (CdtTwoCore.hasSum_sq1 4).mul_left (4345 : ℝ)
  have h16 : HasSum (fun m : ℕ => (27560 : ℝ) * (1 / (xm m 16)^2))
      ((27560 : ℝ) * (A - Asum 5)) := by
    simpa using (CdtTwoCore.hasSum_sq1 5).mul_left (27560 : ℝ)
  have h19 : HasSum (fun m : ℕ => (23920 : ℝ) * (1 / (xm m 19)^2))
      ((23920 : ℝ) * (A - Asum 6)) := by
    simpa using (CdtTwoCore.hasSum_sq1 6).mul_left (23920 : ℝ)
  have h22 : HasSum (fun m : ℕ => (988 : ℝ) * (1 / (xm m 22)^2))
      ((988 : ℝ) * (A - Asum 7)) := by
    simpa using (CdtTwoCore.hasSum_sq1 7).mul_left (988 : ℝ)
  have h25 : HasSum (fun m : ℕ => (5434 : ℝ) * (1 / (xm m 25)^2))
      ((5434 : ℝ) * (A - Asum 8)) := by
    simpa using (CdtTwoCore.hasSum_sq1 8).mul_left (5434 : ℝ)
  have h5 : HasSum (fun m : ℕ => (494/9 : ℝ) * (1 / (xm m 5)^2))
      ((494/9 : ℝ) * (B - Bsum 1)) := by
    simpa using (CdtTwoCore.hasSum_sq2 1).mul_left (494/9 : ℝ)
  have h8 : HasSum (fun m : ℕ => (8840/9 : ℝ) * (1 / (xm m 8)^2))
      ((8840/9 : ℝ) * (B - Bsum 2)) := by
    simpa using (CdtTwoCore.hasSum_sq2 2).mul_left (8840/9 : ℝ)
  have h11 : HasSum (fun m : ℕ => (8840 : ℝ) * (1 / (xm m 11)^2))
      ((8840 : ℝ) * (B - Bsum 3)) := by
    simpa using (CdtTwoCore.hasSum_sq2 3).mul_left (8840 : ℝ)
  have h14 : HasSum (fun m : ℕ => (10175 : ℝ) * (1 / (xm m 14)^2))
      ((10175 : ℝ) * (B - Bsum 4)) := by
    simpa using (CdtTwoCore.hasSum_sq2 4).mul_left (10175 : ℝ)
  have h17 : HasSum (fun m : ℕ => (14245 : ℝ) * (1 / (xm m 17)^2))
      ((14245 : ℝ) * (B - Bsum 5)) := by
    simpa using (CdtTwoCore.hasSum_sq2 5).mul_left (14245 : ℝ)
  have h20 : HasSum (fun m : ℕ => (25432 : ℝ) * (1 / (xm m 20)^2))
      ((25432 : ℝ) * (B - Bsum 6)) := by
    simpa using (CdtTwoCore.hasSum_sq2 6).mul_left (25432 : ℝ)
  have h23 : HasSum (fun m : ℕ => (63580/9 : ℝ) * (1 / (xm m 23)^2))
      ((63580/9 : ℝ) * (B - Bsum 7)) := by
    simpa using (CdtTwoCore.hasSum_sq2 7).mul_left (63580/9 : ℝ)
  have h26 : HasSum (fun m : ℕ => (21505/9 : ℝ) * (1 / (xm m 26)^2))
      ((21505/9 : ℝ) * (B - Bsum 8)) := by
    simpa using (CdtTwoCore.hasSum_sq2 8).mul_left (21505/9 : ℝ)
  exact
    (((((((((((((h7.sub h10).sub h13).add h16).sub h19).sub h22).add h25).sub h5).sub h8).add h11).sub h14).sub h17).add h20).sub h23).sub h26

lemma hasSum_W24 : HasSum W24 V2val4 := by
  have hp5 : HasSum (fun m : ℕ => (253927/22680 : ℝ) * (1 / xm m 5 - 1 / xm m 8))
      ((253927/22680 : ℝ) * (1 / xm 0 5)) := by
    simpa using (CdtTwoCore.hasSum_pair 5 (by norm_num)).mul_left (253927/22680 : ℝ)
  have hp6 : HasSum (fun m : ℕ => (19683/56 : ℝ) * (1 / xm m 6 - 1 / xm m 9))
      ((19683/56 : ℝ) * (1 / xm 0 6)) := by
    simpa using (CdtTwoCore.hasSum_pair 6 (by norm_num)).mul_left (19683/56 : ℝ)
  have hp7 : HasSum (fun m : ℕ => (750557/630 : ℝ) * (1 / xm m 7 - 1 / xm m 10))
      ((750557/630 : ℝ) * (1 / xm 0 7)) := by
    simpa using (CdtTwoCore.hasSum_pair 7 (by norm_num)).mul_left (750557/630 : ℝ)
  have hp8 : HasSum (fun m : ℕ => (14793707/22680 : ℝ) * (1 / xm m 8 - 1 / xm m 11))
      ((14793707/22680 : ℝ) * (1 / xm 0 8)) := by
    simpa using (CdtTwoCore.hasSum_pair 8 (by norm_num)).mul_left (14793707/22680 : ℝ)
  have hp9 : HasSum (fun m : ℕ => (6561/56 : ℝ) * (1 / xm m 9 - 1 / xm m 12))
      ((6561/56 : ℝ) * (1 / xm 0 9)) := by
    simpa using (CdtTwoCore.hasSum_pair 9 (by norm_num)).mul_left (6561/56 : ℝ)
  have hp10 : HasSum (fun m : ℕ => (676387/420 : ℝ) * (1 / xm m 10 - 1 / xm m 13))
      ((676387/420 : ℝ) * (1 / xm 0 10)) := by
    simpa using (CdtTwoCore.hasSum_pair 10 (by norm_num)).mul_left (676387/420 : ℝ)
  have hp11 : HasSum (fun m : ℕ => (60921587/22680 : ℝ) * (1 / xm m 11 - 1 / xm m 14))
      ((60921587/22680 : ℝ) * (1 / xm 0 11)) := by
    simpa using (CdtTwoCore.hasSum_pair 11 (by norm_num)).mul_left (60921587/22680 : ℝ)
  have hp12 : HasSum (fun m : ℕ => (3588867/280 : ℝ) * (1 / xm m 12 - 1 / xm m 15))
      ((3588867/280 : ℝ) * (1 / xm 0 12)) := by
    simpa using (CdtTwoCore.hasSum_pair 12 (by norm_num)).mul_left (3588867/280 : ℝ)
  have hp13 : HasSum (fun m : ℕ => (27431057/2520 : ℝ) * (1 / xm m 13 - 1 / xm m 16))
      ((27431057/2520 : ℝ) * (1 / xm 0 13)) := by
    simpa using (CdtTwoCore.hasSum_pair 13 (by norm_num)).mul_left (27431057/2520 : ℝ)
  have hp14 : HasSum (fun m : ℕ => (29047273/3780 : ℝ) * (1 / xm m 14 - 1 / xm m 17))
      ((29047273/3780 : ℝ) * (1 / xm 0 14)) := by
    simpa using (CdtTwoCore.hasSum_pair 14 (by norm_num)).mul_left (29047273/3780 : ℝ)
  have hp15 : HasSum (fun m : ℕ => (951345/56 : ℝ) * (1 / xm m 15 - 1 / xm m 18))
      ((951345/56 : ℝ) * (1 / xm 0 15)) := by
    simpa using (CdtTwoCore.hasSum_pair 15 (by norm_num)).mul_left (951345/56 : ℝ)
  have hp16 : HasSum (fun m : ℕ => (4094689/360 : ℝ) * (1 / xm m 16 - 1 / xm m 19))
      ((4094689/360 : ℝ) * (1 / xm 0 16)) := by
    simpa using (CdtTwoCore.hasSum_pair 16 (by norm_num)).mul_left (4094689/360 : ℝ)
  have hp17 : HasSum (fun m : ℕ => (162408593/22680 : ℝ) * (1 / xm m 17 - 1 / xm m 20))
      ((162408593/22680 : ℝ) * (1 / xm 0 17)) := by
    simpa using (CdtTwoCore.hasSum_pair 17 (by norm_num)).mul_left (162408593/22680 : ℝ)
  have hp18 : HasSum (fun m : ℕ => (216513/28 : ℝ) * (1 / xm m 18 - 1 / xm m 21))
      ((216513/28 : ℝ) * (1 / xm 0 18)) := by
    simpa using (CdtTwoCore.hasSum_pair 18 (by norm_num)).mul_left (216513/28 : ℝ)
  have hp19 : HasSum (fun m : ℕ => (3804821/840 : ℝ) * (1 / xm m 19 - 1 / xm m 22))
      ((3804821/840 : ℝ) * (1 / xm 0 19)) := by
    simpa using (CdtTwoCore.hasSum_pair 19 (by norm_num)).mul_left (3804821/840 : ℝ)
  have hp20 : HasSum (fun m : ℕ => (7201325/648 : ℝ) * (1 / xm m 20 - 1 / xm m 23))
      ((7201325/648 : ℝ) * (1 / xm 0 20)) := by
    simpa using (CdtTwoCore.hasSum_pair 20 (by norm_num)).mul_left (7201325/648 : ℝ)
  have hp21 : HasSum (fun m : ℕ => (19683/2 : ℝ) * (1 / xm m 21 - 1 / xm m 24))
      ((19683/2 : ℝ) * (1 / xm 0 21)) := by
    simpa using (CdtTwoCore.hasSum_pair 21 (by norm_num)).mul_left (19683/2 : ℝ)
  have hp22 : HasSum (fun m : ℕ => (4676083/2520 : ℝ) * (1 / xm m 22 - 1 / xm m 25))
      ((4676083/2520 : ℝ) * (1 / xm 0 22)) := by
    simpa using (CdtTwoCore.hasSum_pair 22 (by norm_num)).mul_left (4676083/2520 : ℝ)
  have hp23 : HasSum (fun m : ℕ => (2701495/4536 : ℝ) * (1 / xm m 23 - 1 / xm m 26))
      ((2701495/4536 : ℝ) * (1 / xm 0 23)) := by
    simpa using (CdtTwoCore.hasSum_pair 23 (by norm_num)).mul_left (2701495/4536 : ℝ)
  exact
    (((((((((((((((((hp5.add hp6).sub hp7).add hp8).add hp9).add hp10).add hp11).sub hp12).add hp13).sub hp14).add hp15).sub hp16).sub hp17).add hp18).sub hp19).add hp20).sub hp21).add hp22).add hp23

/-- `HasSum` for the whole summand. -/
lemma hasSum_Vm4 : HasSum Vm4 Vval4 := by
  have hsum : HasSum (fun m : ℕ => W14 m + W24 m) Vval4 := by
    simpa [Vval4] using hasSum_W14.add hasSum_W24
  apply HasSum.congr_fun hsum
  intro m
  exact vm4_decomp m

/-- The infinite sum of `Vm4` in closed form. -/
lemma tsum_Vm4 : (∑' m : ℕ, Vm4 m) = 639 * A - 639 * B - 3993 / 8 := by
  have hval : Vval4 = 639 * A - 639 * B - 3993 / 8 := by
    unfold Vval4 V1val4 V2val4
    norm_num [xm]
    simp
    ring
  rw [hasSum_Vm4.tsum_eq]
  exact hval

end CdtFourCore
open CdtFourCore

theorem sum_cintegralFour_core :
    (∑' m : ℕ,
        (6561 : ℝ) * (Nat.choose (m + 8) 8 : ℝ) *
          (∑ i ∈ Finset.range 10,
            ((-1 : ℝ) ^ i * (Nat.choose 9 i : ℝ)) *
              (1944 / ((((3 * m + 5 + i : ℕ) : ℝ) * ((3 * m + 8 + i : ℕ) : ℝ) * ((3 * m + 11 + i : ℕ) : ℝ) * ((3 * m + 14 + i : ℕ) : ℝ) * ((3 * m + 17 + i : ℕ) : ℝ)))) ^ 2)) =
      639 * (∑' k : ℕ,
          ((1 : ℝ) / (((3 * k + 1 : ℕ) : ℝ) ^ 2) - (1 : ℝ) / (((3 * k + 2 : ℕ) : ℝ) ^ 2))) - 3993 / 8 := by
  have hMain := tsum_Vm4
  have hL : (∑' m : ℕ, Vm4 m) =
      (∑' m : ℕ,
        (6561 : ℝ) * (Nat.choose (m + 8) 8 : ℝ) *
          (∑ i ∈ Finset.range 10,
            ((-1 : ℝ) ^ i * (Nat.choose 9 i : ℝ)) *
              (1944 / ((((3 * m + 5 + i : ℕ) : ℝ) * ((3 * m + 8 + i : ℕ) : ℝ) * ((3 * m + 11 + i : ℕ) : ℝ) * ((3 * m + 14 + i : ℕ) : ℝ) * ((3 * m + 17 + i : ℕ) : ℝ)))) ^ 2)) := by
    apply tsum_congr
    intro m
    exact (vm4_eq_statement m).symm
  rw [← hL]
  rw [hMain]
  have hR : (∑' k : ℕ,
      ((1 : ℝ) / (((3 * k + 1 : ℕ) : ℝ) ^ 2) - (1 : ℝ) / (((3 * k + 2 : ℕ) : ℝ) ^ 2))) = A - B := by
    simpa [Rk, f1, f2, xm] using tsum_Rk
  rw [hR]
  ring

end Commons.Analysis.Summation
