import Mathlib
import Submission.Commons.Analysis.Summation.sum_cintegralOne_core
import Submission.Commons.Analysis.Summation.sum_cintegralTwo_core_corrected

noncomputable section
open scoped BigOperators Nat
open Filter Topology

namespace Commons.Analysis.Summation
namespace CdtThreeCore

/-! ## Binomial `(m+6 choose 6)` as a degree-6 polynomial -/

lemma asc6 (n : ℕ) : n.ascFactorial 6 = n * (n + 1) * (n + 2) * (n + 3) * (n + 4) * (n + 5) := by
  simp [Nat.ascFactorial_succ, Nat.ascFactorial_zero]
  ring

lemma factorial_add_six (m : ℕ) : (m + 6)! = m ! * (m + 1) * (m + 2) * (m + 3) * (m + 4) * (m + 5) * (m + 6) := by
  rw [← Nat.factorial_mul_ascFactorial m 6]
  have h := asc6 (m + 1)
  rw [h]
  ring

lemma choose36 (m : ℕ) :
    (Nat.choose (m + 6) 6 : ℝ) =
      (1 / 720 : ℝ) * (((m : ℝ) + 1) * ((m : ℝ) + 2) * ((m : ℝ) + 3) * ((m : ℝ) + 4) * ((m : ℝ) + 5) * ((m : ℝ) + 6)) := by
  have hcast := Nat.cast_choose ℝ (a := 6) (b := m + 6) (by omega : 6 ≤ m + 6)
  rw [hcast]
  have h6 : ((6 : ℕ)! : ℝ) = 720 := by norm_num
  have hsub : ((m + 6 - 6) : ℕ) = m := by omega
  rw [h6, hsub]
  have hfacR : ((m + 6)! : ℝ) = (m ! : ℝ) * (((m : ℝ) + 1) * ((m : ℝ) + 2) * ((m : ℝ) + 3) * ((m : ℝ) + 4) * ((m : ℝ) + 5) * ((m : ℝ) + 6)) := by
    norm_num [factorial_add_six, Nat.cast_mul]
    ring
  rw [hfacR]
  have hm : (m ! : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_ne_zero m)
  field_simp [hm]

/-! ## Binomial coefficients `choose 7 i` -/

@[simp] lemma c7_0 : (Nat.choose 7 0 : ℝ) = 1 := by
  rw [Nat.cast_choose ℝ (by decide : 0 ≤ 7)]; norm_num
@[simp] lemma c7_1 : (Nat.choose 7 1 : ℝ) = 7 := by
  rw [Nat.cast_choose ℝ (by decide : 1 ≤ 7)]; norm_num
@[simp] lemma c7_2 : (Nat.choose 7 2 : ℝ) = 21 := by
  rw [Nat.cast_choose ℝ (by decide : 2 ≤ 7)]; norm_num
@[simp] lemma c7_3 : (Nat.choose 7 3 : ℝ) = 35 := by
  rw [Nat.cast_choose ℝ (by decide : 3 ≤ 7)]; norm_num
@[simp] lemma c7_4 : (Nat.choose 7 4 : ℝ) = 35 := by
  rw [Nat.cast_choose ℝ (by decide : 4 ≤ 7)]; norm_num
@[simp] lemma c7_5 : (Nat.choose 7 5 : ℝ) = 21 := by
  rw [Nat.cast_choose ℝ (by decide : 5 ≤ 7)]; norm_num
@[simp] lemma c7_6 : (Nat.choose 7 6 : ℝ) = 7 := by
  rw [Nat.cast_choose ℝ (by decide : 6 ≤ 7)]; norm_num
@[simp] lemma c7_7 : (Nat.choose 7 7 : ℝ) = 1 := by
  rw [Nat.cast_choose ℝ (by decide : 7 ≤ 7)]; norm_num

/-! ## The summand and its closed-form decomposition -/

/-- The `m`-summand of the three-core sum. -/
def Vm3 (m : ℕ) : ℝ :=
  (729 : ℝ) * (Nat.choose (m + 6) 6 : ℝ) *
    (∑ i ∈ Finset.range 8,
      ((-1 : ℝ) ^ i * (Nat.choose 7 i : ℝ)) *
        (162 / (xm m (4 + i) * xm m (7 + i) * xm m (10 + i) * xm m (13 + i))) ^ 2)

/-- Squared-term part of the closed-form decomposition. -/
def W1 (m : ℕ) : ℝ :=
((((((((((((-154 / 9 : ℝ) * (1 / (xm m 4)^2) + (637 / 9 : ℝ) * (1 / (xm m 5)^2)) + (-1144 / 9 : ℝ) * (1 / (xm m 7)^2)) + (-980 / 9 : ℝ) * (1 / (xm m 8)^2)) + (8372 / 9 : ℝ) * (1 / (xm m 10)^2)) + (-7028 / 9 : ℝ) * (1 / (xm m 11)^2)) + (-8785 / 9 : ℝ) * (1 / (xm m 13)^2)) + (13156 / 9 : ℝ) * (1 / (xm m 14)^2)) + (-2548 / 9 : ℝ) * (1 / (xm m 16)^2)) + (-4004 / 9 : ℝ) * (1 / (xm m 17)^2)) + (5096 / 9 : ℝ) * (1 / (xm m 19)^2)) + (-2618 / 9 : ℝ) * (1 / (xm m 20)^2))

/-- Telescoping-pair part of the closed-form decomposition. -/
def W2 (m : ℕ) : ℝ :=
((((((((((((((34231 / 1620 : ℝ) * (1 / xm m 4 - 1 / xm m 7) + (418067 / 1620 : ℝ) * (1 / xm m 7 - 1 / xm m 10)) + (-11591 / 20 : ℝ) * (1 / xm m 10 - 1 / xm m 13)) + (-235613 / 810 : ℝ) * (1 / xm m 13 - 1 / xm m 16)) + (188069 / 810 : ℝ) * (1 / xm m 16 - 1 / xm m 19)) + (-17479 / 1620 : ℝ) * (1 / xm m 5 - 1 / xm m 8)) + (-294539 / 1620 : ℝ) * (1 / xm m 8 - 1 / xm m 11)) + (-4741 / 20 : ℝ) * (1 / xm m 11 - 1 / xm m 14)) + (1194733 / 1620 : ℝ) * (1 / xm m 14 - 1 / xm m 17)) + (82967 / 1620 : ℝ) * (1 / xm m 17 - 1 / xm m 20)) + (-1701 / 10 : ℝ) * (1 / xm m 6 - 1 / xm m 9)) + (5103 / 10 : ℝ) * (1 / xm m 9 - 1 / xm m 12)) + (5103 / 10 : ℝ) * (1 / xm m 12 - 1 / xm m 15)) + (-1701 / 2 : ℝ) * (1 / xm m 15 - 1 / xm m 18))

/-- The closed-form decomposition of the summand (as `W1 + W2`). -/
def Vd (m : ℕ) : ℝ := W1 m + W2 m

set_option maxHeartbeats 8000000 in
lemma vm_decomp (m : ℕ) : Vm3 m = Vd m := by
  unfold Vm3 Vd W1 W2
  rw [choose36]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, c7_0, c7_1, c7_2, c7_3, c7_4, c7_5, c7_6, c7_7]
  norm_num
  simp_rw [xm_eq]
  norm_num
  have h4 : (3 * (m : ℝ) + 4) ≠ 0 := by positivity
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
  field_simp [h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20]
  ring

/-! ## Small partial sums of the basic series -/

@[simp] lemma asum1 : Asum 1 = 1 := by norm_num [Asum, f1, xm]
@[simp] lemma asum2 : Asum 2 = 17 / 16 := by norm_num [Asum, f1, xm]
@[simp] lemma asum3 : Asum 3 = 849 / 784 := by norm_num [Asum, f1, xm]
@[simp] lemma asum4 : Asum 4 = 21421 / 19600 := by norm_num [Asum, f1, xm]
@[simp] lemma asum5 : Asum 5 = 3639749 / 3312400 := by norm_num [Asum, f1, xm]
@[simp] lemma asum6 : Asum 6 = 58443009 / 52998400 := by norm_num [Asum, f1, xm]
@[simp] lemma bsum1 : Bsum 1 = 1 / 4 := by norm_num [Bsum, f2, xm]
@[simp] lemma bsum2 : Bsum 2 = 29 / 100 := by norm_num [Bsum, f2, xm]
@[simp] lemma bsum3 : Bsum 3 = 489 / 1600 := by norm_num [Bsum, f2, xm]
@[simp] lemma bsum4 : Bsum 4 = 60769 / 193600 := by norm_num [Bsum, f2, xm]
@[simp] lemma bsum5 : Bsum 5 = 3026081 / 9486400 := by norm_num [Bsum, f2, xm]
@[simp] lemma bsum6 : Bsum 6 = 884023809 / 2741569600 := by norm_num [Bsum, f2, xm]

/-! ## The statement denominators equal the `xm` denominators -/

lemma denom_statement (m : ℕ) : ∀ i : ℕ,
    ((((3 * m + 4 + i : ℕ) : ℝ) * ((3 * m + 7 + i : ℕ) : ℝ) * ((3 * m + 10 + i : ℕ) : ℝ) * ((3 * m + 13 + i : ℕ) : ℝ)))
      = xm m (4 + i) * xm m (7 + i) * xm m (10 + i) * xm m (13 + i) := by
  intro i
  have hf1 : (((3 * m + 4 + i : ℕ) : ℝ)) = xm m (4 + i) := by
    unfold xm
    congr 1
    omega
  have hf2 : (((3 * m + 7 + i : ℕ) : ℝ)) = xm m (7 + i) := by
    unfold xm
    congr 1
    omega
  have hf3 : (((3 * m + 10 + i : ℕ) : ℝ)) = xm m (10 + i) := by
    unfold xm
    congr 1
    omega
  have hf4 : (((3 * m + 13 + i : ℕ) : ℝ)) = xm m (13 + i) := by
    unfold xm
    congr 1
    omega
  rw [hf1, hf2, hf3, hf4]

/-- The inner `i`-sum in the statement's form equals the `xm` form. -/
lemma inner_sum_statement (m : ℕ) :
    (∑ i ∈ Finset.range 8,
      ((-1 : ℝ) ^ i * (Nat.choose 7 i : ℝ)) *
        (162 / ((((3 * m + 4 + i : ℕ) : ℝ) * ((3 * m + 7 + i : ℕ) : ℝ) * ((3 * m + 10 + i : ℕ) : ℝ) * ((3 * m + 13 + i : ℕ) : ℝ)))) ^ 2)
    = (∑ i ∈ Finset.range 8,
      ((-1 : ℝ) ^ i * (Nat.choose 7 i : ℝ)) *
        (162 / (xm m (4 + i) * xm m (7 + i) * xm m (10 + i) * xm m (13 + i))) ^ 2) := by
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  rw [denom_statement m i]

/-- The `m`-summand of the three-core sum, in the statement's form. -/
lemma vm_eq_statement (m : ℕ) :
    (729 : ℝ) * (Nat.choose (m + 6) 6 : ℝ) *
      (∑ i ∈ Finset.range 8,
        ((-1 : ℝ) ^ i * (Nat.choose 7 i : ℝ)) *
          (162 / ((((3 * m + 4 + i : ℕ) : ℝ) * ((3 * m + 7 + i : ℕ) : ℝ) * ((3 * m + 10 + i : ℕ) : ℝ) * ((3 * m + 13 + i : ℕ) : ℝ)))) ^ 2) =
      Vm3 m := by
  unfold Vm3
  rw [inner_sum_statement m]

/-! ## The values of the two pieces -/

/-- The value of the `W1`-sum (before simplifying the small partial sums). -/
noncomputable def V1val : ℝ :=
((((((((((((-154 / 9 : ℝ) * (A - Asum 1) + (637 / 9 : ℝ) * (B - Bsum 1)) + (-1144 / 9 : ℝ) * (A - Asum 2)) + (-980 / 9 : ℝ) * (B - Bsum 2)) + (8372 / 9 : ℝ) * (A - Asum 3)) + (-7028 / 9 : ℝ) * (B - Bsum 3)) + (-8785 / 9 : ℝ) * (A - Asum 4)) + (13156 / 9 : ℝ) * (B - Bsum 4)) + (-2548 / 9 : ℝ) * (A - Asum 5)) + (-4004 / 9 : ℝ) * (B - Bsum 5)) + (5096 / 9 : ℝ) * (A - Asum 6)) + (-2618 / 9 : ℝ) * (B - Bsum 6))

/-- The value of the `W2`-sum. -/
noncomputable def V2val : ℝ :=
((((((((((((((34231 / 1620 : ℝ) * (1 / xm 0 4) + (418067 / 1620 : ℝ) * (1 / xm 0 7)) + (-11591 / 20 : ℝ) * (1 / xm 0 10)) + (-235613 / 810 : ℝ) * (1 / xm 0 13)) + (188069 / 810 : ℝ) * (1 / xm 0 16)) + (-17479 / 1620 : ℝ) * (1 / xm 0 5)) + (-294539 / 1620 : ℝ) * (1 / xm 0 8)) + (-4741 / 20 : ℝ) * (1 / xm 0 11)) + (1194733 / 1620 : ℝ) * (1 / xm 0 14)) + (82967 / 1620 : ℝ) * (1 / xm 0 17)) + (-1701 / 10 : ℝ) * (1 / xm 0 6)) + (5103 / 10 : ℝ) * (1 / xm 0 9)) + (5103 / 10 : ℝ) * (1 / xm 0 12)) + (-1701 / 2 : ℝ) * (1 / xm 0 15))

/-- The value of the whole sum. -/
noncomputable def Vval : ℝ := V1val + V2val

/-! ## `HasSum` of the two pieces of the decomposition -/

open CdtTwoCore

lemma hasSum_W1 : HasSum W1 V1val := by
  have hT4 : HasSum (fun m : ℕ => (-154 / 9 : ℝ) * (1 / (xm m 4)^2))
      ((-154 / 9 : ℝ) * (A - Asum 1)) := by
    simpa using (hasSum_sq1 1).mul_left (-154 / 9 : ℝ)
  have hT5 : HasSum (fun m : ℕ => (637 / 9 : ℝ) * (1 / (xm m 5)^2))
      ((637 / 9 : ℝ) * (B - Bsum 1)) := by
    simpa using (hasSum_sq2 1).mul_left (637 / 9 : ℝ)
  have hT7 : HasSum (fun m : ℕ => (-1144 / 9 : ℝ) * (1 / (xm m 7)^2))
      ((-1144 / 9 : ℝ) * (A - Asum 2)) := by
    simpa using (hasSum_sq1 2).mul_left (-1144 / 9 : ℝ)
  have hT8 : HasSum (fun m : ℕ => (-980 / 9 : ℝ) * (1 / (xm m 8)^2))
      ((-980 / 9 : ℝ) * (B - Bsum 2)) := by
    simpa using (hasSum_sq2 2).mul_left (-980 / 9 : ℝ)
  have hT10 : HasSum (fun m : ℕ => (8372 / 9 : ℝ) * (1 / (xm m 10)^2))
      ((8372 / 9 : ℝ) * (A - Asum 3)) := by
    simpa using (hasSum_sq1 3).mul_left (8372 / 9 : ℝ)
  have hT11 : HasSum (fun m : ℕ => (-7028 / 9 : ℝ) * (1 / (xm m 11)^2))
      ((-7028 / 9 : ℝ) * (B - Bsum 3)) := by
    simpa using (hasSum_sq2 3).mul_left (-7028 / 9 : ℝ)
  have hT13 : HasSum (fun m : ℕ => (-8785 / 9 : ℝ) * (1 / (xm m 13)^2))
      ((-8785 / 9 : ℝ) * (A - Asum 4)) := by
    simpa using (hasSum_sq1 4).mul_left (-8785 / 9 : ℝ)
  have hT14 : HasSum (fun m : ℕ => (13156 / 9 : ℝ) * (1 / (xm m 14)^2))
      ((13156 / 9 : ℝ) * (B - Bsum 4)) := by
    simpa using (hasSum_sq2 4).mul_left (13156 / 9 : ℝ)
  have hT16 : HasSum (fun m : ℕ => (-2548 / 9 : ℝ) * (1 / (xm m 16)^2))
      ((-2548 / 9 : ℝ) * (A - Asum 5)) := by
    simpa using (hasSum_sq1 5).mul_left (-2548 / 9 : ℝ)
  have hT17 : HasSum (fun m : ℕ => (-4004 / 9 : ℝ) * (1 / (xm m 17)^2))
      ((-4004 / 9 : ℝ) * (B - Bsum 5)) := by
    simpa using (hasSum_sq2 5).mul_left (-4004 / 9 : ℝ)
  have hT19 : HasSum (fun m : ℕ => (5096 / 9 : ℝ) * (1 / (xm m 19)^2))
      ((5096 / 9 : ℝ) * (A - Asum 6)) := by
    simpa using (hasSum_sq1 6).mul_left (5096 / 9 : ℝ)
  have hT20 : HasSum (fun m : ℕ => (-2618 / 9 : ℝ) * (1 / (xm m 20)^2))
      ((-2618 / 9 : ℝ) * (B - Bsum 6)) := by
    simpa using (hasSum_sq2 6).mul_left (-2618 / 9 : ℝ)
  exact
(((((((((((hT4.add hT5).add hT7).add hT8).add hT10).add hT11).add hT13).add hT14).add hT16).add hT17).add hT19).add hT20)

lemma hasSum_W2 : HasSum W2 V2val := by
  have hp4 : HasSum (fun m : ℕ => (34231 / 1620 : ℝ) * (1 / xm m 4 - 1 / xm m 7))
      ((34231 / 1620 : ℝ) * (1 / xm 0 4)) := by
    simpa using (hasSum_pair 4 (by norm_num)).mul_left (34231 / 1620 : ℝ)
  have hp7 : HasSum (fun m : ℕ => (418067 / 1620 : ℝ) * (1 / xm m 7 - 1 / xm m 10))
      ((418067 / 1620 : ℝ) * (1 / xm 0 7)) := by
    simpa using (hasSum_pair 7 (by norm_num)).mul_left (418067 / 1620 : ℝ)
  have hp10 : HasSum (fun m : ℕ => (-11591 / 20 : ℝ) * (1 / xm m 10 - 1 / xm m 13))
      ((-11591 / 20 : ℝ) * (1 / xm 0 10)) := by
    simpa using (hasSum_pair 10 (by norm_num)).mul_left (-11591 / 20 : ℝ)
  have hp13 : HasSum (fun m : ℕ => (-235613 / 810 : ℝ) * (1 / xm m 13 - 1 / xm m 16))
      ((-235613 / 810 : ℝ) * (1 / xm 0 13)) := by
    simpa using (hasSum_pair 13 (by norm_num)).mul_left (-235613 / 810 : ℝ)
  have hp16 : HasSum (fun m : ℕ => (188069 / 810 : ℝ) * (1 / xm m 16 - 1 / xm m 19))
      ((188069 / 810 : ℝ) * (1 / xm 0 16)) := by
    simpa using (hasSum_pair 16 (by norm_num)).mul_left (188069 / 810 : ℝ)
  have hp5 : HasSum (fun m : ℕ => (-17479 / 1620 : ℝ) * (1 / xm m 5 - 1 / xm m 8))
      ((-17479 / 1620 : ℝ) * (1 / xm 0 5)) := by
    simpa using (hasSum_pair 5 (by norm_num)).mul_left (-17479 / 1620 : ℝ)
  have hp8 : HasSum (fun m : ℕ => (-294539 / 1620 : ℝ) * (1 / xm m 8 - 1 / xm m 11))
      ((-294539 / 1620 : ℝ) * (1 / xm 0 8)) := by
    simpa using (hasSum_pair 8 (by norm_num)).mul_left (-294539 / 1620 : ℝ)
  have hp11 : HasSum (fun m : ℕ => (-4741 / 20 : ℝ) * (1 / xm m 11 - 1 / xm m 14))
      ((-4741 / 20 : ℝ) * (1 / xm 0 11)) := by
    simpa using (hasSum_pair 11 (by norm_num)).mul_left (-4741 / 20 : ℝ)
  have hp14 : HasSum (fun m : ℕ => (1194733 / 1620 : ℝ) * (1 / xm m 14 - 1 / xm m 17))
      ((1194733 / 1620 : ℝ) * (1 / xm 0 14)) := by
    simpa using (hasSum_pair 14 (by norm_num)).mul_left (1194733 / 1620 : ℝ)
  have hp17 : HasSum (fun m : ℕ => (82967 / 1620 : ℝ) * (1 / xm m 17 - 1 / xm m 20))
      ((82967 / 1620 : ℝ) * (1 / xm 0 17)) := by
    simpa using (hasSum_pair 17 (by norm_num)).mul_left (82967 / 1620 : ℝ)
  have hp6 : HasSum (fun m : ℕ => (-1701 / 10 : ℝ) * (1 / xm m 6 - 1 / xm m 9))
      ((-1701 / 10 : ℝ) * (1 / xm 0 6)) := by
    simpa using (hasSum_pair 6 (by norm_num)).mul_left (-1701 / 10 : ℝ)
  have hp9 : HasSum (fun m : ℕ => (5103 / 10 : ℝ) * (1 / xm m 9 - 1 / xm m 12))
      ((5103 / 10 : ℝ) * (1 / xm 0 9)) := by
    simpa using (hasSum_pair 9 (by norm_num)).mul_left (5103 / 10 : ℝ)
  have hp12 : HasSum (fun m : ℕ => (5103 / 10 : ℝ) * (1 / xm m 12 - 1 / xm m 15))
      ((5103 / 10 : ℝ) * (1 / xm 0 12)) := by
    simpa using (hasSum_pair 12 (by norm_num)).mul_left (5103 / 10 : ℝ)
  have hp15 : HasSum (fun m : ℕ => (-1701 / 2 : ℝ) * (1 / xm m 15 - 1 / xm m 18))
      ((-1701 / 2 : ℝ) * (1 / xm 0 15)) := by
    simpa using (hasSum_pair 15 (by norm_num)).mul_left (-1701 / 2 : ℝ)
  exact
(((((((((((((hp4.add hp7).add hp10).add hp13).add hp16).add hp5).add hp8).add hp11).add hp14).add hp17).add hp6).add hp9).add hp12).add hp15)

/-- `HasSum` for the whole summand. -/
lemma hasSum_Vm : HasSum Vm3 Vval := by
  have hsum : HasSum (fun m : ℕ => W1 m + W2 m) Vval := by
    simpa [Vval] using hasSum_W1.add hasSum_W2
  apply HasSum.congr_fun hsum
  intro m
  exact vm_decomp m

set_option maxHeartbeats 8000000 in
/-- The infinite sum of `Vm3` in closed form. -/
lemma tsum_Vm : (∑' m : ℕ, Vm3 m) = 93 * A - 93 * B - 145 / 2 := by
  have hval : Vval = 93 * A - 93 * B - 145 / 2 := by
    unfold Vval V1val V2val
    norm_num [xm]
    simp
    ring
  rw [hasSum_Vm.tsum_eq]
  exact hval

end CdtThreeCore
open CdtThreeCore

theorem sum_cintegralThree_core :
    (∑' m : ℕ,
        (729 : ℝ) * (Nat.choose (m + 6) 6 : ℝ) *
          (∑ i ∈ Finset.range 8,
            ((-1 : ℝ) ^ i * (Nat.choose 7 i : ℝ)) *
              (162 / ((((3 * m + 4 + i : ℕ) : ℝ) * ((3 * m + 7 + i : ℕ) : ℝ) * ((3 * m + 10 + i : ℕ) : ℝ) * ((3 * m + 13 + i : ℕ) : ℝ)))) ^ 2)) =
      93 * (∑' k : ℕ,
          ((1 : ℝ) / (((3 * k + 1 : ℕ) : ℝ) ^ 2) - (1 : ℝ) / (((3 * k + 2 : ℕ) : ℝ) ^ 2))) - 145 / 2 := by
  have hMain := tsum_Vm
  have hL : (∑' m : ℕ, Vm3 m) =
      (∑' m : ℕ,
        (729 : ℝ) * (Nat.choose (m + 6) 6 : ℝ) *
          (∑ i ∈ Finset.range 8,
            ((-1 : ℝ) ^ i * (Nat.choose 7 i : ℝ)) *
              (162 / ((((3 * m + 4 + i : ℕ) : ℝ) * ((3 * m + 7 + i : ℕ) : ℝ) * ((3 * m + 10 + i : ℕ) : ℝ) * ((3 * m + 13 + i : ℕ) : ℝ)))) ^ 2)) := by
    apply tsum_congr
    intro m
    exact (vm_eq_statement m).symm
  rw [← hL]
  rw [hMain]
  have hR : (∑' k : ℕ,
      ((1 : ℝ) / (((3 * k + 1 : ℕ) : ℝ) ^ 2) - (1 : ℝ) / (((3 * k + 2 : ℕ) : ℝ) ^ 2))) = A - B := by
    simpa [Rk, f1, f2, xm] using tsum_Rk
  rw [hR]
  ring

end Commons.Analysis.Summation

