import Mathlib
import Submission.Commons.Analysis.Summation.sum_cintegralFour_core

noncomputable section
open scoped BigOperators Nat
open Filter Topology

namespace Commons.Analysis.Summation
namespace CdtFiveCore

/-! ## Binomial `(m+10 choose 10)` as a degree-10 polynomial -/

lemma asc10 (n : ℕ) : n.ascFactorial 10 =
    n * (n + 1) * (n + 2) * (n + 3) * (n + 4) * (n + 5) * (n + 6) * (n + 7) * (n + 8) * (n + 9) := by
  simp [Nat.ascFactorial_succ, Nat.ascFactorial_zero]
  ring

lemma factorial_add_ten (m : ℕ) : (m + 10)! =
    m ! * (m + 1) * (m + 2) * (m + 3) * (m + 4) * (m + 5) * (m + 6) * (m + 7) * (m + 8) * (m + 9) * (m + 10) := by
  rw [← Nat.factorial_mul_ascFactorial m 10]
  have h := asc10 (m + 1)
  rw [h]
  ring

lemma choose210 (m : ℕ) :
    (Nat.choose (m + 10) 10 : ℝ) =
      (1 / 3628800 : ℝ) *
        (((m : ℝ) + 1) * ((m : ℝ) + 2) * ((m : ℝ) + 3) * ((m : ℝ) + 4) *
          ((m : ℝ) + 5) * ((m : ℝ) + 6) * ((m : ℝ) + 7) * ((m : ℝ) + 8) *
          ((m : ℝ) + 9) * ((m : ℝ) + 10)) := by
  have hcast := Nat.cast_choose ℝ (a := 10) (b := m + 10) (by omega : 10 ≤ m + 10)
  rw [hcast]
  have h10 : ((10 : ℕ)! : ℝ) = 3628800 := by norm_num
  have hsub : ((m + 10 - 10) : ℕ) = m := by omega
  rw [h10, hsub]
  have hfacR : ((m + 10)! : ℝ) = (m ! : ℝ) *
      (((m : ℝ) + 1) * ((m : ℝ) + 2) * ((m : ℝ) + 3) * ((m : ℝ) + 4) *
        ((m : ℝ) + 5) * ((m : ℝ) + 6) * ((m : ℝ) + 7) * ((m : ℝ) + 8) *
        ((m : ℝ) + 9) * ((m : ℝ) + 10)) := by
    norm_num [factorial_add_ten, Nat.cast_mul]
    ring
  rw [hfacR]
  have hm : (m ! : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_ne_zero m)
  field_simp [hm]

/-! ## Binomial coefficients `choose 11 i` -/
@[simp] lemma c11_0 : (Nat.choose 11 0 : ℝ) = 1 := by
  rw [Nat.cast_choose ℝ (by decide : 0 ≤ 11)]; norm_num
@[simp] lemma c11_1 : (Nat.choose 11 1 : ℝ) = 11 := by
  rw [Nat.cast_choose ℝ (by decide : 1 ≤ 11)]; norm_num
@[simp] lemma c11_2 : (Nat.choose 11 2 : ℝ) = 55 := by
  rw [Nat.cast_choose ℝ (by decide : 2 ≤ 11)]; norm_num
@[simp] lemma c11_3 : (Nat.choose 11 3 : ℝ) = 165 := by
  rw [Nat.cast_choose ℝ (by decide : 3 ≤ 11)]; norm_num
@[simp] lemma c11_4 : (Nat.choose 11 4 : ℝ) = 330 := by
  rw [Nat.cast_choose ℝ (by decide : 4 ≤ 11)]; norm_num
@[simp] lemma c11_5 : (Nat.choose 11 5 : ℝ) = 462 := by
  rw [Nat.cast_choose ℝ (by decide : 5 ≤ 11)]; norm_num
@[simp] lemma c11_6 : (Nat.choose 11 6 : ℝ) = 462 := by
  rw [Nat.cast_choose ℝ (by decide : 6 ≤ 11)]; norm_num
@[simp] lemma c11_7 : (Nat.choose 11 7 : ℝ) = 330 := by
  rw [Nat.cast_choose ℝ (by decide : 7 ≤ 11)]; norm_num
@[simp] lemma c11_8 : (Nat.choose 11 8 : ℝ) = 165 := by
  rw [Nat.cast_choose ℝ (by decide : 8 ≤ 11)]; norm_num
@[simp] lemma c11_9 : (Nat.choose 11 9 : ℝ) = 55 := by
  rw [Nat.cast_choose ℝ (by decide : 9 ≤ 11)]; norm_num
@[simp] lemma c11_10 : (Nat.choose 11 10 : ℝ) = 11 := by
  rw [Nat.cast_choose ℝ (by decide : 10 ≤ 11)]; norm_num
@[simp] lemma c11_11 : (Nat.choose 11 11 : ℝ) = 1 := by
  rw [Nat.cast_choose ℝ (by decide : 11 ≤ 11)]; norm_num

/-! ## The `m`-summand and its pointwise closed-form decomposition -/

/-- The `m`-summand of the five-core sum. -/
def Vm5 (m : ℕ) : ℝ :=
  (59049 : ℝ) * (Nat.choose (m + 10) 10 : ℝ) *
    (∑ i ∈ Finset.range 12,
      ((-1 : ℝ) ^ i * (Nat.choose 11 i : ℝ)) *
        (29160 / (xm m (6 + i) * xm m (9 + i) * xm m (12 + i) * xm m (15 + i) * xm m (18 + i) * xm m (21 + i))) ^ 2)

/-- Squared-term part of the closed-form decomposition. -/
def W15 (m : ℕ) : ℝ := (((((((((((((((((-94622 / 81 : ℝ) * (1 / (xm m 7)^2) + (298870 / 81 : ℝ) * (1 / (xm m 8)^2)) + (-143990 / 81 : ℝ) * (1 / (xm m 10)^2)) + (-1804088 / 81 : ℝ) * (1 / (xm m 11)^2)) + (8927380 / 81 : ℝ) * (1 / (xm m 13)^2)) + (-6732440 / 81 : ℝ) * (1 / (xm m 14)^2)) + (-2631629 / 9 : ℝ) * (1 / (xm m 16)^2)) + (4068064 / 9 : ℝ) * (1 / (xm m 17)^2)) + (-458150 : ℝ) * (1 / (xm m 20)^2)) + (5194904 / 9 : ℝ) * (1 / (xm m 22)^2)) + (-1426810 / 9 : ℝ) * (1 / (xm m 23)^2)) + (-37059880 / 81 : ℝ) * (1 / (xm m 25)^2)) + (30648926 / 81 : ℝ) * (1 / (xm m 26)^2)) + (1494350 / 81 : ℝ) * (1 / (xm m 28)^2)) + (-7827820 / 81 : ℝ) * (1 / (xm m 29)^2)) + (4184180 / 81 : ℝ) * (1 / (xm m 31)^2)) + (-1621477 / 81 : ℝ) * (1 / (xm m 32)^2))

/-- Telescoping-pair part of the closed-form decomposition. -/
def W25 (m : ℕ) : ℝ := ((((((((((((((((((((((((-2187 / 10 : ℝ) * (1 / xm m 6 - 1 / xm m 9) + (194642591 / 102060 : ℝ) * (1 / xm m 7 - 1 / xm m 10)) + (-74088487 / 40824 : ℝ) * (1 / xm m 8 - 1 / xm m 11)) + (-39366 / 5 : ℝ) * (1 / xm m 9 - 1 / xm m 12)) + (625176893 / 51030 : ℝ) * (1 / xm m 10 - 1 / xm m 13)) + (-2836851391 / 204120 : ℝ) * (1 / xm m 11 - 1 / xm m 14)) + (3024621 / 40 : ℝ) * (1 / xm m 12 - 1 / xm m 15)) + (-1030827677 / 8505 : ℝ) * (1 / xm m 13 - 1 / xm m 16)) + (1603265543 / 68040 : ℝ) * (1 / xm m 14 - 1 / xm m 17)) + (-282123 / 280 : ℝ) * (1 / xm m 15 - 1 / xm m 18)) + (14150740351 / 204120 : ℝ) * (1 / xm m 16 - 1 / xm m 19)) + (37078312741 / 204120 : ℝ) * (1 / xm m 17 - 1 / xm m 20)) + (-124285023 / 280 : ℝ) * (1 / xm m 18 - 1 / xm m 21)) + (55287836351 / 204120 : ℝ) * (1 / xm m 19 - 1 / xm m 22)) + (-47321886709 / 204120 : ℝ) * (1 / xm m 20 - 1 / xm m 23)) + (16527159 / 40 : ℝ) * (1 / xm m 21 - 1 / xm m 24)) + (-1803804761 / 9720 : ℝ) * (1 / xm m 22 - 1 / xm m 25)) + (-8926426133 / 68040 : ℝ) * (1 / xm m 23 - 1 / xm m 26)) + (457083 / 5 : ℝ) * (1 / xm m 24 - 1 / xm m 27)) + (-13018436321 / 204120 : ℝ) * (1 / xm m 25 - 1 / xm m 28)) + (30597514207 / 204120 : ℝ) * (1 / xm m 26 - 1 / xm m 29)) + (-216513 / 2 : ℝ) * (1 / xm m 27 - 1 / xm m 30)) + (213788641 / 14580 : ℝ) * (1 / xm m 28 - 1 / xm m 31)) + (1265220587 / 204120 : ℝ) * (1 / xm m 29 - 1 / xm m 32))

/-- The closed-form decomposition of the summand (as `W15 + W25`). -/
def Vd5 (m : ℕ) : ℝ := W15 m + W25 m

set_option maxHeartbeats 80000000 in
lemma vm5_decomp (m : ℕ) : Vm5 m = Vd5 m := by
  unfold Vm5 Vd5 W15 W25
  rw [choose210]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero,
    c11_0, c11_1, c11_2, c11_3, c11_4, c11_5, c11_6, c11_7, c11_8, c11_9, c11_10, c11_11]
  norm_num
  simp_rw [xm_eq]
  norm_num
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
  have h27 : (3 * (m : ℝ) + 27) ≠ 0 := by positivity
  have h28 : (3 * (m : ℝ) + 28) ≠ 0 := by positivity
  have h29 : (3 * (m : ℝ) + 29) ≠ 0 := by positivity
  have h30 : (3 * (m : ℝ) + 30) ≠ 0 := by positivity
  have h31 : (3 * (m : ℝ) + 31) ≠ 0 := by positivity
  have h32 : (3 * (m : ℝ) + 32) ≠ 0 := by positivity
  have hm1 : (m : ℝ) + 1 ≠ 0 := by positivity
  have hm2 : (m : ℝ) + 2 ≠ 0 := by positivity
  have hm3 : (m : ℝ) + 3 ≠ 0 := by positivity
  have hm4 : (m : ℝ) + 4 ≠ 0 := by positivity
  have hm5 : (m : ℝ) + 5 ≠ 0 := by positivity
  have hm6 : (m : ℝ) + 6 ≠ 0 := by positivity
  have hm7 : (m : ℝ) + 7 ≠ 0 := by positivity
  have hm8 : (m : ℝ) + 8 ≠ 0 := by positivity
  have hm9 : (m : ℝ) + 9 ≠ 0 := by positivity
  have hm10 : (m : ℝ) + 10 ≠ 0 := by positivity
  field_simp [h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10]
  ring

/-! ## The statement denominators equal the `xm` denominators -/

lemma denom_statement5 (m : ℕ) : ∀ i : ℕ,
    (((((3 * m + 6 + i : ℕ) : ℝ) * ((3 * m + 9 + i : ℕ) : ℝ) * ((3 * m + 12 + i : ℕ) : ℝ) * ((3 * m + 15 + i : ℕ) : ℝ) * ((3 * m + 18 + i : ℕ) : ℝ) * ((3 * m + 21 + i : ℕ) : ℝ))))
      = xm m (6 + i) * xm m (9 + i) * xm m (12 + i) * xm m (15 + i) * xm m (18 + i) * xm m (21 + i) := by
  intro i
  have h6 : (((3 * m + 6 + i : ℕ) : ℝ)) = xm m (6 + i) := by
    unfold xm
    congr 1
    omega
  have h9 : (((3 * m + 9 + i : ℕ) : ℝ)) = xm m (9 + i) := by
    unfold xm
    congr 1
    omega
  have h12 : (((3 * m + 12 + i : ℕ) : ℝ)) = xm m (12 + i) := by
    unfold xm
    congr 1
    omega
  have h15 : (((3 * m + 15 + i : ℕ) : ℝ)) = xm m (15 + i) := by
    unfold xm
    congr 1
    omega
  have h18 : (((3 * m + 18 + i : ℕ) : ℝ)) = xm m (18 + i) := by
    unfold xm
    congr 1
    omega
  have h21 : (((3 * m + 21 + i : ℕ) : ℝ)) = xm m (21 + i) := by
    unfold xm
    congr 1
    omega
  rw [h6, h9, h12, h15, h18, h21]

lemma inner_sum_statement5 (m : ℕ) :
    (∑ i ∈ Finset.range 12,
      ((-1 : ℝ) ^ i * (Nat.choose 11 i : ℝ)) * (29160 / ((((3 * m + 6 + i : ℕ) : ℝ) * ((3 * m + 9 + i : ℕ) : ℝ) * ((3 * m + 12 + i : ℕ) : ℝ) * ((3 * m + 15 + i : ℕ) : ℝ) * ((3 * m + 18 + i : ℕ) : ℝ) * ((3 * m + 21 + i : ℕ) : ℝ)))) ^ 2)
    = (∑ i ∈ Finset.range 12,
      ((-1 : ℝ) ^ i * (Nat.choose 11 i : ℝ)) * (29160 / (xm m (6 + i) * xm m (9 + i) * xm m (12 + i) * xm m (15 + i) * xm m (18 + i) * xm m (21 + i))) ^ 2) := by
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  rw [denom_statement5 m i]

lemma vm5_eq_statement (m : ℕ) :
    (59049 : ℝ) * (Nat.choose (m + 10) 10 : ℝ) *
      (∑ i ∈ Finset.range 12,
        ((-1 : ℝ) ^ i * (Nat.choose 11 i : ℝ)) * (29160 / ((((3 * m + 6 + i : ℕ) : ℝ) * ((3 * m + 9 + i : ℕ) : ℝ) * ((3 * m + 12 + i : ℕ) : ℝ) * ((3 * m + 15 + i : ℕ) : ℝ) * ((3 * m + 18 + i : ℕ) : ℝ) * ((3 * m + 21 + i : ℕ) : ℝ)))) ^ 2) =
      Vm5 m := by
  unfold Vm5
  rw [inner_sum_statement5 m]


/-! ## Small partial sums needed for the shifts -/

@[simp] lemma asum9 : Asum 9 = 64193725627641 / 57875577760000 := by norm_num [Asum, f1, xm]
@[simp] lemma asum10 : Asum 10 = 64267546517641 / 57875577760000 := by norm_num [Asum, f1, xm]
@[simp] lemma bsum9 : Bsum 9 = 80471258049933 / 245099063809600 := by norm_num [Bsum, f2, xm]
@[simp] lemma bsum10 : Bsum 10 = 67921427083803253 / 206128312663873600 := by norm_num [Bsum, f2, xm]

/-! ## The values of the two pieces -/

/-- The value of the `W15`-sum. -/
noncomputable def V1val5 : ℝ := (((((((((((((((((-94622 / 81 : ℝ) * (A - Asum 2) + (298870 / 81 : ℝ) * (B - Bsum 2)) + (-143990 / 81 : ℝ) * (A - Asum 3)) + (-1804088 / 81 : ℝ) * (B - Bsum 3)) + (8927380 / 81 : ℝ) * (A - Asum 4)) + (-6732440 / 81 : ℝ) * (B - Bsum 4)) + (-2631629 / 9 : ℝ) * (A - Asum 5)) + (4068064 / 9 : ℝ) * (B - Bsum 5)) + (-458150 : ℝ) * (B - Bsum 6)) + (5194904 / 9 : ℝ) * (A - Asum 7)) + (-1426810 / 9 : ℝ) * (B - Bsum 7)) + (-37059880 / 81 : ℝ) * (A - Asum 8)) + (30648926 / 81 : ℝ) * (B - Bsum 8)) + (1494350 / 81 : ℝ) * (A - Asum 9)) + (-7827820 / 81 : ℝ) * (B - Bsum 9)) + (4184180 / 81 : ℝ) * (A - Asum 10)) + (-1621477 / 81 : ℝ) * (B - Bsum 10))

/-- The value of the `W25`-sum. -/
noncomputable def V2val5 : ℝ := ((((((((((((((((((((((((-2187 / 10 : ℝ) * (1 / xm 0 6) + (194642591 / 102060 : ℝ) * (1 / xm 0 7)) + (-74088487 / 40824 : ℝ) * (1 / xm 0 8)) + (-39366 / 5 : ℝ) * (1 / xm 0 9)) + (625176893 / 51030 : ℝ) * (1 / xm 0 10)) + (-2836851391 / 204120 : ℝ) * (1 / xm 0 11)) + (3024621 / 40 : ℝ) * (1 / xm 0 12)) + (-1030827677 / 8505 : ℝ) * (1 / xm 0 13)) + (1603265543 / 68040 : ℝ) * (1 / xm 0 14)) + (-282123 / 280 : ℝ) * (1 / xm 0 15)) + (14150740351 / 204120 : ℝ) * (1 / xm 0 16)) + (37078312741 / 204120 : ℝ) * (1 / xm 0 17)) + (-124285023 / 280 : ℝ) * (1 / xm 0 18)) + (55287836351 / 204120 : ℝ) * (1 / xm 0 19)) + (-47321886709 / 204120 : ℝ) * (1 / xm 0 20)) + (16527159 / 40 : ℝ) * (1 / xm 0 21)) + (-1803804761 / 9720 : ℝ) * (1 / xm 0 22)) + (-8926426133 / 68040 : ℝ) * (1 / xm 0 23)) + (457083 / 5 : ℝ) * (1 / xm 0 24)) + (-13018436321 / 204120 : ℝ) * (1 / xm 0 25)) + (30597514207 / 204120 : ℝ) * (1 / xm 0 26)) + (-216513 / 2 : ℝ) * (1 / xm 0 27)) + (213788641 / 14580 : ℝ) * (1 / xm 0 28)) + (1265220587 / 204120 : ℝ) * (1 / xm 0 29))

/-- The value of the whole sum. -/
noncomputable def Vval5 : ℝ := V1val5 + V2val5

/-! ## `HasSum` of the two pieces of the decomposition -/

lemma hasSum_W15 : HasSum W15 V1val5 := by
  have h7 : HasSum (fun m : ℕ => (-94622 / 81 : ℝ) * (1 / (xm m 7)^2))
      ((-94622 / 81 : ℝ) * (A - Asum 2)) := by
    simpa using (CdtTwoCore.hasSum_sq1 2).mul_left (-94622 / 81 : ℝ)
  have h8 : HasSum (fun m : ℕ => (298870 / 81 : ℝ) * (1 / (xm m 8)^2))
      ((298870 / 81 : ℝ) * (B - Bsum 2)) := by
    simpa using (CdtTwoCore.hasSum_sq2 2).mul_left (298870 / 81 : ℝ)
  have h10 : HasSum (fun m : ℕ => (-143990 / 81 : ℝ) * (1 / (xm m 10)^2))
      ((-143990 / 81 : ℝ) * (A - Asum 3)) := by
    simpa using (CdtTwoCore.hasSum_sq1 3).mul_left (-143990 / 81 : ℝ)
  have h11 : HasSum (fun m : ℕ => (-1804088 / 81 : ℝ) * (1 / (xm m 11)^2))
      ((-1804088 / 81 : ℝ) * (B - Bsum 3)) := by
    simpa using (CdtTwoCore.hasSum_sq2 3).mul_left (-1804088 / 81 : ℝ)
  have h13 : HasSum (fun m : ℕ => (8927380 / 81 : ℝ) * (1 / (xm m 13)^2))
      ((8927380 / 81 : ℝ) * (A - Asum 4)) := by
    simpa using (CdtTwoCore.hasSum_sq1 4).mul_left (8927380 / 81 : ℝ)
  have h14 : HasSum (fun m : ℕ => (-6732440 / 81 : ℝ) * (1 / (xm m 14)^2))
      ((-6732440 / 81 : ℝ) * (B - Bsum 4)) := by
    simpa using (CdtTwoCore.hasSum_sq2 4).mul_left (-6732440 / 81 : ℝ)
  have h16 : HasSum (fun m : ℕ => (-2631629 / 9 : ℝ) * (1 / (xm m 16)^2))
      ((-2631629 / 9 : ℝ) * (A - Asum 5)) := by
    simpa using (CdtTwoCore.hasSum_sq1 5).mul_left (-2631629 / 9 : ℝ)
  have h17 : HasSum (fun m : ℕ => (4068064 / 9 : ℝ) * (1 / (xm m 17)^2))
      ((4068064 / 9 : ℝ) * (B - Bsum 5)) := by
    simpa using (CdtTwoCore.hasSum_sq2 5).mul_left (4068064 / 9 : ℝ)
  have h20 : HasSum (fun m : ℕ => (-458150 : ℝ) * (1 / (xm m 20)^2))
      ((-458150 : ℝ) * (B - Bsum 6)) := by
    simpa using (CdtTwoCore.hasSum_sq2 6).mul_left (-458150 : ℝ)
  have h22 : HasSum (fun m : ℕ => (5194904 / 9 : ℝ) * (1 / (xm m 22)^2))
      ((5194904 / 9 : ℝ) * (A - Asum 7)) := by
    simpa using (CdtTwoCore.hasSum_sq1 7).mul_left (5194904 / 9 : ℝ)
  have h23 : HasSum (fun m : ℕ => (-1426810 / 9 : ℝ) * (1 / (xm m 23)^2))
      ((-1426810 / 9 : ℝ) * (B - Bsum 7)) := by
    simpa using (CdtTwoCore.hasSum_sq2 7).mul_left (-1426810 / 9 : ℝ)
  have h25 : HasSum (fun m : ℕ => (-37059880 / 81 : ℝ) * (1 / (xm m 25)^2))
      ((-37059880 / 81 : ℝ) * (A - Asum 8)) := by
    simpa using (CdtTwoCore.hasSum_sq1 8).mul_left (-37059880 / 81 : ℝ)
  have h26 : HasSum (fun m : ℕ => (30648926 / 81 : ℝ) * (1 / (xm m 26)^2))
      ((30648926 / 81 : ℝ) * (B - Bsum 8)) := by
    simpa using (CdtTwoCore.hasSum_sq2 8).mul_left (30648926 / 81 : ℝ)
  have h28 : HasSum (fun m : ℕ => (1494350 / 81 : ℝ) * (1 / (xm m 28)^2))
      ((1494350 / 81 : ℝ) * (A - Asum 9)) := by
    simpa using (CdtTwoCore.hasSum_sq1 9).mul_left (1494350 / 81 : ℝ)
  have h29 : HasSum (fun m : ℕ => (-7827820 / 81 : ℝ) * (1 / (xm m 29)^2))
      ((-7827820 / 81 : ℝ) * (B - Bsum 9)) := by
    simpa using (CdtTwoCore.hasSum_sq2 9).mul_left (-7827820 / 81 : ℝ)
  have h31 : HasSum (fun m : ℕ => (4184180 / 81 : ℝ) * (1 / (xm m 31)^2))
      ((4184180 / 81 : ℝ) * (A - Asum 10)) := by
    simpa using (CdtTwoCore.hasSum_sq1 10).mul_left (4184180 / 81 : ℝ)
  have h32 : HasSum (fun m : ℕ => (-1621477 / 81 : ℝ) * (1 / (xm m 32)^2))
      ((-1621477 / 81 : ℝ) * (B - Bsum 10)) := by
    simpa using (CdtTwoCore.hasSum_sq2 10).mul_left (-1621477 / 81 : ℝ)
  exact ((((((((((((((((h7.add h8).add h10).add h11).add h13).add h14).add h16).add h17).add h20).add h22).add h23).add h25).add h26).add h28).add h29).add h31).add h32)

lemma hasSum_W25 : HasSum W25 V2val5 := by
  have hp6 : HasSum (fun m : ℕ => (-2187 / 10 : ℝ) * (1 / xm m 6 - 1 / xm m 9))
      ((-2187 / 10 : ℝ) * (1 / xm 0 6)) := by
    simpa using (CdtTwoCore.hasSum_pair 6 (by norm_num)).mul_left (-2187 / 10 : ℝ)
  have hp7 : HasSum (fun m : ℕ => (194642591 / 102060 : ℝ) * (1 / xm m 7 - 1 / xm m 10))
      ((194642591 / 102060 : ℝ) * (1 / xm 0 7)) := by
    simpa using (CdtTwoCore.hasSum_pair 7 (by norm_num)).mul_left (194642591 / 102060 : ℝ)
  have hp8 : HasSum (fun m : ℕ => (-74088487 / 40824 : ℝ) * (1 / xm m 8 - 1 / xm m 11))
      ((-74088487 / 40824 : ℝ) * (1 / xm 0 8)) := by
    simpa using (CdtTwoCore.hasSum_pair 8 (by norm_num)).mul_left (-74088487 / 40824 : ℝ)
  have hp9 : HasSum (fun m : ℕ => (-39366 / 5 : ℝ) * (1 / xm m 9 - 1 / xm m 12))
      ((-39366 / 5 : ℝ) * (1 / xm 0 9)) := by
    simpa using (CdtTwoCore.hasSum_pair 9 (by norm_num)).mul_left (-39366 / 5 : ℝ)
  have hp10 : HasSum (fun m : ℕ => (625176893 / 51030 : ℝ) * (1 / xm m 10 - 1 / xm m 13))
      ((625176893 / 51030 : ℝ) * (1 / xm 0 10)) := by
    simpa using (CdtTwoCore.hasSum_pair 10 (by norm_num)).mul_left (625176893 / 51030 : ℝ)
  have hp11 : HasSum (fun m : ℕ => (-2836851391 / 204120 : ℝ) * (1 / xm m 11 - 1 / xm m 14))
      ((-2836851391 / 204120 : ℝ) * (1 / xm 0 11)) := by
    simpa using (CdtTwoCore.hasSum_pair 11 (by norm_num)).mul_left (-2836851391 / 204120 : ℝ)
  have hp12 : HasSum (fun m : ℕ => (3024621 / 40 : ℝ) * (1 / xm m 12 - 1 / xm m 15))
      ((3024621 / 40 : ℝ) * (1 / xm 0 12)) := by
    simpa using (CdtTwoCore.hasSum_pair 12 (by norm_num)).mul_left (3024621 / 40 : ℝ)
  have hp13 : HasSum (fun m : ℕ => (-1030827677 / 8505 : ℝ) * (1 / xm m 13 - 1 / xm m 16))
      ((-1030827677 / 8505 : ℝ) * (1 / xm 0 13)) := by
    simpa using (CdtTwoCore.hasSum_pair 13 (by norm_num)).mul_left (-1030827677 / 8505 : ℝ)
  have hp14 : HasSum (fun m : ℕ => (1603265543 / 68040 : ℝ) * (1 / xm m 14 - 1 / xm m 17))
      ((1603265543 / 68040 : ℝ) * (1 / xm 0 14)) := by
    simpa using (CdtTwoCore.hasSum_pair 14 (by norm_num)).mul_left (1603265543 / 68040 : ℝ)
  have hp15 : HasSum (fun m : ℕ => (-282123 / 280 : ℝ) * (1 / xm m 15 - 1 / xm m 18))
      ((-282123 / 280 : ℝ) * (1 / xm 0 15)) := by
    simpa using (CdtTwoCore.hasSum_pair 15 (by norm_num)).mul_left (-282123 / 280 : ℝ)
  have hp16 : HasSum (fun m : ℕ => (14150740351 / 204120 : ℝ) * (1 / xm m 16 - 1 / xm m 19))
      ((14150740351 / 204120 : ℝ) * (1 / xm 0 16)) := by
    simpa using (CdtTwoCore.hasSum_pair 16 (by norm_num)).mul_left (14150740351 / 204120 : ℝ)
  have hp17 : HasSum (fun m : ℕ => (37078312741 / 204120 : ℝ) * (1 / xm m 17 - 1 / xm m 20))
      ((37078312741 / 204120 : ℝ) * (1 / xm 0 17)) := by
    simpa using (CdtTwoCore.hasSum_pair 17 (by norm_num)).mul_left (37078312741 / 204120 : ℝ)
  have hp18 : HasSum (fun m : ℕ => (-124285023 / 280 : ℝ) * (1 / xm m 18 - 1 / xm m 21))
      ((-124285023 / 280 : ℝ) * (1 / xm 0 18)) := by
    simpa using (CdtTwoCore.hasSum_pair 18 (by norm_num)).mul_left (-124285023 / 280 : ℝ)
  have hp19 : HasSum (fun m : ℕ => (55287836351 / 204120 : ℝ) * (1 / xm m 19 - 1 / xm m 22))
      ((55287836351 / 204120 : ℝ) * (1 / xm 0 19)) := by
    simpa using (CdtTwoCore.hasSum_pair 19 (by norm_num)).mul_left (55287836351 / 204120 : ℝ)
  have hp20 : HasSum (fun m : ℕ => (-47321886709 / 204120 : ℝ) * (1 / xm m 20 - 1 / xm m 23))
      ((-47321886709 / 204120 : ℝ) * (1 / xm 0 20)) := by
    simpa using (CdtTwoCore.hasSum_pair 20 (by norm_num)).mul_left (-47321886709 / 204120 : ℝ)
  have hp21 : HasSum (fun m : ℕ => (16527159 / 40 : ℝ) * (1 / xm m 21 - 1 / xm m 24))
      ((16527159 / 40 : ℝ) * (1 / xm 0 21)) := by
    simpa using (CdtTwoCore.hasSum_pair 21 (by norm_num)).mul_left (16527159 / 40 : ℝ)
  have hp22 : HasSum (fun m : ℕ => (-1803804761 / 9720 : ℝ) * (1 / xm m 22 - 1 / xm m 25))
      ((-1803804761 / 9720 : ℝ) * (1 / xm 0 22)) := by
    simpa using (CdtTwoCore.hasSum_pair 22 (by norm_num)).mul_left (-1803804761 / 9720 : ℝ)
  have hp23 : HasSum (fun m : ℕ => (-8926426133 / 68040 : ℝ) * (1 / xm m 23 - 1 / xm m 26))
      ((-8926426133 / 68040 : ℝ) * (1 / xm 0 23)) := by
    simpa using (CdtTwoCore.hasSum_pair 23 (by norm_num)).mul_left (-8926426133 / 68040 : ℝ)
  have hp24 : HasSum (fun m : ℕ => (457083 / 5 : ℝ) * (1 / xm m 24 - 1 / xm m 27))
      ((457083 / 5 : ℝ) * (1 / xm 0 24)) := by
    simpa using (CdtTwoCore.hasSum_pair 24 (by norm_num)).mul_left (457083 / 5 : ℝ)
  have hp25 : HasSum (fun m : ℕ => (-13018436321 / 204120 : ℝ) * (1 / xm m 25 - 1 / xm m 28))
      ((-13018436321 / 204120 : ℝ) * (1 / xm 0 25)) := by
    simpa using (CdtTwoCore.hasSum_pair 25 (by norm_num)).mul_left (-13018436321 / 204120 : ℝ)
  have hp26 : HasSum (fun m : ℕ => (30597514207 / 204120 : ℝ) * (1 / xm m 26 - 1 / xm m 29))
      ((30597514207 / 204120 : ℝ) * (1 / xm 0 26)) := by
    simpa using (CdtTwoCore.hasSum_pair 26 (by norm_num)).mul_left (30597514207 / 204120 : ℝ)
  have hp27 : HasSum (fun m : ℕ => (-216513 / 2 : ℝ) * (1 / xm m 27 - 1 / xm m 30))
      ((-216513 / 2 : ℝ) * (1 / xm 0 27)) := by
    simpa using (CdtTwoCore.hasSum_pair 27 (by norm_num)).mul_left (-216513 / 2 : ℝ)
  have hp28 : HasSum (fun m : ℕ => (213788641 / 14580 : ℝ) * (1 / xm m 28 - 1 / xm m 31))
      ((213788641 / 14580 : ℝ) * (1 / xm 0 28)) := by
    simpa using (CdtTwoCore.hasSum_pair 28 (by norm_num)).mul_left (213788641 / 14580 : ℝ)
  have hp29 : HasSum (fun m : ℕ => (1265220587 / 204120 : ℝ) * (1 / xm m 29 - 1 / xm m 32))
      ((1265220587 / 204120 : ℝ) * (1 / xm 0 29)) := by
    simpa using (CdtTwoCore.hasSum_pair 29 (by norm_num)).mul_left (1265220587 / 204120 : ℝ)
  exact (((((((((((((((((((((((hp6.add hp7).add hp8).add hp9).add hp10).add hp11).add hp12).add hp13).add hp14).add hp15).add hp16).add hp17).add hp18).add hp19).add hp20).add hp21).add hp22).add hp23).add hp24).add hp25).add hp26).add hp27).add hp28).add hp29)

/-- `HasSum` for the whole summand. -/
lemma hasSum_Vm5 : HasSum Vm5 Vval5 := by
  have hsum : HasSum (fun m : ℕ => W15 m + W25 m) Vval5 := by
    simpa [Vval5] using hasSum_W15.add hasSum_W25
  apply HasSum.congr_fun hsum
  intro m
  exact vm5_decomp m

set_option maxHeartbeats 80000000 in
/-- The infinite sum of `Vm5` in closed form. -/
lemma tsum_Vm5 : (∑' m : ℕ, Vm5 m) = 4653 * A - 4653 * B - 727059 / 200 := by
  have hval : Vval5 = 4653 * A - 4653 * B - 727059 / 200 := by
    unfold Vval5 V1val5 V2val5
    norm_num [xm]
    ring
  rw [hasSum_Vm5.tsum_eq]
  exact hval

end CdtFiveCore
open CdtFiveCore

/-- Creative-telescoping evaluation of the degree-5 `(Cintegral)` inner sum:
`Σₘ 59049·C(m+10,10)·Σᵢ₌₀¹¹(−1)ⁱC(11,i)·(29160/∏_{k=0}^{5}(3m+6+3k+i))²
 = 4653·Σₖ(1/(3k+1)²−1/(3k+2)²) − 727059/200`. -/
theorem sum_cintegralFive_core :
    (∑' m : ℕ,
        (59049 : ℝ) * (Nat.choose (m + 10) 10 : ℝ) *
          (∑ i ∈ Finset.range 12,
            ((-1 : ℝ) ^ i * (Nat.choose 11 i : ℝ)) *
              (29160 / ((((3 * m + 6 + i : ℕ) : ℝ) * ((3 * m + 9 + i : ℕ) : ℝ) * ((3 * m + 12 + i : ℕ) : ℝ) * ((3 * m + 15 + i : ℕ) : ℝ) * ((3 * m + 18 + i : ℕ) : ℝ) * ((3 * m + 21 + i : ℕ) : ℝ)))) ^ 2)) =
      4653 * (∑' k : ℕ,
          ((1 : ℝ) / (((3 * k + 1 : ℕ) : ℝ) ^ 2) - (1 : ℝ) / (((3 * k + 2 : ℕ) : ℝ) ^ 2))) - 727059 / 200 := by
  have hMain := tsum_Vm5
  have hL : (∑' m : ℕ, Vm5 m) =
      (∑' m : ℕ,
        (59049 : ℝ) * (Nat.choose (m + 10) 10 : ℝ) *
          (∑ i ∈ Finset.range 12,
            ((-1 : ℝ) ^ i * (Nat.choose 11 i : ℝ)) *
              (29160 / ((((3 * m + 6 + i : ℕ) : ℝ) * ((3 * m + 9 + i : ℕ) : ℝ) * ((3 * m + 12 + i : ℕ) : ℝ) * ((3 * m + 15 + i : ℕ) : ℝ) * ((3 * m + 18 + i : ℕ) : ℝ) * ((3 * m + 21 + i : ℕ) : ℝ)))) ^ 2)) := by
    apply tsum_congr
    intro m
    exact (vm5_eq_statement m).symm
  rw [← hL]
  rw [hMain]
  have hR : (∑' k : ℕ,
      ((1 : ℝ) / (((3 * k + 1 : ℕ) : ℝ) ^ 2) - (1 : ℝ) / (((3 * k + 2 : ℕ) : ℝ) ^ 2))) = A - B := by
    simpa [Rk, f1, f2, xm] using tsum_Rk
  rw [hR]
  ring

end Commons.Analysis.Summation
