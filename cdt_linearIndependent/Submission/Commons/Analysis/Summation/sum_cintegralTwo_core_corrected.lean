import Mathlib.Data.Nat.Choose.Cast
import Submission.Commons.Analysis.Summation.sum_cintegralOne_core

noncomputable section
open scoped BigOperators Nat
open Filter Topology

namespace Commons.Analysis.Summation
namespace CdtTwoCore

lemma asc4 (n : ℕ) : n.ascFactorial 4 = n * (n + 1) * (n + 2) * (n + 3) := by
  simp [Nat.ascFactorial_succ, Nat.ascFactorial_zero]
  ring

lemma factorial_add_four (m : ℕ) : (m + 4)! = m ! * (m + 1) * (m + 2) * (m + 3) * (m + 4) := by
  rw [← Nat.factorial_mul_ascFactorial m 4]
  have h := asc4 (m + 1)
  rw [h]
  ring

lemma choose24 (m : ℕ) :
    (Nat.choose (m + 4) 4 : ℝ) =
      (1 / 24 : ℝ) * (((m : ℝ) + 1) * ((m : ℝ) + 2) * ((m : ℝ) + 3) * ((m : ℝ) + 4)) := by
  have hcast := Nat.cast_choose ℝ (a := 4) (b := m + 4) (by omega : 4 ≤ m + 4)
  rw [hcast]
  have h4 : ((4 : ℕ)! : ℝ) = 24 := by norm_num
  have hsub : ((m + 4 - 4) : ℕ) = m := by omega
  rw [h4, hsub]
  have hfacR : ((m + 4)! : ℝ) = (m ! : ℝ) * (((m : ℝ) + 1) * ((m : ℝ) + 2) * ((m : ℝ) + 3) * ((m : ℝ) + 4)) := by
    norm_num [factorial_add_four, Nat.cast_mul]
    ring
  rw [hfacR]
  have hm : (m ! : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_ne_zero m)
  field_simp [hm]

@[simp] lemma c5_0 : (Nat.choose 5 0 : ℝ) = 1 := by
  rw [Nat.cast_choose ℝ (by decide : 0 ≤ 5)]; norm_num
@[simp] lemma c5_1 : (Nat.choose 5 1 : ℝ) = 5 := by
  rw [Nat.cast_choose ℝ (by decide : 1 ≤ 5)]; norm_num
@[simp] lemma c5_2 : (Nat.choose 5 2 : ℝ) = 10 := by
  rw [Nat.cast_choose ℝ (by decide : 2 ≤ 5)]; norm_num
@[simp] lemma c5_3 : (Nat.choose 5 3 : ℝ) = 10 := by
  rw [Nat.cast_choose ℝ (by decide : 3 ≤ 5)]; norm_num
@[simp] lemma c5_4 : (Nat.choose 5 4 : ℝ) = 5 := by
  rw [Nat.cast_choose ℝ (by decide : 4 ≤ 5)]; norm_num
@[simp] lemma c5_5 : (Nat.choose 5 5 : ℝ) = 1 := by
  rw [Nat.cast_choose ℝ (by decide : 5 ≤ 5)]; norm_num

/-- The `m`-summand of the corrected two-core sum. -/
def Vm (m : ℕ) : ℝ :=
  (81 : ℝ) * (Nat.choose (m + 4) 4 : ℝ) *
    (∑ i ∈ Finset.range 6,
      ((-1 : ℝ) ^ i * (Nat.choose 5 i : ℝ)) *
        (18 / (xm m (3 + i) * xm m (6 + i) * xm m (9 + i))) ^ 2)

/-- Squared-term part of the closed-form decomposition. -/
def W1 (m : ℕ) : ℝ :=
  (50/3 : ℝ) * (1 / (xm m 4)^2) - (70/3 : ℝ) * (1 / (xm m 5)^2) - (25 : ℝ) * (1 / (xm m 7)^2)
    + (65 : ℝ) * (1 / (xm m 8)^2) - (35 : ℝ) * (1 / (xm m 10)^2) - (20 : ℝ) * (1 / (xm m 11)^2)
    + (175/3 : ℝ) * (1 / (xm m 13)^2) - (110/3 : ℝ) * (1 / (xm m 14)^2)

/-- Telescoping-pair part of the closed-form decomposition. -/
def W2 (m : ℕ) : ℝ :=
  (27/4 : ℝ) * (1 / xm m 3 - 1 / xm m 6)
    + (81/4 : ℝ) * (1 / xm m 6 - 1 / xm m 9)
    - (135/2 : ℝ) * (1 / xm m 9 - 1 / xm m 12)
    - (235/12 : ℝ) * (1 / xm m 4 - 1 / xm m 7)
    - (85/6 : ℝ) * (1 / xm m 7 - 1 / xm m 10)
    + (115/4 : ℝ) * (1 / xm m 10 - 1 / xm m 13)
    + (5/2 : ℝ) * (1 / xm m 5 - 1 / xm m 8)
    + (479/12 : ℝ) * (1 / xm m 8 - 1 / xm m 11)
    + (37/12 : ℝ) * (1 / xm m 11 - 1 / xm m 14)

/-- The closed-form decomposition of the summand (as `W1 + W2`). -/
def Vd (m : ℕ) : ℝ := W1 m + W2 m

set_option maxHeartbeats 6000000 in
lemma vm_decomp (m : ℕ) : Vm m = Vd m := by
  unfold Vm Vd W1 W2
  rw [choose24]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, c5_0, c5_1, c5_2, c5_3, c5_4, c5_5]
  norm_num
  simp_rw [xm_eq]
  norm_num
  have h3 : (3 * (m : ℝ) + 3) ≠ 0 := by positivity
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
  have hm1 : (m : ℝ) + 1 ≠ 0 := by positivity
  have hm2 : (m : ℝ) + 2 ≠ 0 := by positivity
  have hm3 : (m : ℝ) + 3 ≠ 0 := by positivity
  have hm4 : (m : ℝ) + 4 ≠ 0 := by positivity
  field_simp
  ring


/-! ## Summability and `HasSum` of the building blocks -/

lemma xm_shift1 (m s : ℕ) : xm m (3 * s + 1) = xm (m + s) 1 := by
  unfold xm
  congr 1
  omega

lemma xm_shift2 (m s : ℕ) : xm m (3 * s + 2) = xm (m + s) 2 := by
  unfold xm
  congr 1
  omega

lemma summable_sq (j : ℕ) (hj : 1 ≤ j) :
    Summable (fun m : ℕ => (1 : ℝ) / (xm m j)^2) := by
  refine Summable.of_nonneg_of_le (fun m => ?_) (fun m => ?_) summable_one_div_succ_sq
  · positivity
  · have hx : 0 < xm m j := xm_pos hj
    have hn : 0 < (m : ℝ) + 1 := by positivity
    have hge : (m : ℝ) + 1 ≤ xm m j := xm_ge_succ hj
    have hge2 : ((m : ℝ) + 1)^2 ≤ (xm m j)^2 := by nlinarith
    exact one_div_le_one_div_of_le (by positivity : 0 < ((m : ℝ) + 1)^2) hge2

lemma tsum_shift (f : ℕ → ℝ) (k : ℕ) (hf : Summable f) :
    (∑' n : ℕ, f (n + k)) = (∑' n : ℕ, f n) - ∑ i ∈ Finset.range k, f i := by
  let S : ℝ := ∑ i ∈ Finset.range k, f i
  have hg : HasSum f ((∑' n : ℕ, f n) - S + S) := by
    have h : (∑' n : ℕ, f n) - S + S = (∑' n : ℕ, f n) := by ring
    simpa [h] using hf.hasSum
  have hs := (hasSum_nat_add_iff (f := f) k).2 hg
  exact hs.tsum_eq

lemma hasSum_sq1 (s : ℕ) :
    HasSum (fun m : ℕ => (1 : ℝ) / (xm m (3 * s + 1))^2) (A - Asum s) := by
  have hsh : Summable (fun m : ℕ => f1 (m + s)) := by
    exact ((summable_nat_add_iff (G := ℝ) (f := f1) s).mpr summable_f1)
  have hv : (∑' m : ℕ, f1 (m + s)) = A - Asum s := by
    calc
      (∑' m : ℕ, f1 (m + s)) = (∑' n : ℕ, f1 n) - ∑ i ∈ Finset.range s, f1 i :=
        tsum_shift f1 s summable_f1
      _ = A - Asum s := by rfl
  have hh : HasSum (fun m : ℕ => (1 : ℝ) / (xm m (3 * s + 1))^2) (∑' m : ℕ, f1 (m + s)) := by
    apply HasSum.congr_fun hsh.hasSum
    intro m
    unfold f1
    rw [xm_shift1 m s]
  rw [← hv]
  exact hh

lemma hasSum_sq2 (s : ℕ) :
    HasSum (fun m : ℕ => (1 : ℝ) / (xm m (3 * s + 2))^2) (B - Bsum s) := by
  have hsh : Summable (fun m : ℕ => f2 (m + s)) := by
    exact ((summable_nat_add_iff (G := ℝ) (f := f2) s).mpr summable_f2)
  have hv : (∑' m : ℕ, f2 (m + s)) = B - Bsum s := by
    calc
      (∑' m : ℕ, f2 (m + s)) = (∑' n : ℕ, f2 n) - ∑ i ∈ Finset.range s, f2 i :=
        tsum_shift f2 s summable_f2
      _ = B - Bsum s := by rfl
  have hh : HasSum (fun m : ℕ => (1 : ℝ) / (xm m (3 * s + 2))^2) (∑' m : ℕ, f2 (m + s)) := by
    apply HasSum.congr_fun hsh.hasSum
    intro m
    unfold f2
    rw [xm_shift2 m s]
  rw [← hv]
  exact hh

lemma hasSum_pair (a : ℕ) (ha : 1 ≤ a) :
    HasSum (fun m : ℕ => 1 / xm m a - 1 / xm m (a + 3)) (1 / xm 0 a) := by
  let f : ℕ → ℝ := fun m => 1 / xm m a
  have hpair : ∀ m : ℕ, 1 / xm m a - 1 / xm m (a + 3) = f m - f (m + 1) := by
    intro m
    unfold f
    rw [xm_succ]
  have htel : ∀ M : ℕ,
      (∑ m ∈ Finset.range M, (1 / xm m a - 1 / xm m (a + 3))) = 1 / xm 0 a - 1 / xm M a := by
    intro M
    calc
      (∑ m ∈ Finset.range M, (1 / xm m a - 1 / xm m (a + 3)))
          = ∑ m ∈ Finset.range M, (f m - f (m + 1)) := by
            apply Finset.sum_congr rfl
            intro m hm
            exact hpair m
      _ = f 0 - f M := Finset.sum_range_sub' f M
      _ = 1 / xm 0 a - 1 / xm M a := by rfl
  have hmono : ∀ m : ℕ, 0 ≤ 1 / xm m a - 1 / xm m (a + 3) := by
    intro m
    have h1 : 0 < xm m a := xm_pos ha
    have h2 : 0 < xm (m + 1) a := xm_pos ha
    have hle1 : xm m a ≤ xm (m + 1) a := by
      rw [xm_eq, xm_eq]
      norm_num
    have hle : (1 : ℝ) / xm (m + 1) a ≤ 1 / xm m a :=
      one_div_le_one_div_of_le h1 hle1
    have hpos : 0 ≤ 1 / xm m a := by positivity
    rw [hpair m]
    unfold f
    exact sub_nonneg.mpr hle
  have htend : Tendsto (fun M : ℕ => 1 / xm 0 a - 1 / xm M a) atTop (𝓝 (1 / xm 0 a)) := by
    have hz : Tendsto (fun M : ℕ => 1 / xm M a) atTop (𝓝 0) := tendsto_inv_xm_zero ha
    simpa using (tendsto_const_nhds.sub hz)
  have hsumT : Tendsto (fun M : ℕ =>
      ∑ m ∈ Finset.range M, (1 / xm m a - 1 / xm m (a + 3))) atTop (𝓝 (1 / xm 0 a)) := by
    convert htend using 1
    funext M
    exact htel M
  exact (hasSum_iff_tendsto_nat_of_nonneg hmono (1 / xm 0 a)).2 hsumT



/-! ## Numerical evaluation of the small partial sums -/

@[simp] lemma asum0 : Asum 0 = 0 := by norm_num [Asum]
@[simp] lemma asum1 : Asum 1 = 1 := by norm_num [Asum, f1, xm]
@[simp] lemma asum2 : Asum 2 = 17 / 16 := by norm_num [Asum, f1, xm]
@[simp] lemma asum3 : Asum 3 = 849 / 784 := by norm_num [Asum, f1, xm]
@[simp] lemma asum4 : Asum 4 = 21421 / 19600 := by norm_num [Asum, f1, xm]
@[simp] lemma bsum1 : Bsum 1 = 1 / 4 := by norm_num [Bsum, f2, xm]
@[simp] lemma bsum2 : Bsum 2 = 29 / 100 := by norm_num [Bsum, f2, xm]
@[simp] lemma bsum3 : Bsum 3 = 489 / 1600 := by norm_num [Bsum, f2, xm]
@[simp] lemma bsum4 : Bsum 4 = 60769 / 193600 := by norm_num [Bsum, f2, xm]


/-! ## The statement denominators equal the `xm` denominators -/

lemma denom_statement (m : ℕ) : ∀ i : ℕ,
    ((((3 * m + 3 + i : ℕ) : ℝ) * ((3 * m + 6 + i : ℕ) : ℝ) * ((3 * m + 9 + i : ℕ) : ℝ)))
      = xm m (3 + i) * xm m (6 + i) * xm m (9 + i) := by
  intro i
  have hf1 : (((3 * m + 3 + i : ℕ) : ℝ)) = xm m (3 + i) := by
    unfold xm
    congr 1
    omega
  have hf2 : (((3 * m + 6 + i : ℕ) : ℝ)) = xm m (6 + i) := by
    unfold xm
    congr 1
    omega
  have hf3 : (((3 * m + 9 + i : ℕ) : ℝ)) = xm m (9 + i) := by
    unfold xm
    congr 1
    omega
  rw [hf1, hf2, hf3]

/-- The inner `i`-sum in the statement's form equals the `xm` form. -/
lemma inner_sum_statement (m : ℕ) :
    (∑ i ∈ Finset.range 6,
      ((-1 : ℝ) ^ i * (Nat.choose 5 i : ℝ)) *
        (18 / ((((3 * m + 3 + i : ℕ) : ℝ) * ((3 * m + 6 + i : ℕ) : ℝ) * ((3 * m + 9 + i : ℕ) : ℝ)))) ^ 2)
    = (∑ i ∈ Finset.range 6,
      ((-1 : ℝ) ^ i * (Nat.choose 5 i : ℝ)) *
        (18 / (xm m (3 + i) * xm m (6 + i) * xm m (9 + i))) ^ 2) := by
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  rw [denom_statement m i]

/-- The `m`-summand of the corrected two-core sum, in the statement's form. -/
lemma vm_eq_statement (m : ℕ) :
    (81 : ℝ) * (Nat.choose (m + 4) 4 : ℝ) *
      (∑ i ∈ Finset.range 6,
        ((-1 : ℝ) ^ i * (Nat.choose 5 i : ℝ)) *
          (18 / ((((3 * m + 3 + i : ℕ) : ℝ) * ((3 * m + 6 + i : ℕ) : ℝ) * ((3 * m + 9 + i : ℕ) : ℝ)))) ^ 2) =
      Vm m := by
  unfold Vm
  rw [inner_sum_statement m]



/-! ## The values of the two pieces -/

/-- The value of the `W1`-sum (before simplifying the small partial sums). -/
noncomputable def V1val : ℝ :=
  ((((50/3 : ℝ) * (A - Asum 1) - (70/3 : ℝ) * (B - Bsum 1)) - (25 : ℝ) * (A - Asum 2))
      + (65 : ℝ) * (B - Bsum 2)) - (35 : ℝ) * (A - Asum 3) - (20 : ℝ) * (B - Bsum 3)
    + (175/3 : ℝ) * (A - Asum 4) - (110/3 : ℝ) * (B - Bsum 4)

/-- The value of the `W2`-sum. -/
noncomputable def V2val : ℝ :=
  (27/4 : ℝ) * (1 / xm 0 3) + (81/4 : ℝ) * (1 / xm 0 6) - (135/2 : ℝ) * (1 / xm 0 9)
    - (235/12 : ℝ) * (1 / xm 0 4) - (85/6 : ℝ) * (1 / xm 0 7) + (115/4 : ℝ) * (1 / xm 0 10)
    + (5/2 : ℝ) * (1 / xm 0 5) + (479/12 : ℝ) * (1 / xm 0 8) + (37/12 : ℝ) * (1 / xm 0 11)

/-- The value of the whole sum. -/
noncomputable def Vval : ℝ := V1val + V2val

/-! ## `HasSum` of the two pieces of the decomposition -/

lemma hasSum_W1 : HasSum W1 V1val := by
  have hT4 : HasSum (fun m : ℕ => (50/3 : ℝ) * (1 / (xm m 4)^2))
      ((50/3 : ℝ) * (A - Asum 1)) := by
    simpa using (hasSum_sq1 1).mul_left (50/3 : ℝ)
  have hT5 : HasSum (fun m : ℕ => (70/3 : ℝ) * (1 / (xm m 5)^2))
      ((70/3 : ℝ) * (B - Bsum 1)) := by
    simpa using (hasSum_sq2 1).mul_left (70/3 : ℝ)
  have hT7 : HasSum (fun m : ℕ => (25 : ℝ) * (1 / (xm m 7)^2))
      ((25 : ℝ) * (A - Asum 2)) := by
    simpa using (hasSum_sq1 2).mul_left (25 : ℝ)
  have hT8 : HasSum (fun m : ℕ => (65 : ℝ) * (1 / (xm m 8)^2))
      ((65 : ℝ) * (B - Bsum 2)) := by
    simpa using (hasSum_sq2 2).mul_left (65 : ℝ)
  have hT10 : HasSum (fun m : ℕ => (35 : ℝ) * (1 / (xm m 10)^2))
      ((35 : ℝ) * (A - Asum 3)) := by
    simpa using (hasSum_sq1 3).mul_left (35 : ℝ)
  have hT11 : HasSum (fun m : ℕ => (20 : ℝ) * (1 / (xm m 11)^2))
      ((20 : ℝ) * (B - Bsum 3)) := by
    simpa using (hasSum_sq2 3).mul_left (20 : ℝ)
  have hT13 : HasSum (fun m : ℕ => (175/3 : ℝ) * (1 / (xm m 13)^2))
      ((175/3 : ℝ) * (A - Asum 4)) := by
    simpa using (hasSum_sq1 4).mul_left (175/3 : ℝ)
  have hT14 : HasSum (fun m : ℕ => (110/3 : ℝ) * (1 / (xm m 14)^2))
      ((110/3 : ℝ) * (B - Bsum 4)) := by
    simpa using (hasSum_sq2 4).mul_left (110/3 : ℝ)
  exact
    ((((((hT4.sub hT5).sub hT7).add hT8).sub hT10).sub hT11).add hT13).sub hT14

lemma hasSum_W2 : HasSum W2 V2val := by
  have hp3 : HasSum (fun m : ℕ => (27/4 : ℝ) * (1 / xm m 3 - 1 / xm m 6))
      ((27/4 : ℝ) * (1 / xm 0 3)) := by
    simpa using (hasSum_pair 3 (by norm_num)).mul_left (27/4 : ℝ)
  have hp6 : HasSum (fun m : ℕ => (81/4 : ℝ) * (1 / xm m 6 - 1 / xm m 9))
      ((81/4 : ℝ) * (1 / xm 0 6)) := by
    simpa using (hasSum_pair 6 (by norm_num)).mul_left (81/4 : ℝ)
  have hp9 : HasSum (fun m : ℕ => (135/2 : ℝ) * (1 / xm m 9 - 1 / xm m 12))
      ((135/2 : ℝ) * (1 / xm 0 9)) := by
    simpa using (hasSum_pair 9 (by norm_num)).mul_left (135/2 : ℝ)
  have hp4 : HasSum (fun m : ℕ => (235/12 : ℝ) * (1 / xm m 4 - 1 / xm m 7))
      ((235/12 : ℝ) * (1 / xm 0 4)) := by
    simpa using (hasSum_pair 4 (by norm_num)).mul_left (235/12 : ℝ)
  have hp7 : HasSum (fun m : ℕ => (85/6 : ℝ) * (1 / xm m 7 - 1 / xm m 10))
      ((85/6 : ℝ) * (1 / xm 0 7)) := by
    simpa using (hasSum_pair 7 (by norm_num)).mul_left (85/6 : ℝ)
  have hp10 : HasSum (fun m : ℕ => (115/4 : ℝ) * (1 / xm m 10 - 1 / xm m 13))
      ((115/4 : ℝ) * (1 / xm 0 10)) := by
    simpa using (hasSum_pair 10 (by norm_num)).mul_left (115/4 : ℝ)
  have hp5 : HasSum (fun m : ℕ => (5/2 : ℝ) * (1 / xm m 5 - 1 / xm m 8))
      ((5/2 : ℝ) * (1 / xm 0 5)) := by
    simpa using (hasSum_pair 5 (by norm_num)).mul_left (5/2 : ℝ)
  have hp8 : HasSum (fun m : ℕ => (479/12 : ℝ) * (1 / xm m 8 - 1 / xm m 11))
      ((479/12 : ℝ) * (1 / xm 0 8)) := by
    simpa using (hasSum_pair 8 (by norm_num)).mul_left (479/12 : ℝ)
  have hp11 : HasSum (fun m : ℕ => (37/12 : ℝ) * (1 / xm m 11 - 1 / xm m 14))
      ((37/12 : ℝ) * (1 / xm 0 11)) := by
    simpa using (hasSum_pair 11 (by norm_num)).mul_left (37/12 : ℝ)
  exact
    (((((((hp3.add hp6).sub hp9).sub hp4).sub hp7).add hp10).add hp5).add hp8).add hp11

/-- `HasSum` for the whole summand. -/
lemma hasSum_Vm : HasSum Vm Vval := by
  have hsum : HasSum (fun m : ℕ => W1 m + W2 m) Vval := by
    simpa [Vval] using hasSum_W1.add hasSum_W2
  apply HasSum.congr_fun hsum
  intro m
  exact vm_decomp m

/-- The infinite sum of `Vm` in closed form. -/
lemma tsum_Vm : (∑' m : ℕ, Vm m) = 15 * A - 15 * B - 23 / 2 := by
  have hval : Vval = 15 * A - 15 * B - 23 / 2 := by
    unfold Vval V1val V2val
    norm_num [xm]
    simp
    ring
  rw [hasSum_Vm.tsum_eq]
  exact hval

end CdtTwoCore
open CdtTwoCore

theorem sum_cintegralTwo_core_corrected :
    (∑' m : ℕ,
        (81 : ℝ) * (Nat.choose (m + 4) 4 : ℝ) *
          (∑ i ∈ Finset.range 6,
            ((-1 : ℝ) ^ i * (Nat.choose 5 i : ℝ)) *
              (18 / ((((3 * m + 3 + i : ℕ) : ℝ) * ((3 * m + 6 + i : ℕ) : ℝ) * ((3 * m + 9 + i : ℕ) : ℝ)))) ^ 2)) =
      15 * (∑' k : ℕ,
          ((1 : ℝ) / (((3 * k + 1 : ℕ) : ℝ) ^ 2) - (1 : ℝ) / (((3 * k + 2 : ℕ) : ℝ) ^ 2))) - 23 / 2 := by
  have hMain := tsum_Vm
  have hL : (∑' m : ℕ, Vm m) =
      (∑' m : ℕ,
        (81 : ℝ) * (Nat.choose (m + 4) 4 : ℝ) *
          (∑ i ∈ Finset.range 6,
            ((-1 : ℝ) ^ i * (Nat.choose 5 i : ℝ)) *
              (18 / ((((3 * m + 3 + i : ℕ) : ℝ) * ((3 * m + 6 + i : ℕ) : ℝ) * ((3 * m + 9 + i : ℕ) : ℝ)))) ^ 2)) := by
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