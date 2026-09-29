import Mathlib
import Submission.Commons.Analysis.Summation.sum_cintegralFour_core

noncomputable section
open scoped BigOperators Nat
open Filter Topology

namespace Commons.Analysis.Summation
namespace CdtSixCore

/-! ## Binomial `(m+12 choose 12)` as a degree-12 polynomial -/

lemma asc12 (n : ℕ) : n.ascFactorial 12 =
    n * (n + 1) * (n + 2) * (n + 3) * (n + 4) * (n + 5) * (n + 6) * (n + 7) *
      (n + 8) * (n + 9) * (n + 10) * (n + 11) := by
  simp [Nat.ascFactorial_succ, Nat.ascFactorial_zero]
  ring

lemma factorial_add_twelve (m : ℕ) : (m + 12)! =
    m ! * (m + 1) * (m + 2) * (m + 3) * (m + 4) * (m + 5) * (m + 6) * (m + 7) *
      (m + 8) * (m + 9) * (m + 10) * (m + 11) * (m + 12) := by
  rw [← Nat.factorial_mul_ascFactorial m 12]
  have h := asc12 (m + 1)
  rw [h]
  ring

lemma choose312 (m : ℕ) :
    (Nat.choose (m + 12) 12 : ℝ) =
      (1 / 479001600 : ℝ) *
        (((m : ℝ) + 1) * ((m : ℝ) + 2) * ((m : ℝ) + 3) * ((m : ℝ) + 4) *
          ((m : ℝ) + 5) * ((m : ℝ) + 6) * ((m : ℝ) + 7) * ((m : ℝ) + 8) *
          ((m : ℝ) + 9) * ((m : ℝ) + 10) * ((m : ℝ) + 11) * ((m : ℝ) + 12)) := by
  have hcast := Nat.cast_choose ℝ (a := 12) (b := m + 12) (by omega : 12 ≤ m + 12)
  rw [hcast]
  have h12 : ((12 : ℕ)! : ℝ) = 479001600 := by norm_num
  have hsub : ((m + 12 - 12) : ℕ) = m := by omega
  rw [h12, hsub]
  have hfacR : ((m + 12)! : ℝ) = (m ! : ℝ) *
      (((m : ℝ) + 1) * ((m : ℝ) + 2) * ((m : ℝ) + 3) * ((m : ℝ) + 4) *
        ((m : ℝ) + 5) * ((m : ℝ) + 6) * ((m : ℝ) + 7) * ((m : ℝ) + 8) *
        ((m : ℝ) + 9) * ((m : ℝ) + 10) * ((m : ℝ) + 11) * ((m : ℝ) + 12)) := by
    norm_num [factorial_add_twelve, Nat.cast_mul]
    ring
  rw [hfacR]
  have hm : (m ! : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_ne_zero m)
  field_simp [hm]

@[simp] lemma c13_0 : (Nat.choose 13 0 : ℝ) = 1 := by
  rw [Nat.cast_choose ℝ (by decide : 0 ≤ 13)]; norm_num
@[simp] lemma c13_1 : (Nat.choose 13 1 : ℝ) = 13 := by
  rw [Nat.cast_choose ℝ (by decide : 1 ≤ 13)]; norm_num
@[simp] lemma c13_2 : (Nat.choose 13 2 : ℝ) = 78 := by
  rw [Nat.cast_choose ℝ (by decide : 2 ≤ 13)]; norm_num
@[simp] lemma c13_3 : (Nat.choose 13 3 : ℝ) = 286 := by
  rw [Nat.cast_choose ℝ (by decide : 3 ≤ 13)]; norm_num
@[simp] lemma c13_4 : (Nat.choose 13 4 : ℝ) = 715 := by
  rw [Nat.cast_choose ℝ (by decide : 4 ≤ 13)]; norm_num
@[simp] lemma c13_5 : (Nat.choose 13 5 : ℝ) = 1287 := by
  rw [Nat.cast_choose ℝ (by decide : 5 ≤ 13)]; norm_num
@[simp] lemma c13_6 : (Nat.choose 13 6 : ℝ) = 1716 := by
  rw [Nat.cast_choose ℝ (by decide : 6 ≤ 13)]; norm_num
@[simp] lemma c13_7 : (Nat.choose 13 7 : ℝ) = 1716 := by
  rw [Nat.cast_choose ℝ (by decide : 7 ≤ 13)]; norm_num
@[simp] lemma c13_8 : (Nat.choose 13 8 : ℝ) = 1287 := by
  rw [Nat.cast_choose ℝ (by decide : 8 ≤ 13)]; norm_num
@[simp] lemma c13_9 : (Nat.choose 13 9 : ℝ) = 715 := by
  rw [Nat.cast_choose ℝ (by decide : 9 ≤ 13)]; norm_num
@[simp] lemma c13_10 : (Nat.choose 13 10 : ℝ) = 286 := by
  rw [Nat.cast_choose ℝ (by decide : 10 ≤ 13)]; norm_num
@[simp] lemma c13_11 : (Nat.choose 13 11 : ℝ) = 78 := by
  rw [Nat.cast_choose ℝ (by decide : 11 ≤ 13)]; norm_num
@[simp] lemma c13_12 : (Nat.choose 13 12 : ℝ) = 13 := by
  rw [Nat.cast_choose ℝ (by decide : 12 ≤ 13)]; norm_num
@[simp] lemma c13_13 : (Nat.choose 13 13 : ℝ) = 1 := by
  rw [Nat.cast_choose ℝ (by decide : 13 ≤ 13)]; norm_num

/-! ## The `m`-summand and its pointwise closed-form decomposition -/

/-- The `m`-summand of the six-core sum. -/
def Vm6 (m : ℕ) : ℝ :=
  (531441 : ℝ) * (Nat.choose (m + 12) 12 : ℝ) *
    (∑ i ∈ Finset.range 14,
      ((-1 : ℝ) ^ i * (Nat.choose 13 i : ℝ)) *
        (524880 / (xm m (7 + i) * xm m (10 + i) * xm m (13 + i) * xm m (16 + i) *
          xm m (19 + i) * xm m (22 + i) * xm m (25 + i))) ^ 2)

/-- Squared-term part of the closed-form decomposition. -/
def W16 (m : ℕ) : ℝ :=
  (((147407 : ℝ) / 243)) * (1 / (xm m 7)^2)
    + (((8895250 : ℝ) / 243)) * (1 / (xm m 10)^2)
    + ((-(38112725 : ℝ) / 81)) * (1 / (xm m 13)^2)
    + (((827645 : ℝ) / 9)) * (1 / (xm m 16)^2)
    + (((507824408 : ℝ) / 81)) * (1 / (xm m 19)^2)
    + ((-(1064323988 : ℝ) / 81)) * (1 / (xm m 22)^2)
    + (((335929880 : ℝ) / 81)) * (1 / (xm m 25)^2)
    + (((258485500 : ℝ) / 27)) * (1 / (xm m 28)^2)
    + ((-(608002850 : ℝ) / 81)) * (1 / (xm m 31)^2)
    + (((132389530 : ℝ) / 243)) * (1 / (xm m 34)^2)
    + (((118453790 : ℝ) / 243)) * (1 / (xm m 37)^2)
    + ((-(1123850 : ℝ) / 243)) * (1 / (xm m 8)^2)
    + ((-(6100900 : ℝ) / 243)) * (1 / (xm m 11)^2)
    + (((76434644 : ℝ) / 81)) * (1 / (xm m 14)^2)
    + ((-(72375940 : ℝ) / 27)) * (1 / (xm m 17)^2)
    + ((-(191271080 : ℝ) / 81)) * (1 / (xm m 20)^2)
    + (((1190362355 : ℝ) / 81)) * (1 / (xm m 23)^2)
    + ((-(1123073210 : ℝ) / 81)) * (1 / (xm m 26)^2)
    + ((-(3807167 : ℝ) / 9)) * (1 / (xm m 29)^2)
    + (((410528495 : ℝ) / 81)) * (1 / (xm m 32)^2)
    + ((-(294814000 : ℝ) / 243)) * (1 / (xm m 35)^2)
    + ((-(41273960 : ℝ) / 243)) * (1 / (xm m 38)^2)

/-- Telescoping-pair part of the closed-form decomposition. -/
def W26 (m : ℕ) : ℝ :=
  ((-(2275628899 : ℝ) / 2245320)) * (1 / xm m 7 - 1 / xm m 10)
    + (((156433979 : ℝ) / 64152)) * (1 / xm m 8 - 1 / xm m 11)
    + (((2302911 : ℝ) / 110)) * (1 / xm m 9 - 1 / xm m 12)
    + ((-(18153279941 : ℝ) / 249480)) * (1 / xm m 10 - 1 / xm m 13)
    + (((8488831585 : ℝ) / 149688)) * (1 / xm m 11 - 1 / xm m 14)
    + ((-(2302911 : ℝ) / 20)) * (1 / xm m 12 - 1 / xm m 15)
    + (((159696725501 : ℝ) / 374220)) * (1 / xm m 13 - 1 / xm m 16)
    + (((12402869791 : ℝ) / 748440)) * (1 / xm m 14 - 1 / xm m 17)
    + ((-(591848127 : ℝ) / 440)) * (1 / xm m 15 - 1 / xm m 18)
    + (((2765812223491 : ℝ) / 2245320)) * (1 / xm m 16 - 1 / xm m 19)
    + ((-(3511000133797 : ℝ) / 2245320)) * (1 / xm m 17 - 1 / xm m 20)
    + (((1195210809 : ℝ) / 220)) * (1 / xm m 18 - 1 / xm m 21)
    + ((-(4269041157707 : ℝ) / 748440)) * (1 / xm m 19 - 1 / xm m 22)
    + (((465971274101 : ℝ) / 748440)) * (1 / xm m 20 - 1 / xm m 23)
    + ((-(568819017 : ℝ) / 440)) * (1 / xm m 21 - 1 / xm m 24)
    + (((1799425751119 : ℝ) / 748440)) * (1 / xm m 22 - 1 / xm m 25)
    + (((1197450448769 : ℝ) / 187110)) * (1 / xm m 23 - 1 / xm m 26)
    + ((-(214170723 : ℝ) / 20)) * (1 / xm m 24 - 1 / xm m 27)
    + (((1699076439151 : ℝ) / 320760)) * (1 / xm m 25 - 1 / xm m 28)
    + ((-(6410076026201 : ℝ) / 1122660)) * (1 / xm m 26 - 1 / xm m 29)
    + (((181929969 : ℝ) / 22)) * (1 / xm m 27 - 1 / xm m 30)
    + ((-(290718791233 : ℝ) / 106920)) * (1 / xm m 28 - 1 / xm m 31)
    + ((-(283944958397 : ℝ) / 149688)) * (1 / xm m 29 - 1 / xm m 32)
    + (((39149487 : ℝ) / 44)) * (1 / xm m 30 - 1 / xm m 33)
    + ((-(22702566107 : ℝ) / 26730)) * (1 / xm m 31 - 1 / xm m 34)
    + (((46976163335 : ℝ) / 24948)) * (1 / xm m 32 - 1 / xm m 35)
    + ((-(2302911 : ℝ) / 2)) * (1 / xm m 33 - 1 / xm m 36)
    + (((36653228027 : ℝ) / 320760)) * (1 / xm m 34 - 1 / xm m 37)
    + (((1966395319 : ℝ) / 32076)) * (1 / xm m 35 - 1 / xm m 38)

set_option maxHeartbeats 8000000 in
lemma vm6_decomp (m : ℕ) : Vm6 m = W16 m + W26 m := by
  unfold Vm6 W16 W26
  rw [choose312]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero,
    c13_0, c13_1, c13_2, c13_3, c13_4, c13_5, c13_6, c13_7, c13_8, c13_9, c13_10, c13_11, c13_12, c13_13]
  norm_num
  simp_rw [xm_eq]
  norm_num
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
  have h33 : (3 * (m : ℝ) + 33) ≠ 0 := by positivity
  have h34 : (3 * (m : ℝ) + 34) ≠ 0 := by positivity
  have h35 : (3 * (m : ℝ) + 35) ≠ 0 := by positivity
  have h36 : (3 * (m : ℝ) + 36) ≠ 0 := by positivity
  have h37 : (3 * (m : ℝ) + 37) ≠ 0 := by positivity
  have h38 : (3 * (m : ℝ) + 38) ≠ 0 := by positivity
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
  have hm11 : (m : ℝ) + 11 ≠ 0 := by positivity
  have hm12 : (m : ℝ) + 12 ≠ 0 := by positivity
  field_simp
  ring

/-! ## The statement denominators equal the `xm` denominators -/

lemma denom_statement6 (m : ℕ) : ∀ i : ℕ,
    ((((3 * m + 7 + i : ℕ) : ℝ) * ((3 * m + 10 + i : ℕ) : ℝ) *
        ((3 * m + 13 + i : ℕ) : ℝ) * ((3 * m + 16 + i : ℕ) : ℝ) *
          ((3 * m + 19 + i : ℕ) : ℝ) * ((3 * m + 22 + i : ℕ) : ℝ) *
            ((3 * m + 25 + i : ℕ) : ℝ)))
      = xm m (7 + i) * xm m (10 + i) * xm m (13 + i) * xm m (16 + i) *
          xm m (19 + i) * xm m (22 + i) * xm m (25 + i) := by
  intro i
  have h1 : (((3 * m + 7 + i : ℕ) : ℝ)) = xm m (7 + i) := by
    unfold xm
    congr 1
    omega
  have h2 : (((3 * m + 10 + i : ℕ) : ℝ)) = xm m (10 + i) := by
    unfold xm
    congr 1
    omega
  have h3 : (((3 * m + 13 + i : ℕ) : ℝ)) = xm m (13 + i) := by
    unfold xm
    congr 1
    omega
  have h4 : (((3 * m + 16 + i : ℕ) : ℝ)) = xm m (16 + i) := by
    unfold xm
    congr 1
    omega
  have h5 : (((3 * m + 19 + i : ℕ) : ℝ)) = xm m (19 + i) := by
    unfold xm
    congr 1
    omega
  have h6 : (((3 * m + 22 + i : ℕ) : ℝ)) = xm m (22 + i) := by
    unfold xm
    congr 1
    omega
  have h7 : (((3 * m + 25 + i : ℕ) : ℝ)) = xm m (25 + i) := by
    unfold xm
    congr 1
    omega
  rw [h1, h2, h3, h4, h5, h6, h7]

/-- The inner `i`-sum in the statement's form equals the `xm` form. -/
lemma inner_sum_statement6 (m : ℕ) :
    (∑ i ∈ Finset.range 14,
      ((-1 : ℝ) ^ i * (Nat.choose 13 i : ℝ)) *
        (524880 / ((((3 * m + 7 + i : ℕ) : ℝ) * ((3 * m + 10 + i : ℕ) : ℝ) *
          ((3 * m + 13 + i : ℕ) : ℝ) * ((3 * m + 16 + i : ℕ) : ℝ) *
            ((3 * m + 19 + i : ℕ) : ℝ) * ((3 * m + 22 + i : ℕ) : ℝ) *
              ((3 * m + 25 + i : ℕ) : ℝ)))) ^ 2)
    = (∑ i ∈ Finset.range 14,
      ((-1 : ℝ) ^ i * (Nat.choose 13 i : ℝ)) *
        (524880 / (xm m (7 + i) * xm m (10 + i) * xm m (13 + i) * xm m (16 + i) *
          xm m (19 + i) * xm m (22 + i) * xm m (25 + i))) ^ 2) := by
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  rw [denom_statement6 m i]

/-- The `m`-summand of the six-core sum, in the statement's form. -/
lemma vm6_eq_statement (m : ℕ) :
    (531441 : ℝ) * (Nat.choose (m + 12) 12 : ℝ) *
      (∑ i ∈ Finset.range 14,
        ((-1 : ℝ) ^ i * (Nat.choose 13 i : ℝ)) *
          (524880 / ((((3 * m + 7 + i : ℕ) : ℝ) * ((3 * m + 10 + i : ℕ) : ℝ) *
            ((3 * m + 13 + i : ℕ) : ℝ) * ((3 * m + 16 + i : ℕ) : ℝ) *
              ((3 * m + 19 + i : ℕ) : ℝ) * ((3 * m + 22 + i : ℕ) : ℝ) *
                ((3 * m + 25 + i : ℕ) : ℝ)))) ^ 2) =
      Vm6 m := by
  unfold Vm6
  rw [inner_sum_statement6 m]

/-! ## Small partial sums needed for the shifts -/

@[simp] lemma asum2 : Asum 2 = 17 / 16 := by norm_num [Asum, f1, xm]
@[simp] lemma asum3 : Asum 3 = 849 / 784 := by norm_num [Asum, f1, xm]
@[simp] lemma asum4 : Asum 4 = 21421 / 19600 := by norm_num [Asum, f1, xm]
@[simp] lemma asum5 : Asum 5 = 3639749 / 3312400 := by norm_num [Asum, f1, xm]
@[simp] lemma asum6 : Asum 6 = 58443009 / 52998400 := by norm_num [Asum, f1, xm]
@[simp] lemma asum7 : Asum 7 = 21150924649 / 19132422400 := by norm_num [Asum, f1, xm]
@[simp] lemma asum8 : Asum 8 = 2564044988129 / 2315023110400 := by norm_num [Asum, f1, xm]
@[simp] lemma asum9 : Asum 9 = 64193725627641 / 57875577760000 := by norm_num [Asum, f1, xm]
@[simp] lemma asum10 : Asum 10 = 64267546517641 / 57875577760000 := by norm_num [Asum, f1, xm]
@[simp] lemma asum11 : Asum 11 = 61818987781213001 / 55618430227360000 := by norm_num [Asum, f1, xm]
@[simp] lemma asum12 : Asum 12 = 17879592076327397289 / 16073726335707040000 := by norm_num [Asum, f1, xm]
@[simp] lemma bsum2 : Bsum 2 = 29 / 100 := by norm_num [Bsum, f2, xm]
@[simp] lemma bsum3 : Bsum 3 = 489 / 1600 := by norm_num [Bsum, f2, xm]
@[simp] lemma bsum4 : Bsum 4 = 60769 / 193600 := by norm_num [Bsum, f2, xm]
@[simp] lemma bsum5 : Bsum 5 = 3026081 / 9486400 := by norm_num [Bsum, f2, xm]
@[simp] lemma bsum6 : Bsum 6 = 884023809 / 2741569600 := by norm_num [Bsum, f2, xm]
@[simp] lemma bsum7 : Bsum 7 = 890877733 / 2741569600 := by norm_num [Bsum, f2, xm]
@[simp] lemma bsum8 : Bsum 8 = 474015890357 / 1450290318400 := by norm_num [Bsum, f2, xm]
@[simp] lemma bsum9 : Bsum 9 = 80471258049933 / 245099063809600 := by norm_num [Bsum, f2, xm]
@[simp] lemma bsum10 : Bsum 10 = 67921427083803253 / 206128312663873600 := by norm_num [Bsum, f2, xm]
@[simp] lemma bsum11 : Bsum 11 = 1089963588226225073 / 3298053002621977600 := by norm_num [Bsum, f2, xm]
@[simp] lemma bsum12 : Bsum 12 = 1092655876391630769 / 3298053002621977600 := by norm_num [Bsum, f2, xm]

/-! ## The values of the two pieces -/

/-- The value of the `W16`-sum. -/
noncomputable def V1val6 : ℝ :=
  (((147407 : ℝ) / 243)) * (A - Asum 2)
    + (((8895250 : ℝ) / 243)) * (A - Asum 3)
    + ((-(38112725 : ℝ) / 81)) * (A - Asum 4)
    + (((827645 : ℝ) / 9)) * (A - Asum 5)
    + (((507824408 : ℝ) / 81)) * (A - Asum 6)
    + ((-(1064323988 : ℝ) / 81)) * (A - Asum 7)
    + (((335929880 : ℝ) / 81)) * (A - Asum 8)
    + (((258485500 : ℝ) / 27)) * (A - Asum 9)
    + ((-(608002850 : ℝ) / 81)) * (A - Asum 10)
    + (((132389530 : ℝ) / 243)) * (A - Asum 11)
    + (((118453790 : ℝ) / 243)) * (A - Asum 12)
    + ((-(1123850 : ℝ) / 243)) * (B - Bsum 2)
    + ((-(6100900 : ℝ) / 243)) * (B - Bsum 3)
    + (((76434644 : ℝ) / 81)) * (B - Bsum 4)
    + ((-(72375940 : ℝ) / 27)) * (B - Bsum 5)
    + ((-(191271080 : ℝ) / 81)) * (B - Bsum 6)
    + (((1190362355 : ℝ) / 81)) * (B - Bsum 7)
    + ((-(1123073210 : ℝ) / 81)) * (B - Bsum 8)
    + ((-(3807167 : ℝ) / 9)) * (B - Bsum 9)
    + (((410528495 : ℝ) / 81)) * (B - Bsum 10)
    + ((-(294814000 : ℝ) / 243)) * (B - Bsum 11)
    + ((-(41273960 : ℝ) / 243)) * (B - Bsum 12)

/-- The value of the `W26`-sum. -/
noncomputable def V2val6 : ℝ :=
  ((-(2275628899 : ℝ) / 2245320)) * (1 / xm 0 7)
    + (((156433979 : ℝ) / 64152)) * (1 / xm 0 8)
    + (((2302911 : ℝ) / 110)) * (1 / xm 0 9)
    + ((-(18153279941 : ℝ) / 249480)) * (1 / xm 0 10)
    + (((8488831585 : ℝ) / 149688)) * (1 / xm 0 11)
    + ((-(2302911 : ℝ) / 20)) * (1 / xm 0 12)
    + (((159696725501 : ℝ) / 374220)) * (1 / xm 0 13)
    + (((12402869791 : ℝ) / 748440)) * (1 / xm 0 14)
    + ((-(591848127 : ℝ) / 440)) * (1 / xm 0 15)
    + (((2765812223491 : ℝ) / 2245320)) * (1 / xm 0 16)
    + ((-(3511000133797 : ℝ) / 2245320)) * (1 / xm 0 17)
    + (((1195210809 : ℝ) / 220)) * (1 / xm 0 18)
    + ((-(4269041157707 : ℝ) / 748440)) * (1 / xm 0 19)
    + (((465971274101 : ℝ) / 748440)) * (1 / xm 0 20)
    + ((-(568819017 : ℝ) / 440)) * (1 / xm 0 21)
    + (((1799425751119 : ℝ) / 748440)) * (1 / xm 0 22)
    + (((1197450448769 : ℝ) / 187110)) * (1 / xm 0 23)
    + ((-(214170723 : ℝ) / 20)) * (1 / xm 0 24)
    + (((1699076439151 : ℝ) / 320760)) * (1 / xm 0 25)
    + ((-(6410076026201 : ℝ) / 1122660)) * (1 / xm 0 26)
    + (((181929969 : ℝ) / 22)) * (1 / xm 0 27)
    + ((-(290718791233 : ℝ) / 106920)) * (1 / xm 0 28)
    + ((-(283944958397 : ℝ) / 149688)) * (1 / xm 0 29)
    + (((39149487 : ℝ) / 44)) * (1 / xm 0 30)
    + ((-(22702566107 : ℝ) / 26730)) * (1 / xm 0 31)
    + (((46976163335 : ℝ) / 24948)) * (1 / xm 0 32)
    + ((-(2302911 : ℝ) / 2)) * (1 / xm 0 33)
    + (((36653228027 : ℝ) / 320760)) * (1 / xm 0 34)
    + (((1966395319 : ℝ) / 32076)) * (1 / xm 0 35)

/-- The value of the whole sum. -/
noncomputable def Vval6 : ℝ := V1val6 + V2val6

/-! ## `HasSum` of the two pieces of the decomposition -/

lemma hasSum_W16 : HasSum W16 V1val6 := by
  have hA2 : HasSum (fun m : ℕ => ((147407 : ℝ) / 243) * (1 / (xm m 7)^2))
      (((147407 : ℝ) / 243) * (A - Asum 2)) := by
    simpa using (CdtTwoCore.hasSum_sq1 2).mul_left ((147407 : ℝ) / 243)
  have hA3 : HasSum (fun m : ℕ => ((8895250 : ℝ) / 243) * (1 / (xm m 10)^2))
      (((8895250 : ℝ) / 243) * (A - Asum 3)) := by
    simpa using (CdtTwoCore.hasSum_sq1 3).mul_left ((8895250 : ℝ) / 243)
  have hA4 : HasSum (fun m : ℕ => (-(38112725 : ℝ) / 81) * (1 / (xm m 13)^2))
      ((-(38112725 : ℝ) / 81) * (A - Asum 4)) := by
    simpa using (CdtTwoCore.hasSum_sq1 4).mul_left (-(38112725 : ℝ) / 81)
  have hA5 : HasSum (fun m : ℕ => ((827645 : ℝ) / 9) * (1 / (xm m 16)^2))
      (((827645 : ℝ) / 9) * (A - Asum 5)) := by
    simpa using (CdtTwoCore.hasSum_sq1 5).mul_left ((827645 : ℝ) / 9)
  have hA6 : HasSum (fun m : ℕ => ((507824408 : ℝ) / 81) * (1 / (xm m 19)^2))
      (((507824408 : ℝ) / 81) * (A - Asum 6)) := by
    simpa using (CdtTwoCore.hasSum_sq1 6).mul_left ((507824408 : ℝ) / 81)
  have hA7 : HasSum (fun m : ℕ => (-(1064323988 : ℝ) / 81) * (1 / (xm m 22)^2))
      ((-(1064323988 : ℝ) / 81) * (A - Asum 7)) := by
    simpa using (CdtTwoCore.hasSum_sq1 7).mul_left (-(1064323988 : ℝ) / 81)
  have hA8 : HasSum (fun m : ℕ => ((335929880 : ℝ) / 81) * (1 / (xm m 25)^2))
      (((335929880 : ℝ) / 81) * (A - Asum 8)) := by
    simpa using (CdtTwoCore.hasSum_sq1 8).mul_left ((335929880 : ℝ) / 81)
  have hA9 : HasSum (fun m : ℕ => ((258485500 : ℝ) / 27) * (1 / (xm m 28)^2))
      (((258485500 : ℝ) / 27) * (A - Asum 9)) := by
    simpa using (CdtTwoCore.hasSum_sq1 9).mul_left ((258485500 : ℝ) / 27)
  have hA10 : HasSum (fun m : ℕ => (-(608002850 : ℝ) / 81) * (1 / (xm m 31)^2))
      ((-(608002850 : ℝ) / 81) * (A - Asum 10)) := by
    simpa using (CdtTwoCore.hasSum_sq1 10).mul_left (-(608002850 : ℝ) / 81)
  have hA11 : HasSum (fun m : ℕ => ((132389530 : ℝ) / 243) * (1 / (xm m 34)^2))
      (((132389530 : ℝ) / 243) * (A - Asum 11)) := by
    simpa using (CdtTwoCore.hasSum_sq1 11).mul_left ((132389530 : ℝ) / 243)
  have hA12 : HasSum (fun m : ℕ => ((118453790 : ℝ) / 243) * (1 / (xm m 37)^2))
      (((118453790 : ℝ) / 243) * (A - Asum 12)) := by
    simpa using (CdtTwoCore.hasSum_sq1 12).mul_left ((118453790 : ℝ) / 243)
  have hB2 : HasSum (fun m : ℕ => (-(1123850 : ℝ) / 243) * (1 / (xm m 8)^2))
      ((-(1123850 : ℝ) / 243) * (B - Bsum 2)) := by
    simpa using (CdtTwoCore.hasSum_sq2 2).mul_left (-(1123850 : ℝ) / 243)
  have hB3 : HasSum (fun m : ℕ => (-(6100900 : ℝ) / 243) * (1 / (xm m 11)^2))
      ((-(6100900 : ℝ) / 243) * (B - Bsum 3)) := by
    simpa using (CdtTwoCore.hasSum_sq2 3).mul_left (-(6100900 : ℝ) / 243)
  have hB4 : HasSum (fun m : ℕ => ((76434644 : ℝ) / 81) * (1 / (xm m 14)^2))
      (((76434644 : ℝ) / 81) * (B - Bsum 4)) := by
    simpa using (CdtTwoCore.hasSum_sq2 4).mul_left ((76434644 : ℝ) / 81)
  have hB5 : HasSum (fun m : ℕ => (-(72375940 : ℝ) / 27) * (1 / (xm m 17)^2))
      ((-(72375940 : ℝ) / 27) * (B - Bsum 5)) := by
    simpa using (CdtTwoCore.hasSum_sq2 5).mul_left (-(72375940 : ℝ) / 27)
  have hB6 : HasSum (fun m : ℕ => (-(191271080 : ℝ) / 81) * (1 / (xm m 20)^2))
      ((-(191271080 : ℝ) / 81) * (B - Bsum 6)) := by
    simpa using (CdtTwoCore.hasSum_sq2 6).mul_left (-(191271080 : ℝ) / 81)
  have hB7 : HasSum (fun m : ℕ => ((1190362355 : ℝ) / 81) * (1 / (xm m 23)^2))
      (((1190362355 : ℝ) / 81) * (B - Bsum 7)) := by
    simpa using (CdtTwoCore.hasSum_sq2 7).mul_left ((1190362355 : ℝ) / 81)
  have hB8 : HasSum (fun m : ℕ => (-(1123073210 : ℝ) / 81) * (1 / (xm m 26)^2))
      ((-(1123073210 : ℝ) / 81) * (B - Bsum 8)) := by
    simpa using (CdtTwoCore.hasSum_sq2 8).mul_left (-(1123073210 : ℝ) / 81)
  have hB9 : HasSum (fun m : ℕ => (-(3807167 : ℝ) / 9) * (1 / (xm m 29)^2))
      ((-(3807167 : ℝ) / 9) * (B - Bsum 9)) := by
    simpa using (CdtTwoCore.hasSum_sq2 9).mul_left (-(3807167 : ℝ) / 9)
  have hB10 : HasSum (fun m : ℕ => ((410528495 : ℝ) / 81) * (1 / (xm m 32)^2))
      (((410528495 : ℝ) / 81) * (B - Bsum 10)) := by
    simpa using (CdtTwoCore.hasSum_sq2 10).mul_left ((410528495 : ℝ) / 81)
  have hB11 : HasSum (fun m : ℕ => (-(294814000 : ℝ) / 243) * (1 / (xm m 35)^2))
      ((-(294814000 : ℝ) / 243) * (B - Bsum 11)) := by
    simpa using (CdtTwoCore.hasSum_sq2 11).mul_left (-(294814000 : ℝ) / 243)
  have hB12 : HasSum (fun m : ℕ => (-(41273960 : ℝ) / 243) * (1 / (xm m 38)^2))
      ((-(41273960 : ℝ) / 243) * (B - Bsum 12)) := by
    simpa using (CdtTwoCore.hasSum_sq2 12).mul_left (-(41273960 : ℝ) / 243)
  exact (((((((((((((((((((((hA2.add hA3).add hA4).add hA5).add hA6).add hA7).add hA8).add hA9).add hA10).add hA11).add hA12).add hB2).add hB3).add hB4).add hB5).add hB6).add hB7).add hB8).add hB9).add hB10).add hB11).add hB12)

lemma hasSum_W26 : HasSum W26 V2val6 := by
  have hp7 : HasSum (fun m : ℕ => (-(2275628899 : ℝ) / 2245320) * (1 / xm m 7 - 1 / xm m 10))
      ((-(2275628899 : ℝ) / 2245320) * (1 / xm 0 7)) := by
    simpa using (CdtTwoCore.hasSum_pair 7 (by norm_num)).mul_left (-(2275628899 : ℝ) / 2245320)
  have hp8 : HasSum (fun m : ℕ => ((156433979 : ℝ) / 64152) * (1 / xm m 8 - 1 / xm m 11))
      (((156433979 : ℝ) / 64152) * (1 / xm 0 8)) := by
    simpa using (CdtTwoCore.hasSum_pair 8 (by norm_num)).mul_left ((156433979 : ℝ) / 64152)
  have hp9 : HasSum (fun m : ℕ => ((2302911 : ℝ) / 110) * (1 / xm m 9 - 1 / xm m 12))
      (((2302911 : ℝ) / 110) * (1 / xm 0 9)) := by
    simpa using (CdtTwoCore.hasSum_pair 9 (by norm_num)).mul_left ((2302911 : ℝ) / 110)
  have hp10 : HasSum (fun m : ℕ => (-(18153279941 : ℝ) / 249480) * (1 / xm m 10 - 1 / xm m 13))
      ((-(18153279941 : ℝ) / 249480) * (1 / xm 0 10)) := by
    simpa using (CdtTwoCore.hasSum_pair 10 (by norm_num)).mul_left (-(18153279941 : ℝ) / 249480)
  have hp11 : HasSum (fun m : ℕ => ((8488831585 : ℝ) / 149688) * (1 / xm m 11 - 1 / xm m 14))
      (((8488831585 : ℝ) / 149688) * (1 / xm 0 11)) := by
    simpa using (CdtTwoCore.hasSum_pair 11 (by norm_num)).mul_left ((8488831585 : ℝ) / 149688)
  have hp12 : HasSum (fun m : ℕ => (-(2302911 : ℝ) / 20) * (1 / xm m 12 - 1 / xm m 15))
      ((-(2302911 : ℝ) / 20) * (1 / xm 0 12)) := by
    simpa using (CdtTwoCore.hasSum_pair 12 (by norm_num)).mul_left (-(2302911 : ℝ) / 20)
  have hp13 : HasSum (fun m : ℕ => ((159696725501 : ℝ) / 374220) * (1 / xm m 13 - 1 / xm m 16))
      (((159696725501 : ℝ) / 374220) * (1 / xm 0 13)) := by
    simpa using (CdtTwoCore.hasSum_pair 13 (by norm_num)).mul_left ((159696725501 : ℝ) / 374220)
  have hp14 : HasSum (fun m : ℕ => ((12402869791 : ℝ) / 748440) * (1 / xm m 14 - 1 / xm m 17))
      (((12402869791 : ℝ) / 748440) * (1 / xm 0 14)) := by
    simpa using (CdtTwoCore.hasSum_pair 14 (by norm_num)).mul_left ((12402869791 : ℝ) / 748440)
  have hp15 : HasSum (fun m : ℕ => (-(591848127 : ℝ) / 440) * (1 / xm m 15 - 1 / xm m 18))
      ((-(591848127 : ℝ) / 440) * (1 / xm 0 15)) := by
    simpa using (CdtTwoCore.hasSum_pair 15 (by norm_num)).mul_left (-(591848127 : ℝ) / 440)
  have hp16 : HasSum (fun m : ℕ => ((2765812223491 : ℝ) / 2245320) * (1 / xm m 16 - 1 / xm m 19))
      (((2765812223491 : ℝ) / 2245320) * (1 / xm 0 16)) := by
    simpa using (CdtTwoCore.hasSum_pair 16 (by norm_num)).mul_left ((2765812223491 : ℝ) / 2245320)
  have hp17 : HasSum (fun m : ℕ => (-(3511000133797 : ℝ) / 2245320) * (1 / xm m 17 - 1 / xm m 20))
      ((-(3511000133797 : ℝ) / 2245320) * (1 / xm 0 17)) := by
    simpa using (CdtTwoCore.hasSum_pair 17 (by norm_num)).mul_left (-(3511000133797 : ℝ) / 2245320)
  have hp18 : HasSum (fun m : ℕ => ((1195210809 : ℝ) / 220) * (1 / xm m 18 - 1 / xm m 21))
      (((1195210809 : ℝ) / 220) * (1 / xm 0 18)) := by
    simpa using (CdtTwoCore.hasSum_pair 18 (by norm_num)).mul_left ((1195210809 : ℝ) / 220)
  have hp19 : HasSum (fun m : ℕ => (-(4269041157707 : ℝ) / 748440) * (1 / xm m 19 - 1 / xm m 22))
      ((-(4269041157707 : ℝ) / 748440) * (1 / xm 0 19)) := by
    simpa using (CdtTwoCore.hasSum_pair 19 (by norm_num)).mul_left (-(4269041157707 : ℝ) / 748440)
  have hp20 : HasSum (fun m : ℕ => ((465971274101 : ℝ) / 748440) * (1 / xm m 20 - 1 / xm m 23))
      (((465971274101 : ℝ) / 748440) * (1 / xm 0 20)) := by
    simpa using (CdtTwoCore.hasSum_pair 20 (by norm_num)).mul_left ((465971274101 : ℝ) / 748440)
  have hp21 : HasSum (fun m : ℕ => (-(568819017 : ℝ) / 440) * (1 / xm m 21 - 1 / xm m 24))
      ((-(568819017 : ℝ) / 440) * (1 / xm 0 21)) := by
    simpa using (CdtTwoCore.hasSum_pair 21 (by norm_num)).mul_left (-(568819017 : ℝ) / 440)
  have hp22 : HasSum (fun m : ℕ => ((1799425751119 : ℝ) / 748440) * (1 / xm m 22 - 1 / xm m 25))
      (((1799425751119 : ℝ) / 748440) * (1 / xm 0 22)) := by
    simpa using (CdtTwoCore.hasSum_pair 22 (by norm_num)).mul_left ((1799425751119 : ℝ) / 748440)
  have hp23 : HasSum (fun m : ℕ => ((1197450448769 : ℝ) / 187110) * (1 / xm m 23 - 1 / xm m 26))
      (((1197450448769 : ℝ) / 187110) * (1 / xm 0 23)) := by
    simpa using (CdtTwoCore.hasSum_pair 23 (by norm_num)).mul_left ((1197450448769 : ℝ) / 187110)
  have hp24 : HasSum (fun m : ℕ => (-(214170723 : ℝ) / 20) * (1 / xm m 24 - 1 / xm m 27))
      ((-(214170723 : ℝ) / 20) * (1 / xm 0 24)) := by
    simpa using (CdtTwoCore.hasSum_pair 24 (by norm_num)).mul_left (-(214170723 : ℝ) / 20)
  have hp25 : HasSum (fun m : ℕ => ((1699076439151 : ℝ) / 320760) * (1 / xm m 25 - 1 / xm m 28))
      (((1699076439151 : ℝ) / 320760) * (1 / xm 0 25)) := by
    simpa using (CdtTwoCore.hasSum_pair 25 (by norm_num)).mul_left ((1699076439151 : ℝ) / 320760)
  have hp26 : HasSum (fun m : ℕ => (-(6410076026201 : ℝ) / 1122660) * (1 / xm m 26 - 1 / xm m 29))
      ((-(6410076026201 : ℝ) / 1122660) * (1 / xm 0 26)) := by
    simpa using (CdtTwoCore.hasSum_pair 26 (by norm_num)).mul_left (-(6410076026201 : ℝ) / 1122660)
  have hp27 : HasSum (fun m : ℕ => ((181929969 : ℝ) / 22) * (1 / xm m 27 - 1 / xm m 30))
      (((181929969 : ℝ) / 22) * (1 / xm 0 27)) := by
    simpa using (CdtTwoCore.hasSum_pair 27 (by norm_num)).mul_left ((181929969 : ℝ) / 22)
  have hp28 : HasSum (fun m : ℕ => (-(290718791233 : ℝ) / 106920) * (1 / xm m 28 - 1 / xm m 31))
      ((-(290718791233 : ℝ) / 106920) * (1 / xm 0 28)) := by
    simpa using (CdtTwoCore.hasSum_pair 28 (by norm_num)).mul_left (-(290718791233 : ℝ) / 106920)
  have hp29 : HasSum (fun m : ℕ => (-(283944958397 : ℝ) / 149688) * (1 / xm m 29 - 1 / xm m 32))
      ((-(283944958397 : ℝ) / 149688) * (1 / xm 0 29)) := by
    simpa using (CdtTwoCore.hasSum_pair 29 (by norm_num)).mul_left (-(283944958397 : ℝ) / 149688)
  have hp30 : HasSum (fun m : ℕ => ((39149487 : ℝ) / 44) * (1 / xm m 30 - 1 / xm m 33))
      (((39149487 : ℝ) / 44) * (1 / xm 0 30)) := by
    simpa using (CdtTwoCore.hasSum_pair 30 (by norm_num)).mul_left ((39149487 : ℝ) / 44)
  have hp31 : HasSum (fun m : ℕ => (-(22702566107 : ℝ) / 26730) * (1 / xm m 31 - 1 / xm m 34))
      ((-(22702566107 : ℝ) / 26730) * (1 / xm 0 31)) := by
    simpa using (CdtTwoCore.hasSum_pair 31 (by norm_num)).mul_left (-(22702566107 : ℝ) / 26730)
  have hp32 : HasSum (fun m : ℕ => ((46976163335 : ℝ) / 24948) * (1 / xm m 32 - 1 / xm m 35))
      (((46976163335 : ℝ) / 24948) * (1 / xm 0 32)) := by
    simpa using (CdtTwoCore.hasSum_pair 32 (by norm_num)).mul_left ((46976163335 : ℝ) / 24948)
  have hp33 : HasSum (fun m : ℕ => (-(2302911 : ℝ) / 2) * (1 / xm m 33 - 1 / xm m 36))
      ((-(2302911 : ℝ) / 2) * (1 / xm 0 33)) := by
    simpa using (CdtTwoCore.hasSum_pair 33 (by norm_num)).mul_left (-(2302911 : ℝ) / 2)
  have hp34 : HasSum (fun m : ℕ => ((36653228027 : ℝ) / 320760) * (1 / xm m 34 - 1 / xm m 37))
      (((36653228027 : ℝ) / 320760) * (1 / xm 0 34)) := by
    simpa using (CdtTwoCore.hasSum_pair 34 (by norm_num)).mul_left ((36653228027 : ℝ) / 320760)
  have hp35 : HasSum (fun m : ℕ => ((1966395319 : ℝ) / 32076) * (1 / xm m 35 - 1 / xm m 38))
      (((1966395319 : ℝ) / 32076) * (1 / xm 0 35)) := by
    simpa using (CdtTwoCore.hasSum_pair 35 (by norm_num)).mul_left ((1966395319 : ℝ) / 32076)
  exact ((((((((((((((((((((((((((((hp7.add hp8).add hp9).add hp10).add hp11).add hp12).add hp13).add hp14).add hp15).add hp16).add hp17).add hp18).add hp19).add hp20).add hp21).add hp22).add hp23).add hp24).add hp25).add hp26).add hp27).add hp28).add hp29).add hp30).add hp31).add hp32).add hp33).add hp34).add hp35)

/-- `HasSum` for the whole summand. -/
lemma hasSum_Vm6 : HasSum Vm6 Vval6 := by
  have hsum : HasSum (fun m : ℕ => W16 m + W26 m) Vval6 := by
    simpa [Vval6] using hasSum_W16.add hasSum_W26
  apply HasSum.congr_fun hsum
  intro m
  exact vm6_decomp m

/-- The infinite sum of `Vm6` in closed form. -/
lemma tsum_Vm6 : (∑' m : ℕ, Vm6 m) = 35169 * A - 35169 * B - 5495507 / 200 := by
  have hval : Vval6 = 35169 * A - 35169 * B - 5495507 / 200 := by
    unfold Vval6 V1val6 V2val6
    norm_num [xm]
    ring
  rw [hasSum_Vm6.tsum_eq]
  exact hval

end CdtSixCore
open CdtSixCore

/-! ## Final assembly -/


/-- Creative-telescoping evaluation of the degree-6 `(Cintegral)` inner sum:
`Σₘ 531441·C(m+12,12)·Σᵢ₌₀¹³(−1)ⁱC(13,i)·(524880/∏_{k=0}^{6}(3m+7+3k+i))²
 = 35169·Σₖ(1/(3k+1)²−1/(3k+2)²) − 5495507/200`. -/

theorem sum_cintegralSix_core :
    (∑' m : ℕ,
        (531441 : ℝ) * (Nat.choose (m + 12) 12 : ℝ) *
          (∑ i ∈ Finset.range 14,
            ((-1 : ℝ) ^ i * (Nat.choose 13 i : ℝ)) *
              (524880 / ((((3 * m + 7 + i : ℕ) : ℝ) * ((3 * m + 10 + i : ℕ) : ℝ) * ((3 * m + 13 + i : ℕ) : ℝ) * ((3 * m + 16 + i : ℕ) : ℝ) * ((3 * m + 19 + i : ℕ) : ℝ) * ((3 * m + 22 + i : ℕ) : ℝ) * ((3 * m + 25 + i : ℕ) : ℝ)))) ^ 2)) =
      35169 * (∑' k : ℕ,
          ((1 : ℝ) / (((3 * k + 1 : ℕ) : ℝ) ^ 2) - (1 : ℝ) / (((3 * k + 2 : ℕ) : ℝ) ^ 2))) - 5495507 / 200 := by
  have hMain := tsum_Vm6
  have hL : (∑' m : ℕ, Vm6 m) =
      (∑' m : ℕ,
        (531441 : ℝ) * (Nat.choose (m + 12) 12 : ℝ) *
          (∑ i ∈ Finset.range 14,
            ((-1 : ℝ) ^ i * (Nat.choose 13 i : ℝ)) *
              (524880 / ((((3 * m + 7 + i : ℕ) : ℝ) * ((3 * m + 10 + i : ℕ) : ℝ) * ((3 * m + 13 + i : ℕ) : ℝ) * ((3 * m + 16 + i : ℕ) : ℝ) * ((3 * m + 19 + i : ℕ) : ℝ) * ((3 * m + 22 + i : ℕ) : ℝ) * ((3 * m + 25 + i : ℕ) : ℝ)))) ^ 2)) := by
    apply tsum_congr
    intro m
    exact (vm6_eq_statement m).symm
  rw [← hL]
  rw [hMain]
  have hR : (∑' k : ℕ,
      ((1 : ℝ) / (((3 * k + 1 : ℕ) : ℝ) ^ 2) - (1 : ℝ) / (((3 * k + 2 : ℕ) : ℝ) ^ 2))) = A - B := by
    simpa [Rk, f1, f2, xm] using tsum_Rk
  rw [hR]
  ring

end Commons.Analysis.Summation