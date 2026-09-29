import Mathlib
import Submission.Commons.Analysis.Summation.sum_cintegralFour_core

noncomputable section
open scoped BigOperators Nat
open Filter Topology

namespace Commons.Analysis.Summation
namespace CdtSevenCore

/-! ## Binomial `(m+14 choose 14)` as a degree-14 polynomial -/

lemma asc14 (n : ℕ) : n.ascFactorial 14 =
    n * (n + 1) * (n + 2) * (n + 3) * (n + 4) * (n + 5) * (n + 6) * (n + 7) *
      (n + 8) * (n + 9) * (n + 10) * (n + 11) * (n + 12) * (n + 13) := by
  simp [Nat.ascFactorial_succ, Nat.ascFactorial_zero]
  ring

lemma factorial_add_fourteen (m : ℕ) : (m + 14)! =
    m ! * (m + 1) * (m + 2) * (m + 3) * (m + 4) * (m + 5) * (m + 6) * (m + 7) *
      (m + 8) * (m + 9) * (m + 10) * (m + 11) * (m + 12) * (m + 13) * (m + 14) := by
  rw [← Nat.factorial_mul_ascFactorial m 14]
  have h := asc14 (m + 1)
  rw [h]
  ring

lemma choose314 (m : ℕ) :
    (Nat.choose (m + 14) 14 : ℝ) =
      (1 / 87178291200 : ℝ) *
        (((m : ℝ) + 1) * ((m : ℝ) + 2) * ((m : ℝ) + 3) * ((m : ℝ) + 4) *
          ((m : ℝ) + 5) * ((m : ℝ) + 6) * ((m : ℝ) + 7) * ((m : ℝ) + 8) *
          ((m : ℝ) + 9) * ((m : ℝ) + 10) * ((m : ℝ) + 11) * ((m : ℝ) + 12) *
          ((m : ℝ) + 13) * ((m : ℝ) + 14)) := by
  have hcast := Nat.cast_choose ℝ (a := 14) (b := m + 14) (by omega : 14 ≤ m + 14)
  rw [hcast]
  have h14 : ((14 : ℕ)! : ℝ) = 87178291200 := by norm_num
  have hsub : ((m + 14 - 14) : ℕ) = m := by omega
  rw [h14, hsub]
  have hfacR : ((m + 14)! : ℝ) = (m ! : ℝ) *
      (((m : ℝ) + 1) * ((m : ℝ) + 2) * ((m : ℝ) + 3) * ((m : ℝ) + 4) *
        ((m : ℝ) + 5) * ((m : ℝ) + 6) * ((m : ℝ) + 7) * ((m : ℝ) + 8) *
        ((m : ℝ) + 9) * ((m : ℝ) + 10) * ((m : ℝ) + 11) * ((m : ℝ) + 12) *
        ((m : ℝ) + 13) * ((m : ℝ) + 14)) := by
    norm_num [factorial_add_fourteen, Nat.cast_mul]
    ring
  rw [hfacR]
  have hm : (m ! : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_ne_zero m)
  field_simp [hm]

@[simp] lemma c15_0 : (Nat.choose 15 0 : ℝ) = 1 := by
  rw [Nat.cast_choose ℝ (by decide : 0 ≤ 15)]; norm_num
@[simp] lemma c15_1 : (Nat.choose 15 1 : ℝ) = 15 := by
  rw [Nat.cast_choose ℝ (by decide : 1 ≤ 15)]; norm_num
@[simp] lemma c15_2 : (Nat.choose 15 2 : ℝ) = 105 := by
  rw [Nat.cast_choose ℝ (by decide : 2 ≤ 15)]; norm_num
@[simp] lemma c15_3 : (Nat.choose 15 3 : ℝ) = 455 := by
  rw [Nat.cast_choose ℝ (by decide : 3 ≤ 15)]; norm_num
@[simp] lemma c15_4 : (Nat.choose 15 4 : ℝ) = 1365 := by
  rw [Nat.cast_choose ℝ (by decide : 4 ≤ 15)]; norm_num
@[simp] lemma c15_5 : (Nat.choose 15 5 : ℝ) = 3003 := by
  rw [Nat.cast_choose ℝ (by decide : 5 ≤ 15)]; norm_num
@[simp] lemma c15_6 : (Nat.choose 15 6 : ℝ) = 5005 := by
  rw [Nat.cast_choose ℝ (by decide : 6 ≤ 15)]; norm_num
@[simp] lemma c15_7 : (Nat.choose 15 7 : ℝ) = 6435 := by
  rw [Nat.cast_choose ℝ (by decide : 7 ≤ 15)]; norm_num
@[simp] lemma c15_8 : (Nat.choose 15 8 : ℝ) = 6435 := by
  rw [Nat.cast_choose ℝ (by decide : 8 ≤ 15)]; norm_num
@[simp] lemma c15_9 : (Nat.choose 15 9 : ℝ) = 5005 := by
  rw [Nat.cast_choose ℝ (by decide : 9 ≤ 15)]; norm_num
@[simp] lemma c15_10 : (Nat.choose 15 10 : ℝ) = 3003 := by
  rw [Nat.cast_choose ℝ (by decide : 10 ≤ 15)]; norm_num
@[simp] lemma c15_11 : (Nat.choose 15 11 : ℝ) = 1365 := by
  rw [Nat.cast_choose ℝ (by decide : 11 ≤ 15)]; norm_num
@[simp] lemma c15_12 : (Nat.choose 15 12 : ℝ) = 455 := by
  rw [Nat.cast_choose ℝ (by decide : 12 ≤ 15)]; norm_num
@[simp] lemma c15_13 : (Nat.choose 15 13 : ℝ) = 105 := by
  rw [Nat.cast_choose ℝ (by decide : 13 ≤ 15)]; norm_num
@[simp] lemma c15_14 : (Nat.choose 15 14 : ℝ) = 15 := by
  rw [Nat.cast_choose ℝ (by decide : 14 ≤ 15)]; norm_num
@[simp] lemma c15_15 : (Nat.choose 15 15 : ℝ) = 1 := by
  rw [Nat.cast_choose ℝ (by decide : 15 ≤ 15)]; norm_num

/-! ## The `m`-summand and its pointwise closed-form decomposition -/

/-- The `m`-summand of the seven-core sum. -/
def Vm7 (m : ℕ) : ℝ :=
  (4782969 : ℝ) * (Nat.choose (m + 14) 14 : ℝ) *
    (∑ i ∈ Finset.range 16,
      ((-1 : ℝ) ^ i * (Nat.choose 15 i : ℝ)) *
        (11022480 / (xm m (8 + i) * xm m (11 + i) * xm m (14 + i) * xm m (17 + i) *
          xm m (20 + i) * xm m (23 + i) * xm m (26 + i) * xm m (29 + i))) ^ 2)

/-- Squared-term part of the closed-form decomposition. -/
def W17 (m : ℕ) : ℝ :=
  (-6349840/81 : ℝ) * (1 / (xm m 10)^2)
    + (13493410/27 : ℝ) * (1 / (xm m 13)^2)
    + (799784635/81 : ℝ) * (1 / (xm m 16)^2)
    + (-1532282080/27 : ℝ) * (1 / (xm m 19)^2)
    + (372806600/9 : ℝ) * (1 / (xm m 22)^2)
    + (5762610700/27 : ℝ) * (1 / (xm m 25)^2)
    + (-11374678700/27 : ℝ) * (1 / (xm m 28)^2)
    + (535165400/3 : ℝ) * (1 / (xm m 31)^2)
    + (3550727600/27 : ℝ) * (1 / (xm m 34)^2)
    + (-8984164250/81 : ℝ) * (1 / (xm m 37)^2)
    + (259336700/27 : ℝ) * (1 / (xm m 40)^2)
    + (370481000/81 : ℝ) * (1 / (xm m 43)^2)
    + (500650/243 : ℝ) * (1 / (xm m 8)^2)
    + (47826800/243 : ℝ) * (1 / (xm m 11)^2)
    + (-704288200/243 : ℝ) * (1 / (xm m 14)^2)
    + (-852929000/243 : ℝ) * (1 / (xm m 17)^2)
    + (6661946060/81 : ℝ) * (1 / (xm m 20)^2)
    + (-14596499200/81 : ℝ) * (1 / (xm m 23)^2)
    + (28712850400/81 : ℝ) * (1 / (xm m 29)^2)
    + (-26576064725/81 : ℝ) * (1 / (xm m 32)^2)
    + (7403913440/243 : ℝ) * (1 / (xm m 35)^2)
    + (15284064880/243 : ℝ) * (1 / (xm m 38)^2)
    + (-3498761840/243 : ℝ) * (1 / (xm m 41)^2)
    + (-353323240/243 : ℝ) * (1 / (xm m 44)^2)

/-- Telescoping-pair part of the closed-form decomposition. -/
def W27 (m : ℕ) : ℝ :=
  (-321206621/277992 : ℝ) * (1 / xm m 8 - 1 / xm m 11)
    + (-7971615/364 : ℝ) * (1 / xm m 9 - 1 / xm m 12)
    + (1136604679/7722 : ℝ) * (1 / xm m 10 - 1 / xm m 13)
    + (-133456527599/833976 : ℝ) * (1 / xm m 11 - 1 / xm m 14)
    + (-1092111255/4004 : ℝ) * (1 / xm m 12 - 1 / xm m 15)
    + (8040134305/138996 : ℝ) * (1 / xm m 13 - 1 / xm m 16)
    + (-467492804635/833976 : ℝ) * (1 / xm m 14 - 1 / xm m 17)
    + (33240040227/4004 : ℝ) * (1 / xm m 15 - 1 / xm m 18)
    + (-463133265547/30888 : ℝ) * (1 / xm m 16 - 1 / xm m 19)
    + (6123016249945/833976 : ℝ) * (1 / xm m 17 - 1 / xm m 20)
    + (-5715647955/364 : ℝ) * (1 / xm m 18 - 1 / xm m 21)
    + (10182984257549/277992 : ℝ) * (1 / xm m 19 - 1 / xm m 22)
    + (4299411293357/277992 : ℝ) * (1 / xm m 20 - 1 / xm m 23)
    + (-676871423973/8008 : ℝ) * (1 / xm m 21 - 1 / xm m 24)
    + (14973547145729/277992 : ℝ) * (1 / xm m 22 - 1 / xm m 25)
    + (-534224141780431/5837832 : ℝ) * (1 / xm m 23 - 1 / xm m 26)
    + (963112986747/4004 : ℝ) * (1 / xm m 24 - 1 / xm m 27)
    + (-5717548972133/30888 : ℝ) * (1 / xm m 25 - 1 / xm m 28)
    + (154960952641393/5837832 : ℝ) * (1 / xm m 26 - 1 / xm m 29)
    + (-329803250103/4004 : ℝ) * (1 / xm m 27 - 1 / xm m 30)
    + (18668744141681/277992 : ℝ) * (1 / xm m 28 - 1 / xm m 31)
    + (318458249027339/1945944 : ℝ) * (1 / xm m 29 - 1 / xm m 32)
    + (-826648503885/4004 : ℝ) * (1 / xm m 30 - 1 / xm m 33)
    + (25125471211397/277992 : ℝ) * (1 / xm m 31 - 1 / xm m 34)
    + (-351391212664319/2918916 : ℝ) * (1 / xm m 32 - 1 / xm m 35)
    + (52649328429/364 : ℝ) * (1 / xm m 33 - 1 / xm m 36)
    + (-383183987561/10296 : ℝ) * (1 / xm m 34 - 1 / xm m 37)
    + (-68265498887875/2918916 : ℝ) * (1 / xm m 35 - 1 / xm m 38)
    + (176969853/26 : ℝ) * (1 / xm m 36 - 1 / xm m 39)
    + (-1510803088841/138996 : ℝ) * (1 / xm m 37 - 1 / xm m 40)
    + (65677891960987/2918916 : ℝ) * (1 / xm m 38 - 1 / xm m 41)
    + (-23914845/2 : ℝ) * (1 / xm m 39 - 1 / xm m 42)
    + (20259728465/23166 : ℝ) * (1 / xm m 40 - 1 / xm m 43)
    + (191202368069/324324 : ℝ) * (1 / xm m 41 - 1 / xm m 44)

set_option maxHeartbeats 0 in
lemma vm7_decomp (m : ℕ) : Vm7 m = W17 m + W27 m := by
  unfold Vm7 W17 W27
  rw [choose314]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero,
    c15_0, c15_1, c15_2, c15_3, c15_4, c15_5, c15_6, c15_7, c15_8, c15_9, c15_10, c15_11, c15_12, c15_13, c15_14, c15_15]
  norm_num
  simp_rw [xm_eq]
  norm_num
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
  have h39 : (3 * (m : ℝ) + 39) ≠ 0 := by positivity
  have h40 : (3 * (m : ℝ) + 40) ≠ 0 := by positivity
  have h41 : (3 * (m : ℝ) + 41) ≠ 0 := by positivity
  have h42 : (3 * (m : ℝ) + 42) ≠ 0 := by positivity
  have h43 : (3 * (m : ℝ) + 43) ≠ 0 := by positivity
  have h44 : (3 * (m : ℝ) + 44) ≠ 0 := by positivity
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
  have hm13 : (m : ℝ) + 13 ≠ 0 := by positivity
  have hm14 : (m : ℝ) + 14 ≠ 0 := by positivity
  field_simp
  ring

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
@[simp] lemma asum13 : Asum 13 = 24493235278827913928641 / 22004931353582937760000 := by norm_num [Asum, f1, xm]
@[simp] lemma asum14 : Asum 14 = 24506988360923903264741 / 22004931353582937760000 := by norm_num [Asum, f1, xm]
@[simp] lemma bsum1 : Bsum 1 = 1 / 4 := by norm_num [Bsum, f2, xm]
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
@[simp] lemma bsum13 : Bsum 13 = 395273284628034202009 / 1190597133946533913600 := by norm_num [Bsum, f2, xm]
@[simp] lemma bsum14 : Bsum 14 = 665644988593672027490729 / 2001393782164123508761600 := by norm_num [Bsum, f2, xm]

/-! ## The statement denominators equal the `xm` denominators -/

lemma denom_statement7 (m : ℕ) : ∀ i : ℕ,
    ((((3 * m + 8 + i : ℕ) : ℝ) * ((3 * m + 11 + i : ℕ) : ℝ) *
        ((3 * m + 14 + i : ℕ) : ℝ) * ((3 * m + 17 + i : ℕ) : ℝ) *
          ((3 * m + 20 + i : ℕ) : ℝ) * ((3 * m + 23 + i : ℕ) : ℝ) *
            ((3 * m + 26 + i : ℕ) : ℝ) * ((3 * m + 29 + i : ℕ) : ℝ)))
      = xm m (8 + i) * xm m (11 + i) * xm m (14 + i) * xm m (17 + i) *
          xm m (20 + i) * xm m (23 + i) * xm m (26 + i) * xm m (29 + i) := by
  intro i
  have h8 : (((3 * m + 8 + i : ℕ) : ℝ)) = xm m (8 + i) := by
    unfold xm
    congr 1
    omega
  have h11 : (((3 * m + 11 + i : ℕ) : ℝ)) = xm m (11 + i) := by
    unfold xm
    congr 1
    omega
  have h14 : (((3 * m + 14 + i : ℕ) : ℝ)) = xm m (14 + i) := by
    unfold xm
    congr 1
    omega
  have h17 : (((3 * m + 17 + i : ℕ) : ℝ)) = xm m (17 + i) := by
    unfold xm
    congr 1
    omega
  have h20 : (((3 * m + 20 + i : ℕ) : ℝ)) = xm m (20 + i) := by
    unfold xm
    congr 1
    omega
  have h23 : (((3 * m + 23 + i : ℕ) : ℝ)) = xm m (23 + i) := by
    unfold xm
    congr 1
    omega
  have h26 : (((3 * m + 26 + i : ℕ) : ℝ)) = xm m (26 + i) := by
    unfold xm
    congr 1
    omega
  have h29 : (((3 * m + 29 + i : ℕ) : ℝ)) = xm m (29 + i) := by
    unfold xm
    congr 1
    omega
  rw [h8, h11, h14, h17, h20, h23, h26, h29]

/-- The inner `i`-sum in the statement's form equals the `xm` form. -/
lemma inner_sum_statement7 (m : ℕ) :
    (∑ i ∈ Finset.range 16,
      ((-1 : ℝ) ^ i * (Nat.choose 15 i : ℝ)) *
        (11022480 / ((((3 * m + 8 + i : ℕ) : ℝ) * ((3 * m + 11 + i : ℕ) : ℝ) *
          ((3 * m + 14 + i : ℕ) : ℝ) * ((3 * m + 17 + i : ℕ) : ℝ) *
            ((3 * m + 20 + i : ℕ) : ℝ) * ((3 * m + 23 + i : ℕ) : ℝ) *
              ((3 * m + 26 + i : ℕ) : ℝ) * ((3 * m + 29 + i : ℕ) : ℝ)))) ^ 2)
    = (∑ i ∈ Finset.range 16,
      ((-1 : ℝ) ^ i * (Nat.choose 15 i : ℝ)) *
        (11022480 / (xm m (8 + i) * xm m (11 + i) * xm m (14 + i) * xm m (17 + i) *
          xm m (20 + i) * xm m (23 + i) * xm m (26 + i) * xm m (29 + i))) ^ 2) := by
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  rw [denom_statement7 m i]

/-- The `m`-summand of the seven-core sum, in the statement's form. -/
lemma vm7_eq_statement (m : ℕ) :
    ((4782969 : ℝ) * (Nat.choose (m + 14) 14 : ℝ) *
      (∑ i ∈ Finset.range 16,
        ((-1 : ℝ) ^ i * (Nat.choose 15 i : ℝ)) *
          (11022480 / ((((3 * m + 8 + i : ℕ) : ℝ) * ((3 * m + 11 + i : ℕ) : ℝ) *
            ((3 * m + 14 + i : ℕ) : ℝ) * ((3 * m + 17 + i : ℕ) : ℝ) *
              ((3 * m + 20 + i : ℕ) : ℝ) * ((3 * m + 23 + i : ℕ) : ℝ) *
                ((3 * m + 26 + i : ℕ) : ℝ) * ((3 * m + 29 + i : ℕ) : ℝ)))) ^ 2)) =
      Vm7 m := by
  unfold Vm7
  rw [inner_sum_statement7 m]

/-! ## The values of the two pieces -/

/-- The value of the `W17`-sum. -/
noncomputable def V1val7 : ℝ :=
  (-6349840/81 : ℝ) * (A - Asum 3)
    + (13493410/27 : ℝ) * (A - Asum 4)
    + (799784635/81 : ℝ) * (A - Asum 5)
    + (-1532282080/27 : ℝ) * (A - Asum 6)
    + (372806600/9 : ℝ) * (A - Asum 7)
    + (5762610700/27 : ℝ) * (A - Asum 8)
    + (-11374678700/27 : ℝ) * (A - Asum 9)
    + (535165400/3 : ℝ) * (A - Asum 10)
    + (3550727600/27 : ℝ) * (A - Asum 11)
    + (-8984164250/81 : ℝ) * (A - Asum 12)
    + (259336700/27 : ℝ) * (A - Asum 13)
    + (370481000/81 : ℝ) * (A - Asum 14)
    + (500650/243 : ℝ) * (B - Bsum 2)
    + (47826800/243 : ℝ) * (B - Bsum 3)
    + (-704288200/243 : ℝ) * (B - Bsum 4)
    + (-852929000/243 : ℝ) * (B - Bsum 5)
    + (6661946060/81 : ℝ) * (B - Bsum 6)
    + (-14596499200/81 : ℝ) * (B - Bsum 7)
    + (28712850400/81 : ℝ) * (B - Bsum 9)
    + (-26576064725/81 : ℝ) * (B - Bsum 10)
    + (7403913440/243 : ℝ) * (B - Bsum 11)
    + (15284064880/243 : ℝ) * (B - Bsum 12)
    + (-3498761840/243 : ℝ) * (B - Bsum 13)
    + (-353323240/243 : ℝ) * (B - Bsum 14)

/-- The value of the `W27`-sum. -/
noncomputable def V2val7 : ℝ :=
  (-321206621/277992 : ℝ) * (1 / xm 0 8)
    + (-7971615/364 : ℝ) * (1 / xm 0 9)
    + (1136604679/7722 : ℝ) * (1 / xm 0 10)
    + (-133456527599/833976 : ℝ) * (1 / xm 0 11)
    + (-1092111255/4004 : ℝ) * (1 / xm 0 12)
    + (8040134305/138996 : ℝ) * (1 / xm 0 13)
    + (-467492804635/833976 : ℝ) * (1 / xm 0 14)
    + (33240040227/4004 : ℝ) * (1 / xm 0 15)
    + (-463133265547/30888 : ℝ) * (1 / xm 0 16)
    + (6123016249945/833976 : ℝ) * (1 / xm 0 17)
    + (-5715647955/364 : ℝ) * (1 / xm 0 18)
    + (10182984257549/277992 : ℝ) * (1 / xm 0 19)
    + (4299411293357/277992 : ℝ) * (1 / xm 0 20)
    + (-676871423973/8008 : ℝ) * (1 / xm 0 21)
    + (14973547145729/277992 : ℝ) * (1 / xm 0 22)
    + (-534224141780431/5837832 : ℝ) * (1 / xm 0 23)
    + (963112986747/4004 : ℝ) * (1 / xm 0 24)
    + (-5717548972133/30888 : ℝ) * (1 / xm 0 25)
    + (154960952641393/5837832 : ℝ) * (1 / xm 0 26)
    + (-329803250103/4004 : ℝ) * (1 / xm 0 27)
    + (18668744141681/277992 : ℝ) * (1 / xm 0 28)
    + (318458249027339/1945944 : ℝ) * (1 / xm 0 29)
    + (-826648503885/4004 : ℝ) * (1 / xm 0 30)
    + (25125471211397/277992 : ℝ) * (1 / xm 0 31)
    + (-351391212664319/2918916 : ℝ) * (1 / xm 0 32)
    + (52649328429/364 : ℝ) * (1 / xm 0 33)
    + (-383183987561/10296 : ℝ) * (1 / xm 0 34)
    + (-68265498887875/2918916 : ℝ) * (1 / xm 0 35)
    + (176969853/26 : ℝ) * (1 / xm 0 36)
    + (-1510803088841/138996 : ℝ) * (1 / xm 0 37)
    + (65677891960987/2918916 : ℝ) * (1 / xm 0 38)
    + (-23914845/2 : ℝ) * (1 / xm 0 39)
    + (20259728465/23166 : ℝ) * (1 / xm 0 40)
    + (191202368069/324324 : ℝ) * (1 / xm 0 41)

/-- The value of the whole sum. -/
noncomputable def Vval7 : ℝ := V1val7 + V2val7

/-! ## `HasSum` of the two pieces of the decomposition -/

lemma hasSum_W17 : HasSum W17 V1val7 := by
  have hsq1_10 : HasSum (fun m : ℕ => (-6349840/81 : ℝ) * (1 / (xm m 10)^2))
      ((-6349840/81 : ℝ) * (A - Asum 3)) := by
    simpa using (CdtTwoCore.hasSum_sq1 3).mul_left (-6349840/81 : ℝ)
  have hsq1_13 : HasSum (fun m : ℕ => (13493410/27 : ℝ) * (1 / (xm m 13)^2))
      ((13493410/27 : ℝ) * (A - Asum 4)) := by
    simpa using (CdtTwoCore.hasSum_sq1 4).mul_left (13493410/27 : ℝ)
  have hsq1_16 : HasSum (fun m : ℕ => (799784635/81 : ℝ) * (1 / (xm m 16)^2))
      ((799784635/81 : ℝ) * (A - Asum 5)) := by
    simpa using (CdtTwoCore.hasSum_sq1 5).mul_left (799784635/81 : ℝ)
  have hsq1_19 : HasSum (fun m : ℕ => (-1532282080/27 : ℝ) * (1 / (xm m 19)^2))
      ((-1532282080/27 : ℝ) * (A - Asum 6)) := by
    simpa using (CdtTwoCore.hasSum_sq1 6).mul_left (-1532282080/27 : ℝ)
  have hsq1_22 : HasSum (fun m : ℕ => (372806600/9 : ℝ) * (1 / (xm m 22)^2))
      ((372806600/9 : ℝ) * (A - Asum 7)) := by
    simpa using (CdtTwoCore.hasSum_sq1 7).mul_left (372806600/9 : ℝ)
  have hsq1_25 : HasSum (fun m : ℕ => (5762610700/27 : ℝ) * (1 / (xm m 25)^2))
      ((5762610700/27 : ℝ) * (A - Asum 8)) := by
    simpa using (CdtTwoCore.hasSum_sq1 8).mul_left (5762610700/27 : ℝ)
  have hsq1_28 : HasSum (fun m : ℕ => (-11374678700/27 : ℝ) * (1 / (xm m 28)^2))
      ((-11374678700/27 : ℝ) * (A - Asum 9)) := by
    simpa using (CdtTwoCore.hasSum_sq1 9).mul_left (-11374678700/27 : ℝ)
  have hsq1_31 : HasSum (fun m : ℕ => (535165400/3 : ℝ) * (1 / (xm m 31)^2))
      ((535165400/3 : ℝ) * (A - Asum 10)) := by
    simpa using (CdtTwoCore.hasSum_sq1 10).mul_left (535165400/3 : ℝ)
  have hsq1_34 : HasSum (fun m : ℕ => (3550727600/27 : ℝ) * (1 / (xm m 34)^2))
      ((3550727600/27 : ℝ) * (A - Asum 11)) := by
    simpa using (CdtTwoCore.hasSum_sq1 11).mul_left (3550727600/27 : ℝ)
  have hsq1_37 : HasSum (fun m : ℕ => (-8984164250/81 : ℝ) * (1 / (xm m 37)^2))
      ((-8984164250/81 : ℝ) * (A - Asum 12)) := by
    simpa using (CdtTwoCore.hasSum_sq1 12).mul_left (-8984164250/81 : ℝ)
  have hsq1_40 : HasSum (fun m : ℕ => (259336700/27 : ℝ) * (1 / (xm m 40)^2))
      ((259336700/27 : ℝ) * (A - Asum 13)) := by
    simpa using (CdtTwoCore.hasSum_sq1 13).mul_left (259336700/27 : ℝ)
  have hsq1_43 : HasSum (fun m : ℕ => (370481000/81 : ℝ) * (1 / (xm m 43)^2))
      ((370481000/81 : ℝ) * (A - Asum 14)) := by
    simpa using (CdtTwoCore.hasSum_sq1 14).mul_left (370481000/81 : ℝ)
  have hsq2_8 : HasSum (fun m : ℕ => (500650/243 : ℝ) * (1 / (xm m 8)^2))
      ((500650/243 : ℝ) * (B - Bsum 2)) := by
    simpa using (CdtTwoCore.hasSum_sq2 2).mul_left (500650/243 : ℝ)
  have hsq2_11 : HasSum (fun m : ℕ => (47826800/243 : ℝ) * (1 / (xm m 11)^2))
      ((47826800/243 : ℝ) * (B - Bsum 3)) := by
    simpa using (CdtTwoCore.hasSum_sq2 3).mul_left (47826800/243 : ℝ)
  have hsq2_14 : HasSum (fun m : ℕ => (-704288200/243 : ℝ) * (1 / (xm m 14)^2))
      ((-704288200/243 : ℝ) * (B - Bsum 4)) := by
    simpa using (CdtTwoCore.hasSum_sq2 4).mul_left (-704288200/243 : ℝ)
  have hsq2_17 : HasSum (fun m : ℕ => (-852929000/243 : ℝ) * (1 / (xm m 17)^2))
      ((-852929000/243 : ℝ) * (B - Bsum 5)) := by
    simpa using (CdtTwoCore.hasSum_sq2 5).mul_left (-852929000/243 : ℝ)
  have hsq2_20 : HasSum (fun m : ℕ => (6661946060/81 : ℝ) * (1 / (xm m 20)^2))
      ((6661946060/81 : ℝ) * (B - Bsum 6)) := by
    simpa using (CdtTwoCore.hasSum_sq2 6).mul_left (6661946060/81 : ℝ)
  have hsq2_23 : HasSum (fun m : ℕ => (-14596499200/81 : ℝ) * (1 / (xm m 23)^2))
      ((-14596499200/81 : ℝ) * (B - Bsum 7)) := by
    simpa using (CdtTwoCore.hasSum_sq2 7).mul_left (-14596499200/81 : ℝ)
  have hsq2_29 : HasSum (fun m : ℕ => (28712850400/81 : ℝ) * (1 / (xm m 29)^2))
      ((28712850400/81 : ℝ) * (B - Bsum 9)) := by
    simpa using (CdtTwoCore.hasSum_sq2 9).mul_left (28712850400/81 : ℝ)
  have hsq2_32 : HasSum (fun m : ℕ => (-26576064725/81 : ℝ) * (1 / (xm m 32)^2))
      ((-26576064725/81 : ℝ) * (B - Bsum 10)) := by
    simpa using (CdtTwoCore.hasSum_sq2 10).mul_left (-26576064725/81 : ℝ)
  have hsq2_35 : HasSum (fun m : ℕ => (7403913440/243 : ℝ) * (1 / (xm m 35)^2))
      ((7403913440/243 : ℝ) * (B - Bsum 11)) := by
    simpa using (CdtTwoCore.hasSum_sq2 11).mul_left (7403913440/243 : ℝ)
  have hsq2_38 : HasSum (fun m : ℕ => (15284064880/243 : ℝ) * (1 / (xm m 38)^2))
      ((15284064880/243 : ℝ) * (B - Bsum 12)) := by
    simpa using (CdtTwoCore.hasSum_sq2 12).mul_left (15284064880/243 : ℝ)
  have hsq2_41 : HasSum (fun m : ℕ => (-3498761840/243 : ℝ) * (1 / (xm m 41)^2))
      ((-3498761840/243 : ℝ) * (B - Bsum 13)) := by
    simpa using (CdtTwoCore.hasSum_sq2 13).mul_left (-3498761840/243 : ℝ)
  have hsq2_44 : HasSum (fun m : ℕ => (-353323240/243 : ℝ) * (1 / (xm m 44)^2))
      ((-353323240/243 : ℝ) * (B - Bsum 14)) := by
    simpa using (CdtTwoCore.hasSum_sq2 14).mul_left (-353323240/243 : ℝ)
  exact (((((((((((((((((((((((hsq1_10).add hsq1_13).add hsq1_16).add hsq1_19).add hsq1_22).add hsq1_25).add hsq1_28).add hsq1_31).add hsq1_34).add hsq1_37).add hsq1_40).add hsq1_43).add hsq2_8).add hsq2_11).add hsq2_14).add hsq2_17).add hsq2_20).add hsq2_23).add hsq2_29).add hsq2_32).add hsq2_35).add hsq2_38).add hsq2_41).add hsq2_44

lemma hasSum_W27 : HasSum W27 V2val7 := by
  have hp8 : HasSum (fun m : ℕ => (-321206621/277992 : ℝ) * (1 / xm m 8 - 1 / xm m 11))
      ((-321206621/277992 : ℝ) * (1 / xm 0 8)) := by
    simpa using (CdtTwoCore.hasSum_pair 8 (by norm_num)).mul_left (-321206621/277992 : ℝ)
  have hp9 : HasSum (fun m : ℕ => (-7971615/364 : ℝ) * (1 / xm m 9 - 1 / xm m 12))
      ((-7971615/364 : ℝ) * (1 / xm 0 9)) := by
    simpa using (CdtTwoCore.hasSum_pair 9 (by norm_num)).mul_left (-7971615/364 : ℝ)
  have hp10 : HasSum (fun m : ℕ => (1136604679/7722 : ℝ) * (1 / xm m 10 - 1 / xm m 13))
      ((1136604679/7722 : ℝ) * (1 / xm 0 10)) := by
    simpa using (CdtTwoCore.hasSum_pair 10 (by norm_num)).mul_left (1136604679/7722 : ℝ)
  have hp11 : HasSum (fun m : ℕ => (-133456527599/833976 : ℝ) * (1 / xm m 11 - 1 / xm m 14))
      ((-133456527599/833976 : ℝ) * (1 / xm 0 11)) := by
    simpa using (CdtTwoCore.hasSum_pair 11 (by norm_num)).mul_left (-133456527599/833976 : ℝ)
  have hp12 : HasSum (fun m : ℕ => (-1092111255/4004 : ℝ) * (1 / xm m 12 - 1 / xm m 15))
      ((-1092111255/4004 : ℝ) * (1 / xm 0 12)) := by
    simpa using (CdtTwoCore.hasSum_pair 12 (by norm_num)).mul_left (-1092111255/4004 : ℝ)
  have hp13 : HasSum (fun m : ℕ => (8040134305/138996 : ℝ) * (1 / xm m 13 - 1 / xm m 16))
      ((8040134305/138996 : ℝ) * (1 / xm 0 13)) := by
    simpa using (CdtTwoCore.hasSum_pair 13 (by norm_num)).mul_left (8040134305/138996 : ℝ)
  have hp14 : HasSum (fun m : ℕ => (-467492804635/833976 : ℝ) * (1 / xm m 14 - 1 / xm m 17))
      ((-467492804635/833976 : ℝ) * (1 / xm 0 14)) := by
    simpa using (CdtTwoCore.hasSum_pair 14 (by norm_num)).mul_left (-467492804635/833976 : ℝ)
  have hp15 : HasSum (fun m : ℕ => (33240040227/4004 : ℝ) * (1 / xm m 15 - 1 / xm m 18))
      ((33240040227/4004 : ℝ) * (1 / xm 0 15)) := by
    simpa using (CdtTwoCore.hasSum_pair 15 (by norm_num)).mul_left (33240040227/4004 : ℝ)
  have hp16 : HasSum (fun m : ℕ => (-463133265547/30888 : ℝ) * (1 / xm m 16 - 1 / xm m 19))
      ((-463133265547/30888 : ℝ) * (1 / xm 0 16)) := by
    simpa using (CdtTwoCore.hasSum_pair 16 (by norm_num)).mul_left (-463133265547/30888 : ℝ)
  have hp17 : HasSum (fun m : ℕ => (6123016249945/833976 : ℝ) * (1 / xm m 17 - 1 / xm m 20))
      ((6123016249945/833976 : ℝ) * (1 / xm 0 17)) := by
    simpa using (CdtTwoCore.hasSum_pair 17 (by norm_num)).mul_left (6123016249945/833976 : ℝ)
  have hp18 : HasSum (fun m : ℕ => (-5715647955/364 : ℝ) * (1 / xm m 18 - 1 / xm m 21))
      ((-5715647955/364 : ℝ) * (1 / xm 0 18)) := by
    simpa using (CdtTwoCore.hasSum_pair 18 (by norm_num)).mul_left (-5715647955/364 : ℝ)
  have hp19 : HasSum (fun m : ℕ => (10182984257549/277992 : ℝ) * (1 / xm m 19 - 1 / xm m 22))
      ((10182984257549/277992 : ℝ) * (1 / xm 0 19)) := by
    simpa using (CdtTwoCore.hasSum_pair 19 (by norm_num)).mul_left (10182984257549/277992 : ℝ)
  have hp20 : HasSum (fun m : ℕ => (4299411293357/277992 : ℝ) * (1 / xm m 20 - 1 / xm m 23))
      ((4299411293357/277992 : ℝ) * (1 / xm 0 20)) := by
    simpa using (CdtTwoCore.hasSum_pair 20 (by norm_num)).mul_left (4299411293357/277992 : ℝ)
  have hp21 : HasSum (fun m : ℕ => (-676871423973/8008 : ℝ) * (1 / xm m 21 - 1 / xm m 24))
      ((-676871423973/8008 : ℝ) * (1 / xm 0 21)) := by
    simpa using (CdtTwoCore.hasSum_pair 21 (by norm_num)).mul_left (-676871423973/8008 : ℝ)
  have hp22 : HasSum (fun m : ℕ => (14973547145729/277992 : ℝ) * (1 / xm m 22 - 1 / xm m 25))
      ((14973547145729/277992 : ℝ) * (1 / xm 0 22)) := by
    simpa using (CdtTwoCore.hasSum_pair 22 (by norm_num)).mul_left (14973547145729/277992 : ℝ)
  have hp23 : HasSum (fun m : ℕ => (-534224141780431/5837832 : ℝ) * (1 / xm m 23 - 1 / xm m 26))
      ((-534224141780431/5837832 : ℝ) * (1 / xm 0 23)) := by
    simpa using (CdtTwoCore.hasSum_pair 23 (by norm_num)).mul_left (-534224141780431/5837832 : ℝ)
  have hp24 : HasSum (fun m : ℕ => (963112986747/4004 : ℝ) * (1 / xm m 24 - 1 / xm m 27))
      ((963112986747/4004 : ℝ) * (1 / xm 0 24)) := by
    simpa using (CdtTwoCore.hasSum_pair 24 (by norm_num)).mul_left (963112986747/4004 : ℝ)
  have hp25 : HasSum (fun m : ℕ => (-5717548972133/30888 : ℝ) * (1 / xm m 25 - 1 / xm m 28))
      ((-5717548972133/30888 : ℝ) * (1 / xm 0 25)) := by
    simpa using (CdtTwoCore.hasSum_pair 25 (by norm_num)).mul_left (-5717548972133/30888 : ℝ)
  have hp26 : HasSum (fun m : ℕ => (154960952641393/5837832 : ℝ) * (1 / xm m 26 - 1 / xm m 29))
      ((154960952641393/5837832 : ℝ) * (1 / xm 0 26)) := by
    simpa using (CdtTwoCore.hasSum_pair 26 (by norm_num)).mul_left (154960952641393/5837832 : ℝ)
  have hp27 : HasSum (fun m : ℕ => (-329803250103/4004 : ℝ) * (1 / xm m 27 - 1 / xm m 30))
      ((-329803250103/4004 : ℝ) * (1 / xm 0 27)) := by
    simpa using (CdtTwoCore.hasSum_pair 27 (by norm_num)).mul_left (-329803250103/4004 : ℝ)
  have hp28 : HasSum (fun m : ℕ => (18668744141681/277992 : ℝ) * (1 / xm m 28 - 1 / xm m 31))
      ((18668744141681/277992 : ℝ) * (1 / xm 0 28)) := by
    simpa using (CdtTwoCore.hasSum_pair 28 (by norm_num)).mul_left (18668744141681/277992 : ℝ)
  have hp29 : HasSum (fun m : ℕ => (318458249027339/1945944 : ℝ) * (1 / xm m 29 - 1 / xm m 32))
      ((318458249027339/1945944 : ℝ) * (1 / xm 0 29)) := by
    simpa using (CdtTwoCore.hasSum_pair 29 (by norm_num)).mul_left (318458249027339/1945944 : ℝ)
  have hp30 : HasSum (fun m : ℕ => (-826648503885/4004 : ℝ) * (1 / xm m 30 - 1 / xm m 33))
      ((-826648503885/4004 : ℝ) * (1 / xm 0 30)) := by
    simpa using (CdtTwoCore.hasSum_pair 30 (by norm_num)).mul_left (-826648503885/4004 : ℝ)
  have hp31 : HasSum (fun m : ℕ => (25125471211397/277992 : ℝ) * (1 / xm m 31 - 1 / xm m 34))
      ((25125471211397/277992 : ℝ) * (1 / xm 0 31)) := by
    simpa using (CdtTwoCore.hasSum_pair 31 (by norm_num)).mul_left (25125471211397/277992 : ℝ)
  have hp32 : HasSum (fun m : ℕ => (-351391212664319/2918916 : ℝ) * (1 / xm m 32 - 1 / xm m 35))
      ((-351391212664319/2918916 : ℝ) * (1 / xm 0 32)) := by
    simpa using (CdtTwoCore.hasSum_pair 32 (by norm_num)).mul_left (-351391212664319/2918916 : ℝ)
  have hp33 : HasSum (fun m : ℕ => (52649328429/364 : ℝ) * (1 / xm m 33 - 1 / xm m 36))
      ((52649328429/364 : ℝ) * (1 / xm 0 33)) := by
    simpa using (CdtTwoCore.hasSum_pair 33 (by norm_num)).mul_left (52649328429/364 : ℝ)
  have hp34 : HasSum (fun m : ℕ => (-383183987561/10296 : ℝ) * (1 / xm m 34 - 1 / xm m 37))
      ((-383183987561/10296 : ℝ) * (1 / xm 0 34)) := by
    simpa using (CdtTwoCore.hasSum_pair 34 (by norm_num)).mul_left (-383183987561/10296 : ℝ)
  have hp35 : HasSum (fun m : ℕ => (-68265498887875/2918916 : ℝ) * (1 / xm m 35 - 1 / xm m 38))
      ((-68265498887875/2918916 : ℝ) * (1 / xm 0 35)) := by
    simpa using (CdtTwoCore.hasSum_pair 35 (by norm_num)).mul_left (-68265498887875/2918916 : ℝ)
  have hp36 : HasSum (fun m : ℕ => (176969853/26 : ℝ) * (1 / xm m 36 - 1 / xm m 39))
      ((176969853/26 : ℝ) * (1 / xm 0 36)) := by
    simpa using (CdtTwoCore.hasSum_pair 36 (by norm_num)).mul_left (176969853/26 : ℝ)
  have hp37 : HasSum (fun m : ℕ => (-1510803088841/138996 : ℝ) * (1 / xm m 37 - 1 / xm m 40))
      ((-1510803088841/138996 : ℝ) * (1 / xm 0 37)) := by
    simpa using (CdtTwoCore.hasSum_pair 37 (by norm_num)).mul_left (-1510803088841/138996 : ℝ)
  have hp38 : HasSum (fun m : ℕ => (65677891960987/2918916 : ℝ) * (1 / xm m 38 - 1 / xm m 41))
      ((65677891960987/2918916 : ℝ) * (1 / xm 0 38)) := by
    simpa using (CdtTwoCore.hasSum_pair 38 (by norm_num)).mul_left (65677891960987/2918916 : ℝ)
  have hp39 : HasSum (fun m : ℕ => (-23914845/2 : ℝ) * (1 / xm m 39 - 1 / xm m 42))
      ((-23914845/2 : ℝ) * (1 / xm 0 39)) := by
    simpa using (CdtTwoCore.hasSum_pair 39 (by norm_num)).mul_left (-23914845/2 : ℝ)
  have hp40 : HasSum (fun m : ℕ => (20259728465/23166 : ℝ) * (1 / xm m 40 - 1 / xm m 43))
      ((20259728465/23166 : ℝ) * (1 / xm 0 40)) := by
    simpa using (CdtTwoCore.hasSum_pair 40 (by norm_num)).mul_left (20259728465/23166 : ℝ)
  have hp41 : HasSum (fun m : ℕ => (191202368069/324324 : ℝ) * (1 / xm m 41 - 1 / xm m 44))
      ((191202368069/324324 : ℝ) * (1 / xm 0 41)) := by
    simpa using (CdtTwoCore.hasSum_pair 41 (by norm_num)).mul_left (191202368069/324324 : ℝ)
  exact (((((((((((((((((((((((((((((((((hp8).add hp9).add hp10).add hp11).add hp12).add hp13).add hp14).add hp15).add hp16).add hp17).add hp18).add hp19).add hp20).add hp21).add hp22).add hp23).add hp24).add hp25).add hp26).add hp27).add hp28).add hp29).add hp30).add hp31).add hp32).add hp33).add hp34).add hp35).add hp36).add hp37).add hp38).add hp39).add hp40).add hp41

/-- `HasSum` for the whole summand. -/
lemma hasSum_Vm7 : HasSum Vm7 Vval7 := by
  have hsum : HasSum (fun m : ℕ => W17 m + W27 m) Vval7 := by
    simpa [Vval7] using hasSum_W17.add hasSum_W27
  apply HasSum.congr_fun hsum
  intro m
  exact vm7_decomp m

/-- The infinite sum of `Vm7` in closed form. -/
lemma tsum_Vm7 : (∑' m : ℕ, Vm7 m) = 272835 * A - 272835 * B - 417806469 / 1960 := by
  have hval : Vval7 = 272835 * A - 272835 * B - 417806469 / 1960 := by
    unfold Vval7 V1val7 V2val7
    norm_num [xm]
    ring
  rw [hasSum_Vm7.tsum_eq]
  exact hval

end CdtSevenCore
open CdtSevenCore


/-! ## Final assembly -/

/-- Creative-telescoping evaluation of the degree-7 `(Cintegral)` inner sum:
`Σₘ 4782969·C(m+14,14)·Σᵢ₌₀¹⁵(−1)ⁱC(15,i)·(11022480/∏_{k=0}^{7}(3m+8+3k+i))²
 = 272835·Σₖ(1/(3k+1)²−1/(3k+2)²) − 417806469/1960`. -/
theorem sum_cintegralSeven_core :
    (∑' m : ℕ,
        (4782969 : ℝ) * (Nat.choose (m + 14) 14 : ℝ) *
          (∑ i ∈ Finset.range 16,
            ((-1 : ℝ) ^ i * (Nat.choose 15 i : ℝ)) *
              (11022480 / ((((3 * m + 8 + i : ℕ) : ℝ) * ((3 * m + 11 + i : ℕ) : ℝ) * ((3 * m + 14 + i : ℕ) : ℝ) * ((3 * m + 17 + i : ℕ) : ℝ) * ((3 * m + 20 + i : ℕ) : ℝ) * ((3 * m + 23 + i : ℕ) : ℝ) * ((3 * m + 26 + i : ℕ) : ℝ) * ((3 * m + 29 + i : ℕ) : ℝ)))) ^ 2)) =
      272835 * (∑' k : ℕ,
          ((1 : ℝ) / (((3 * k + 1 : ℕ) : ℝ) ^ 2) - (1 : ℝ) / (((3 * k + 2 : ℕ) : ℝ) ^ 2))) - 417806469 / 1960 := by
  have hMain := tsum_Vm7
  have hL : (∑' m : ℕ, Vm7 m) =
      (∑' m : ℕ,
        (4782969 : ℝ) * (Nat.choose (m + 14) 14 : ℝ) *
          (∑ i ∈ Finset.range 16,
            ((-1 : ℝ) ^ i * (Nat.choose 15 i : ℝ)) *
              (11022480 / ((((3 * m + 8 + i : ℕ) : ℝ) * ((3 * m + 11 + i : ℕ) : ℝ) * ((3 * m + 14 + i : ℕ) : ℝ) * ((3 * m + 17 + i : ℕ) : ℝ) * ((3 * m + 20 + i : ℕ) : ℝ) * ((3 * m + 23 + i : ℕ) : ℝ) * ((3 * m + 26 + i : ℕ) : ℝ) * ((3 * m + 29 + i : ℕ) : ℝ)))) ^ 2)) := by
    apply tsum_congr
    intro m
    exact (vm7_eq_statement m).symm
  rw [← hL]
  rw [hMain]
  have hR : (∑' k : ℕ,
      ((1 : ℝ) / (((3 * k + 1 : ℕ) : ℝ) ^ 2) - (1 : ℝ) / (((3 * k + 2 : ℕ) : ℝ) ^ 2))) = A - B := by
    simpa [Rk, f1, f2, xm] using tsum_Rk
  rw [hR]
  ring

end Commons.Analysis.Summation
