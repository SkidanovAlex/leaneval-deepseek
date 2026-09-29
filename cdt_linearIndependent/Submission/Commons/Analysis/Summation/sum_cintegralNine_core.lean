import Mathlib
import Submission.Commons.Analysis.Summation.sum_cintegralEight_core

noncomputable section
set_option maxHeartbeats 0
open scoped BigOperators Nat
open Filter Topology

namespace Commons.Analysis.Summation
namespace CdtNineCore

/-! ## Binomial `(m+18 choose 18)` as a degree-18 polynomial -/

lemma asc18 (n : ℕ) : n.ascFactorial 18 =
    n * (n + 1) * (n + 2) * (n + 3) * (n + 4) * (n + 5) * (n + 6) * (n + 7) *
      (n + 8) * (n + 9) * (n + 10) * (n + 11) * (n + 12) * (n + 13) * (n + 14) *
        (n + 15) * (n + 16) * (n + 17) := by
  simp [Nat.ascFactorial_succ, Nat.ascFactorial_zero]
  ring

lemma factorial_add_eighteen (m : ℕ) : (m + 18)! =
    m ! * (m + 1) * (m + 2) * (m + 3) * (m + 4) * (m + 5) * (m + 6) * (m + 7) *
      (m + 8) * (m + 9) * (m + 10) * (m + 11) * (m + 12) * (m + 13) * (m + 14) *
        (m + 15) * (m + 16) * (m + 17) * (m + 18) := by
  rw [← Nat.factorial_mul_ascFactorial m 18]
  have h := asc18 (m + 1)
  rw [h]
  ring

lemma choose218 (m : ℕ) :
    (Nat.choose (m + 18) 18 : ℝ) =
      (1 / 6402373705728000 : ℝ) *
        (((m : ℝ) + 1) * ((m : ℝ) + 2) * ((m : ℝ) + 3) * ((m : ℝ) + 4) *
          ((m : ℝ) + 5) * ((m : ℝ) + 6) * ((m : ℝ) + 7) * ((m : ℝ) + 8) *
          ((m : ℝ) + 9) * ((m : ℝ) + 10) * ((m : ℝ) + 11) * ((m : ℝ) + 12) *
          ((m : ℝ) + 13) * ((m : ℝ) + 14) * ((m : ℝ) + 15) * ((m : ℝ) + 16) *
          ((m : ℝ) + 17) * ((m : ℝ) + 18)) := by
  have hcast := Nat.cast_choose ℝ (a := 18) (b := m + 18) (by omega : 18 ≤ m + 18)
  rw [hcast]
  have h18 : ((18 : ℕ)! : ℝ) = 6402373705728000 := by norm_num
  have hsub : ((m + 18 - 18) : ℕ) = m := by omega
  rw [h18, hsub]
  have hfacR : ((m + 18)! : ℝ) = (m ! : ℝ) *
      (((m : ℝ) + 1) * ((m : ℝ) + 2) * ((m : ℝ) + 3) * ((m : ℝ) + 4) *
        ((m : ℝ) + 5) * ((m : ℝ) + 6) * ((m : ℝ) + 7) * ((m : ℝ) + 8) *
        ((m : ℝ) + 9) * ((m : ℝ) + 10) * ((m : ℝ) + 11) * ((m : ℝ) + 12) *
        ((m : ℝ) + 13) * ((m : ℝ) + 14) * ((m : ℝ) + 15) * ((m : ℝ) + 16) *
        ((m : ℝ) + 17) * ((m : ℝ) + 18)) := by
    norm_num [factorial_add_eighteen, Nat.cast_mul]
    ring
  rw [hfacR]
  have hm : (m ! : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_ne_zero m)
  field_simp [hm]

@[simp] lemma c19_0 : (Nat.choose 19 0 : ℝ) = 1 := by
  rw [Nat.cast_choose ℝ (by decide : 0 ≤ 19)]; norm_num
@[simp] lemma c19_1 : (Nat.choose 19 1 : ℝ) = 19 := by
  rw [Nat.cast_choose ℝ (by decide : 1 ≤ 19)]; norm_num
@[simp] lemma c19_2 : (Nat.choose 19 2 : ℝ) = 171 := by
  rw [Nat.cast_choose ℝ (by decide : 2 ≤ 19)]; norm_num
@[simp] lemma c19_3 : (Nat.choose 19 3 : ℝ) = 969 := by
  rw [Nat.cast_choose ℝ (by decide : 3 ≤ 19)]; norm_num
@[simp] lemma c19_4 : (Nat.choose 19 4 : ℝ) = 3876 := by
  rw [Nat.cast_choose ℝ (by decide : 4 ≤ 19)]; norm_num
@[simp] lemma c19_5 : (Nat.choose 19 5 : ℝ) = 11628 := by
  rw [Nat.cast_choose ℝ (by decide : 5 ≤ 19)]; norm_num
@[simp] lemma c19_6 : (Nat.choose 19 6 : ℝ) = 27132 := by
  rw [Nat.cast_choose ℝ (by decide : 6 ≤ 19)]; norm_num
@[simp] lemma c19_7 : (Nat.choose 19 7 : ℝ) = 50388 := by
  rw [Nat.cast_choose ℝ (by decide : 7 ≤ 19)]; norm_num
@[simp] lemma c19_8 : (Nat.choose 19 8 : ℝ) = 75582 := by
  rw [Nat.cast_choose ℝ (by decide : 8 ≤ 19)]; norm_num
@[simp] lemma c19_9 : (Nat.choose 19 9 : ℝ) = 92378 := by
  rw [Nat.cast_choose ℝ (by decide : 9 ≤ 19)]; norm_num
@[simp] lemma c19_10 : (Nat.choose 19 10 : ℝ) = 92378 := by
  rw [Nat.cast_choose ℝ (by decide : 10 ≤ 19)]; norm_num
@[simp] lemma c19_11 : (Nat.choose 19 11 : ℝ) = 75582 := by
  rw [Nat.cast_choose ℝ (by decide : 11 ≤ 19)]; norm_num
@[simp] lemma c19_12 : (Nat.choose 19 12 : ℝ) = 50388 := by
  rw [Nat.cast_choose ℝ (by decide : 12 ≤ 19)]; norm_num
@[simp] lemma c19_13 : (Nat.choose 19 13 : ℝ) = 27132 := by
  rw [Nat.cast_choose ℝ (by decide : 13 ≤ 19)]; norm_num
@[simp] lemma c19_14 : (Nat.choose 19 14 : ℝ) = 11628 := by
  rw [Nat.cast_choose ℝ (by decide : 14 ≤ 19)]; norm_num
@[simp] lemma c19_15 : (Nat.choose 19 15 : ℝ) = 3876 := by
  rw [Nat.cast_choose ℝ (by decide : 15 ≤ 19)]; norm_num
@[simp] lemma c19_16 : (Nat.choose 19 16 : ℝ) = 969 := by
  rw [Nat.cast_choose ℝ (by decide : 16 ≤ 19)]; norm_num
@[simp] lemma c19_17 : (Nat.choose 19 17 : ℝ) = 171 := by
  rw [Nat.cast_choose ℝ (by decide : 17 ≤ 19)]; norm_num
@[simp] lemma c19_18 : (Nat.choose 19 18 : ℝ) = 19 := by
  rw [Nat.cast_choose ℝ (by decide : 18 ≤ 19)]; norm_num
@[simp] lemma c19_19 : (Nat.choose 19 19 : ℝ) = 1 := by
  rw [Nat.cast_choose ℝ (by decide : 19 ≤ 19)]; norm_num

/-! ## The `m`-summand and its pointwise closed-form decomposition -/

/-- The `m`-summand of the nine-core sum. -/
def Vm9 (m : ℕ) : ℝ :=
  (387420489 : ℝ) * (Nat.choose (m + 18) 18 : ℝ) *
    (∑ i ∈ Finset.range 20,
      ((-1 : ℝ) ^ i * (Nat.choose 19 i : ℝ)) *
        (7142567040 / (xm m (10 + i) * xm m (13 + i) * xm m (16 + i) * xm m (19 + i) *
          xm m (22 + i) * xm m (25 + i) * xm m (28 + i) * xm m (31 + i) * xm m (34 + i) * xm m (37 + i))) ^ 2)

/-- Squared-term part of the closed-form decomposition. -/
def W19 (m : ℕ) : ℝ :=
  (-(160034644 : ℝ)) / 6561 * (1 / (xm m 10)^2)
  +   (1780488100 : ℝ) / 6561 * (1 / (xm m 11)^2)
  +   (-(10765966960 : ℝ)) / 2187 * (1 / (xm m 13)^2)
  +   (18674421700 : ℝ) / 2187 * (1 / (xm m 14)^2)
  +   (192441659410 : ℝ) / 2187 * (1 / (xm m 16)^2)
  +   (-(668271012640 : ℝ)) / 2187 * (1 / (xm m 17)^2)
  +   (4159181804960 : ℝ) / 6561 * (1 / (xm m 19)^2)
  +   (3470206110910 : ℝ) / 6561 * (1 / (xm m 20)^2)
  +   (-(18372328730912 : ℝ)) / 2187 * (1 / (xm m 22)^2)
  +   (23281168872500 : ℝ) / 2187 * (1 / (xm m 23)^2)
  +   (36505191495344 : ℝ) / 2187 * (1 / (xm m 25)^2)
  +   (-(99140514738650 : ℝ)) / 2187 * (1 / (xm m 26)^2)
  +   (267866754444575 : ℝ) / 6561 * (1 / (xm m 28)^2)
  +   (190322577101800 : ℝ) / 6561 * (1 / (xm m 29)^2)
  +   (-(14376960909850 : ℝ)) / 81 * (1 / (xm m 31)^2)
  +   (11271008428537 : ℝ) / 81 * (1 / (xm m 32)^2)
  +   (14103383859950 : ℝ) / 81 * (1 / (xm m 34)^2)
  +   (-(22525150183952 : ℝ)) / 81 * (1 / (xm m 35)^2)
  +   (469632098279960 : ℝ) / 6561 * (1 / (xm m 37)^2)
  +   (832565759268880 : ℝ) / 6561 * (1 / (xm m 38)^2)
  +   (-(494409436544485 : ℝ)) / 2187 * (1 / (xm m 40)^2)
  +   (232305764061280 : ℝ) / 2187 * (1 / (xm m 41)^2)
  +   (246115213795000 : ℝ) / 2187 * (1 / (xm m 43)^2)
  +   (-(253502805085180 : ℝ)) / 2187 * (1 / (xm m 44)^2)
  +   (84355965201800 : ℝ) / 6561 * (1 / (xm m 46)^2)
  +   (137077034179624 : ℝ) / 6561 * (1 / (xm m 47)^2)
  +   (-(42916885162400 : ℝ)) / 2187 * (1 / (xm m 49)^2)
  +   (17930487272588 : ℝ) / 2187 * (1 / (xm m 50)^2)
  +   (4113550681835 : ℝ) / 2187 * (1 / (xm m 52)^2)
  +   (-(3975717798800 : ℝ)) / 2187 * (1 / (xm m 53)^2)
  +   (2608593115310 : ℝ) / 6561 * (1 / (xm m 55)^2)
  +   (-(711868389650 : ℝ)) / 6561 * (1 / (xm m 56)^2)

/-- Telescoping-pair part of the closed-form decomposition. -/
def W29 (m : ℕ) : ℝ :=
  (73834838343949 : ℝ) / 1565979480 * (1 / xm m 10 - 1 / xm m (10 + 3))
  +   (-(358986576880223 : ℝ)) / 1722577428 * (1 / xm m 11 - 1 / xm m (11 + 3))
  +   (-(2453663097 : ℝ)) / 1360 * (1 / xm m 12 - 1 / xm m (12 + 3))
  +   (180862049695590059 : ℝ) / 17225774280 * (1 / xm m 13 - 1 / xm m (13 + 3))
  +   (-(5127197954934689 : ℝ)) / 430644357 * (1 / xm m 14 - 1 / xm m (14 + 3))
  +   (46619598843 : ℝ) / 9520 * (1 / xm m 15 - 1 / xm m (15 + 3))
  +   (-(2747448774152478947 : ℝ)) / 34451548560 * (1 / xm m 16 - 1 / xm m (16 + 3))
  +   (56299376823384077 : ℝ) / 2153221785 * (1 / xm m 17 - 1 / xm m (17 + 3))
  +   (1023177511449 : ℝ) / 1360 * (1 / xm m 18 - 1 / xm m (18 + 3))
  +   (-(47083617883937152627 : ℝ)) / 34451548560 * (1 / xm m 19 - 1 / xm m (19 + 3))
  +   (1307468594386437761 : ℝ) / 1325059560 * (1 / xm m 20 - 1 / xm m (20 + 3))
  +   (-(467700083908461 : ℝ)) / 123760 * (1 / xm m 21 - 1 / xm m (21 + 3))
  +   (278998770269750798717 : ℝ) / 34451548560 * (1 / xm m 22 - 1 / xm m (22 + 3))
  +   (-(12754996673051891857 : ℝ)) / 17225774280 * (1 / xm m 23 - 1 / xm m (23 + 3))
  +   (-(11428065918421641 : ℝ)) / 1361360 * (1 / xm m 24 - 1 / xm m (24 + 3))
  +   (37460705804159755853 : ℝ) / 34451548560 * (1 / xm m 25 - 1 / xm m (25 + 3))
  +   (-(149060964191141136461 : ℝ)) / 8612887140 * (1 / xm m 26 - 1 / xm m (26 + 3))
  +   (6983319013446663 : ℝ) / 104720 * (1 / xm m 27 - 1 / xm m (27 + 3))
  +   (-(4904093445886785286 : ℝ)) / 79748955 * (1 / xm m 28 - 1 / xm m (28 + 3))
  +   (67579794830728691029 : ℝ) / 2232970740 * (1 / xm m 29 - 1 / xm m (29 + 3))
  +   (-(9946764970131771 : ℝ)) / 123760 * (1 / xm m 30 - 1 / xm m (30 + 3))
  +   (53848123721928614497 : ℝ) / 637991640 * (1 / xm m 31 - 1 / xm m (31 + 3))
  +   (387880612235350374643 : ℝ) / 8931882960 * (1 / xm m 32 - 1 / xm m (32 + 3))
  +   (-(9946764970131771 : ℝ)) / 123760 * (1 / xm m 33 - 1 / xm m (33 + 3))
  +   (708226381220574527 : ℝ) / 24538140 * (1 / xm m 34 - 1 / xm m (34 + 3))
  +   (-(1094037352368808966421 : ℝ)) / 8931882960 * (1 / xm m 35 - 1 / xm m (35 + 3))
  +   (1612674977829444 : ℝ) / 7735 * (1 / xm m 36 - 1 / xm m (36 + 3))
  +   (-(903814450480016249089 : ℝ)) / 8612887140 * (1 / xm m 37 - 1 / xm m (37 + 3))
  +   (10257883818182378321953 : ℝ) / 241160839920 * (1 / xm m 38 - 1 / xm m (38 + 3))
  +   (-(411584808880071 : ℝ)) / 4760 * (1 / xm m 39 - 1 / xm m (39 + 3))
  +   (1107954397571751413441 : ℝ) / 34451548560 * (1 / xm m 40 - 1 / xm m (40 + 3))
  +   (14697144396974365714033 : ℝ) / 241160839920 * (1 / xm m 41 - 1 / xm m (41 + 3))
  +   (-(33151442103567 : ℝ)) / 680 * (1 / xm m 42 - 1 / xm m (42 + 3))
  +   (722416830631049864441 : ℝ) / 34451548560 * (1 / xm m 43 - 1 / xm m (43 + 3))
  +   (-(49268782689753205811 : ℝ)) / 1289630160 * (1 / xm m 44 - 1 / xm m (44 + 3))
  +   (4585896328293 : ℝ) / 136 * (1 / xm m 45 - 1 / xm m (45 + 3))
  +   (-(213348134488954669679 : ℝ)) / 34451548560 * (1 / xm m 46 - 1 / xm m (46 + 3))
  +   (-(51005926223417397431 : ℝ)) / 21923712720 * (1 / xm m 47 - 1 / xm m (47 + 3))
  +   (-(4907326194 : ℝ)) / 17 * (1 / xm m 48 - 1 / xm m (48 + 3))
  +   (-(55959478822287565199 : ℝ)) / 34451548560 * (1 / xm m 49 - 1 / xm m (49 + 3))
  +   (12714323567196633131 : ℝ) / 4384742544 * (1 / xm m 50 - 1 / xm m (50 + 3))
  +   (-(2453663097 : ℝ)) / 2 * (1 / xm m 51 - 1 / xm m (51 + 3))
  +   (62393981797184249 : ℝ) / 1325059560 * (1 / xm m 52 - 1 / xm m (52 + 3))
  +   (228355373070909923 : ℝ) / 4384742544 * (1 / xm m 53 - 1 / xm m (53 + 3))

/-- The closed-form decomposition of the summand (as `W19 + W29`). -/
def Vd9 (m : ℕ) : ℝ := W19 m + W29 m

set_option maxHeartbeats 0 in
lemma vm9_decomp (m : ℕ) : Vm9 m = Vd9 m := by
  unfold Vm9 Vd9 W19 W29
  rw [choose218]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero,
    c19_0, c19_1, c19_2, c19_3, c19_4, c19_5, c19_6, c19_7, c19_8, c19_9, c19_10,
    c19_11, c19_12, c19_13, c19_14, c19_15, c19_16, c19_17, c19_18, c19_19]
  norm_num
  simp_rw [xm_eq]
  norm_num
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
  have h45 : (3 * (m : ℝ) + 45) ≠ 0 := by positivity
  have h46 : (3 * (m : ℝ) + 46) ≠ 0 := by positivity
  have h47 : (3 * (m : ℝ) + 47) ≠ 0 := by positivity
  have h48 : (3 * (m : ℝ) + 48) ≠ 0 := by positivity
  have h49 : (3 * (m : ℝ) + 49) ≠ 0 := by positivity
  have h50 : (3 * (m : ℝ) + 50) ≠ 0 := by positivity
  have h51 : (3 * (m : ℝ) + 51) ≠ 0 := by positivity
  have h52 : (3 * (m : ℝ) + 52) ≠ 0 := by positivity
  have h53 : (3 * (m : ℝ) + 53) ≠ 0 := by positivity
  have h54 : (3 * (m : ℝ) + 54) ≠ 0 := by positivity
  have h55 : (3 * (m : ℝ) + 55) ≠ 0 := by positivity
  have h56 : (3 * (m : ℝ) + 56) ≠ 0 := by positivity
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
  have hm15 : (m : ℝ) + 15 ≠ 0 := by positivity
  have hm16 : (m : ℝ) + 16 ≠ 0 := by positivity
  have hm17 : (m : ℝ) + 17 ≠ 0 := by positivity
  have hm18 : (m : ℝ) + 18 ≠ 0 := by positivity
  field_simp [h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36, h37, h38, h39, h40, h41, h42, h43, h44, h45, h46, h47, h48, h49, h50, h51, h52, h53, h54, h55, h56, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18]
  ring

/-! ## The statement denominators equal the `xm` denominators -/

lemma denom_statement9 (m : ℕ) : ∀ i : ℕ,
    ((((3 * m + 10 + i : ℕ) : ℝ) * ((3 * m + 13 + i : ℕ) : ℝ) * ((3 * m + 16 + i : ℕ) : ℝ) * ((3 * m + 19 + i : ℕ) : ℝ) * ((3 * m + 22 + i : ℕ) : ℝ) * ((3 * m + 25 + i : ℕ) : ℝ) * ((3 * m + 28 + i : ℕ) : ℝ) * ((3 * m + 31 + i : ℕ) : ℝ) * ((3 * m + 34 + i : ℕ) : ℝ) * ((3 * m + 37 + i : ℕ) : ℝ)))
      = xm m (10 + i) * xm m (13 + i) * xm m (16 + i) * xm m (19 + i) * xm m (22 + i) * xm m (25 + i) * xm m (28 + i) * xm m (31 + i) * xm m (34 + i) * xm m (37 + i) := by
  intro i
  have h0 : (((3 * m + 10 + i : ℕ) : ℝ)) = xm m (10 + i) := by
    unfold xm
    congr 1
    omega
  have h1 : (((3 * m + 13 + i : ℕ) : ℝ)) = xm m (13 + i) := by
    unfold xm
    congr 1
    omega
  have h2 : (((3 * m + 16 + i : ℕ) : ℝ)) = xm m (16 + i) := by
    unfold xm
    congr 1
    omega
  have h3 : (((3 * m + 19 + i : ℕ) : ℝ)) = xm m (19 + i) := by
    unfold xm
    congr 1
    omega
  have h4 : (((3 * m + 22 + i : ℕ) : ℝ)) = xm m (22 + i) := by
    unfold xm
    congr 1
    omega
  have h5 : (((3 * m + 25 + i : ℕ) : ℝ)) = xm m (25 + i) := by
    unfold xm
    congr 1
    omega
  have h6 : (((3 * m + 28 + i : ℕ) : ℝ)) = xm m (28 + i) := by
    unfold xm
    congr 1
    omega
  have h7 : (((3 * m + 31 + i : ℕ) : ℝ)) = xm m (31 + i) := by
    unfold xm
    congr 1
    omega
  have h8 : (((3 * m + 34 + i : ℕ) : ℝ)) = xm m (34 + i) := by
    unfold xm
    congr 1
    omega
  have h9 : (((3 * m + 37 + i : ℕ) : ℝ)) = xm m (37 + i) := by
    unfold xm
    congr 1
    omega
  rw [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9]

/-- The inner `i`-sum in the statement's form equals the `xm` form. -/
lemma inner_sum_statement9 (m : ℕ) :
        (∑ i ∈ Finset.range 20,
      ((-1 : ℝ) ^ i * (Nat.choose 19 i : ℝ)) *
        (7142567040 / (((3 * m + 10 + i : ℕ) : ℝ) * ((3 * m + 13 + i : ℕ) : ℝ) * ((3 * m + 16 + i : ℕ) : ℝ) * ((3 * m + 19 + i : ℕ) : ℝ) * ((3 * m + 22 + i : ℕ) : ℝ) * ((3 * m + 25 + i : ℕ) : ℝ) * ((3 * m + 28 + i : ℕ) : ℝ) * ((3 * m + 31 + i : ℕ) : ℝ) * ((3 * m + 34 + i : ℕ) : ℝ) * ((3 * m + 37 + i : ℕ) : ℝ))) ^ 2)
    =     (∑ i ∈ Finset.range 20,
      ((-1 : ℝ) ^ i * (Nat.choose 19 i : ℝ)) *
        (7142567040 / (xm m (10 + i) * xm m (13 + i) * xm m (16 + i) * xm m (19 + i) * xm m (22 + i) * xm m (25 + i) * xm m (28 + i) * xm m (31 + i) * xm m (34 + i) * xm m (37 + i))) ^ 2) := by
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  rw [denom_statement9 m i]

/-- The `m`-summand of the nine-core sum, in the statement's form. -/
lemma vm9_eq_statement (m : ℕ) :
    (387420489 : ℝ) * (Nat.choose (m + 18) 18 : ℝ) *
      (∑ i ∈ Finset.range 20,
        ((-1 : ℝ) ^ i * (Nat.choose 19 i : ℝ)) *
          (7142567040 / ((((3 * m + 10 + i : ℕ) : ℝ) * ((3 * m + 13 + i : ℕ) : ℝ) *
            ((3 * m + 16 + i : ℕ) : ℝ) * ((3 * m + 19 + i : ℕ) : ℝ) *
              ((3 * m + 22 + i : ℕ) : ℝ) * ((3 * m + 25 + i : ℕ) : ℝ) *
                ((3 * m + 28 + i : ℕ) : ℝ) * ((3 * m + 31 + i : ℕ) : ℝ) *
                  ((3 * m + 34 + i : ℕ) : ℝ) * ((3 * m + 37 + i : ℕ) : ℝ)))) ^ 2) =
      Vm9 m := by
  unfold Vm9
  rw [inner_sum_statement9 m]

/-! ## Small partial sums needed for the shifts -/

@[simp] lemma asum17 : Asum 17 = 1176077259993511208946453291389 / 1054650787564396936572699040000 := by
  norm_num [Asum, f1, xm]
@[simp] lemma asum18 : Asum 18 = 1176467293568793900121221301389 / 1054650787564396936572699040000 := by
  norm_num [Asum, f1, xm]
@[simp] lemma bsum17 : Bsum 17 = 36911580506190545943361852769 / 110526971620013720771359360000 := by
  norm_num [Bsum, f2, xm]
@[simp] lemma bsum18 : Bsum 18 = 103795156613509257275674803788121 / 310470263280618541646748442240000 := by
  norm_num [Bsum, f2, xm]

/-! ## The values of the two pieces -/

/-- The value of the `W19`-sum. -/
noncomputable def V1val9 : ℝ :=
  (-(160034644 : ℝ)) / 6561 * (A - Asum 3)
  +   (1780488100 : ℝ) / 6561 * (B - Bsum 3)
  +   (-(10765966960 : ℝ)) / 2187 * (A - Asum 4)
  +   (18674421700 : ℝ) / 2187 * (B - Bsum 4)
  +   (192441659410 : ℝ) / 2187 * (A - Asum 5)
  +   (-(668271012640 : ℝ)) / 2187 * (B - Bsum 5)
  +   (4159181804960 : ℝ) / 6561 * (A - Asum 6)
  +   (3470206110910 : ℝ) / 6561 * (B - Bsum 6)
  +   (-(18372328730912 : ℝ)) / 2187 * (A - Asum 7)
  +   (23281168872500 : ℝ) / 2187 * (B - Bsum 7)
  +   (36505191495344 : ℝ) / 2187 * (A - Asum 8)
  +   (-(99140514738650 : ℝ)) / 2187 * (B - Bsum 8)
  +   (267866754444575 : ℝ) / 6561 * (A - Asum 9)
  +   (190322577101800 : ℝ) / 6561 * (B - Bsum 9)
  +   (-(14376960909850 : ℝ)) / 81 * (A - Asum 10)
  +   (11271008428537 : ℝ) / 81 * (B - Bsum 10)
  +   (14103383859950 : ℝ) / 81 * (A - Asum 11)
  +   (-(22525150183952 : ℝ)) / 81 * (B - Bsum 11)
  +   (469632098279960 : ℝ) / 6561 * (A - Asum 12)
  +   (832565759268880 : ℝ) / 6561 * (B - Bsum 12)
  +   (-(494409436544485 : ℝ)) / 2187 * (A - Asum 13)
  +   (232305764061280 : ℝ) / 2187 * (B - Bsum 13)
  +   (246115213795000 : ℝ) / 2187 * (A - Asum 14)
  +   (-(253502805085180 : ℝ)) / 2187 * (B - Bsum 14)
  +   (84355965201800 : ℝ) / 6561 * (A - Asum 15)
  +   (137077034179624 : ℝ) / 6561 * (B - Bsum 15)
  +   (-(42916885162400 : ℝ)) / 2187 * (A - Asum 16)
  +   (17930487272588 : ℝ) / 2187 * (B - Bsum 16)
  +   (4113550681835 : ℝ) / 2187 * (A - Asum 17)
  +   (-(3975717798800 : ℝ)) / 2187 * (B - Bsum 17)
  +   (2608593115310 : ℝ) / 6561 * (A - Asum 18)
  +   (-(711868389650 : ℝ)) / 6561 * (B - Bsum 18)

/-- The value of the `W29`-sum. -/
noncomputable def V2val9 : ℝ :=
  (73834838343949 : ℝ) / 1565979480 * (1 / xm 0 10)
  +   (-(358986576880223 : ℝ)) / 1722577428 * (1 / xm 0 11)
  +   (-(2453663097 : ℝ)) / 1360 * (1 / xm 0 12)
  +   (180862049695590059 : ℝ) / 17225774280 * (1 / xm 0 13)
  +   (-(5127197954934689 : ℝ)) / 430644357 * (1 / xm 0 14)
  +   (46619598843 : ℝ) / 9520 * (1 / xm 0 15)
  +   (-(2747448774152478947 : ℝ)) / 34451548560 * (1 / xm 0 16)
  +   (56299376823384077 : ℝ) / 2153221785 * (1 / xm 0 17)
  +   (1023177511449 : ℝ) / 1360 * (1 / xm 0 18)
  +   (-(47083617883937152627 : ℝ)) / 34451548560 * (1 / xm 0 19)
  +   (1307468594386437761 : ℝ) / 1325059560 * (1 / xm 0 20)
  +   (-(467700083908461 : ℝ)) / 123760 * (1 / xm 0 21)
  +   (278998770269750798717 : ℝ) / 34451548560 * (1 / xm 0 22)
  +   (-(12754996673051891857 : ℝ)) / 17225774280 * (1 / xm 0 23)
  +   (-(11428065918421641 : ℝ)) / 1361360 * (1 / xm 0 24)
  +   (37460705804159755853 : ℝ) / 34451548560 * (1 / xm 0 25)
  +   (-(149060964191141136461 : ℝ)) / 8612887140 * (1 / xm 0 26)
  +   (6983319013446663 : ℝ) / 104720 * (1 / xm 0 27)
  +   (-(4904093445886785286 : ℝ)) / 79748955 * (1 / xm 0 28)
  +   (67579794830728691029 : ℝ) / 2232970740 * (1 / xm 0 29)
  +   (-(9946764970131771 : ℝ)) / 123760 * (1 / xm 0 30)
  +   (53848123721928614497 : ℝ) / 637991640 * (1 / xm 0 31)
  +   (387880612235350374643 : ℝ) / 8931882960 * (1 / xm 0 32)
  +   (-(9946764970131771 : ℝ)) / 123760 * (1 / xm 0 33)
  +   (708226381220574527 : ℝ) / 24538140 * (1 / xm 0 34)
  +   (-(1094037352368808966421 : ℝ)) / 8931882960 * (1 / xm 0 35)
  +   (1612674977829444 : ℝ) / 7735 * (1 / xm 0 36)
  +   (-(903814450480016249089 : ℝ)) / 8612887140 * (1 / xm 0 37)
  +   (10257883818182378321953 : ℝ) / 241160839920 * (1 / xm 0 38)
  +   (-(411584808880071 : ℝ)) / 4760 * (1 / xm 0 39)
  +   (1107954397571751413441 : ℝ) / 34451548560 * (1 / xm 0 40)
  +   (14697144396974365714033 : ℝ) / 241160839920 * (1 / xm 0 41)
  +   (-(33151442103567 : ℝ)) / 680 * (1 / xm 0 42)
  +   (722416830631049864441 : ℝ) / 34451548560 * (1 / xm 0 43)
  +   (-(49268782689753205811 : ℝ)) / 1289630160 * (1 / xm 0 44)
  +   (4585896328293 : ℝ) / 136 * (1 / xm 0 45)
  +   (-(213348134488954669679 : ℝ)) / 34451548560 * (1 / xm 0 46)
  +   (-(51005926223417397431 : ℝ)) / 21923712720 * (1 / xm 0 47)
  +   (-(4907326194 : ℝ)) / 17 * (1 / xm 0 48)
  +   (-(55959478822287565199 : ℝ)) / 34451548560 * (1 / xm 0 49)
  +   (12714323567196633131 : ℝ) / 4384742544 * (1 / xm 0 50)
  +   (-(2453663097 : ℝ)) / 2 * (1 / xm 0 51)
  +   (62393981797184249 : ℝ) / 1325059560 * (1 / xm 0 52)
  +   (228355373070909923 : ℝ) / 4384742544 * (1 / xm 0 53)

/-- The value of the whole sum. -/
noncomputable def Vval9 : ℝ := V1val9 + V2val9

/-! ## `HasSum` of the two pieces of the decomposition -/

lemma hasSum_W19 : HasSum W19 V1val9 := by
  have h10 : HasSum (fun m : ℕ => (-(160034644 : ℝ)) / 6561 * (1 / (xm m 10)^2))
      ((-(160034644 : ℝ)) / 6561 * (A - Asum 3)) := by
    simpa using (CdtTwoCore.hasSum_sq1 3).mul_left ((-(160034644 : ℝ)) / 6561)
  have h11 : HasSum (fun m : ℕ => (1780488100 : ℝ) / 6561 * (1 / (xm m 11)^2))
      ((1780488100 : ℝ) / 6561 * (B - Bsum 3)) := by
    simpa using (CdtTwoCore.hasSum_sq2 3).mul_left ((1780488100 : ℝ) / 6561)
  have h13 : HasSum (fun m : ℕ => (-(10765966960 : ℝ)) / 2187 * (1 / (xm m 13)^2))
      ((-(10765966960 : ℝ)) / 2187 * (A - Asum 4)) := by
    simpa using (CdtTwoCore.hasSum_sq1 4).mul_left ((-(10765966960 : ℝ)) / 2187)
  have h14 : HasSum (fun m : ℕ => (18674421700 : ℝ) / 2187 * (1 / (xm m 14)^2))
      ((18674421700 : ℝ) / 2187 * (B - Bsum 4)) := by
    simpa using (CdtTwoCore.hasSum_sq2 4).mul_left ((18674421700 : ℝ) / 2187)
  have h16 : HasSum (fun m : ℕ => (192441659410 : ℝ) / 2187 * (1 / (xm m 16)^2))
      ((192441659410 : ℝ) / 2187 * (A - Asum 5)) := by
    simpa using (CdtTwoCore.hasSum_sq1 5).mul_left ((192441659410 : ℝ) / 2187)
  have h17 : HasSum (fun m : ℕ => (-(668271012640 : ℝ)) / 2187 * (1 / (xm m 17)^2))
      ((-(668271012640 : ℝ)) / 2187 * (B - Bsum 5)) := by
    simpa using (CdtTwoCore.hasSum_sq2 5).mul_left ((-(668271012640 : ℝ)) / 2187)
  have h19 : HasSum (fun m : ℕ => (4159181804960 : ℝ) / 6561 * (1 / (xm m 19)^2))
      ((4159181804960 : ℝ) / 6561 * (A - Asum 6)) := by
    simpa using (CdtTwoCore.hasSum_sq1 6).mul_left ((4159181804960 : ℝ) / 6561)
  have h20 : HasSum (fun m : ℕ => (3470206110910 : ℝ) / 6561 * (1 / (xm m 20)^2))
      ((3470206110910 : ℝ) / 6561 * (B - Bsum 6)) := by
    simpa using (CdtTwoCore.hasSum_sq2 6).mul_left ((3470206110910 : ℝ) / 6561)
  have h22 : HasSum (fun m : ℕ => (-(18372328730912 : ℝ)) / 2187 * (1 / (xm m 22)^2))
      ((-(18372328730912 : ℝ)) / 2187 * (A - Asum 7)) := by
    simpa using (CdtTwoCore.hasSum_sq1 7).mul_left ((-(18372328730912 : ℝ)) / 2187)
  have h23 : HasSum (fun m : ℕ => (23281168872500 : ℝ) / 2187 * (1 / (xm m 23)^2))
      ((23281168872500 : ℝ) / 2187 * (B - Bsum 7)) := by
    simpa using (CdtTwoCore.hasSum_sq2 7).mul_left ((23281168872500 : ℝ) / 2187)
  have h25 : HasSum (fun m : ℕ => (36505191495344 : ℝ) / 2187 * (1 / (xm m 25)^2))
      ((36505191495344 : ℝ) / 2187 * (A - Asum 8)) := by
    simpa using (CdtTwoCore.hasSum_sq1 8).mul_left ((36505191495344 : ℝ) / 2187)
  have h26 : HasSum (fun m : ℕ => (-(99140514738650 : ℝ)) / 2187 * (1 / (xm m 26)^2))
      ((-(99140514738650 : ℝ)) / 2187 * (B - Bsum 8)) := by
    simpa using (CdtTwoCore.hasSum_sq2 8).mul_left ((-(99140514738650 : ℝ)) / 2187)
  have h28 : HasSum (fun m : ℕ => (267866754444575 : ℝ) / 6561 * (1 / (xm m 28)^2))
      ((267866754444575 : ℝ) / 6561 * (A - Asum 9)) := by
    simpa using (CdtTwoCore.hasSum_sq1 9).mul_left ((267866754444575 : ℝ) / 6561)
  have h29 : HasSum (fun m : ℕ => (190322577101800 : ℝ) / 6561 * (1 / (xm m 29)^2))
      ((190322577101800 : ℝ) / 6561 * (B - Bsum 9)) := by
    simpa using (CdtTwoCore.hasSum_sq2 9).mul_left ((190322577101800 : ℝ) / 6561)
  have h31 : HasSum (fun m : ℕ => (-(14376960909850 : ℝ)) / 81 * (1 / (xm m 31)^2))
      ((-(14376960909850 : ℝ)) / 81 * (A - Asum 10)) := by
    simpa using (CdtTwoCore.hasSum_sq1 10).mul_left ((-(14376960909850 : ℝ)) / 81)
  have h32 : HasSum (fun m : ℕ => (11271008428537 : ℝ) / 81 * (1 / (xm m 32)^2))
      ((11271008428537 : ℝ) / 81 * (B - Bsum 10)) := by
    simpa using (CdtTwoCore.hasSum_sq2 10).mul_left ((11271008428537 : ℝ) / 81)
  have h34 : HasSum (fun m : ℕ => (14103383859950 : ℝ) / 81 * (1 / (xm m 34)^2))
      ((14103383859950 : ℝ) / 81 * (A - Asum 11)) := by
    simpa using (CdtTwoCore.hasSum_sq1 11).mul_left ((14103383859950 : ℝ) / 81)
  have h35 : HasSum (fun m : ℕ => (-(22525150183952 : ℝ)) / 81 * (1 / (xm m 35)^2))
      ((-(22525150183952 : ℝ)) / 81 * (B - Bsum 11)) := by
    simpa using (CdtTwoCore.hasSum_sq2 11).mul_left ((-(22525150183952 : ℝ)) / 81)
  have h37 : HasSum (fun m : ℕ => (469632098279960 : ℝ) / 6561 * (1 / (xm m 37)^2))
      ((469632098279960 : ℝ) / 6561 * (A - Asum 12)) := by
    simpa using (CdtTwoCore.hasSum_sq1 12).mul_left ((469632098279960 : ℝ) / 6561)
  have h38 : HasSum (fun m : ℕ => (832565759268880 : ℝ) / 6561 * (1 / (xm m 38)^2))
      ((832565759268880 : ℝ) / 6561 * (B - Bsum 12)) := by
    simpa using (CdtTwoCore.hasSum_sq2 12).mul_left ((832565759268880 : ℝ) / 6561)
  have h40 : HasSum (fun m : ℕ => (-(494409436544485 : ℝ)) / 2187 * (1 / (xm m 40)^2))
      ((-(494409436544485 : ℝ)) / 2187 * (A - Asum 13)) := by
    simpa using (CdtTwoCore.hasSum_sq1 13).mul_left ((-(494409436544485 : ℝ)) / 2187)
  have h41 : HasSum (fun m : ℕ => (232305764061280 : ℝ) / 2187 * (1 / (xm m 41)^2))
      ((232305764061280 : ℝ) / 2187 * (B - Bsum 13)) := by
    simpa using (CdtTwoCore.hasSum_sq2 13).mul_left ((232305764061280 : ℝ) / 2187)
  have h43 : HasSum (fun m : ℕ => (246115213795000 : ℝ) / 2187 * (1 / (xm m 43)^2))
      ((246115213795000 : ℝ) / 2187 * (A - Asum 14)) := by
    simpa using (CdtTwoCore.hasSum_sq1 14).mul_left ((246115213795000 : ℝ) / 2187)
  have h44 : HasSum (fun m : ℕ => (-(253502805085180 : ℝ)) / 2187 * (1 / (xm m 44)^2))
      ((-(253502805085180 : ℝ)) / 2187 * (B - Bsum 14)) := by
    simpa using (CdtTwoCore.hasSum_sq2 14).mul_left ((-(253502805085180 : ℝ)) / 2187)
  have h46 : HasSum (fun m : ℕ => (84355965201800 : ℝ) / 6561 * (1 / (xm m 46)^2))
      ((84355965201800 : ℝ) / 6561 * (A - Asum 15)) := by
    simpa using (CdtTwoCore.hasSum_sq1 15).mul_left ((84355965201800 : ℝ) / 6561)
  have h47 : HasSum (fun m : ℕ => (137077034179624 : ℝ) / 6561 * (1 / (xm m 47)^2))
      ((137077034179624 : ℝ) / 6561 * (B - Bsum 15)) := by
    simpa using (CdtTwoCore.hasSum_sq2 15).mul_left ((137077034179624 : ℝ) / 6561)
  have h49 : HasSum (fun m : ℕ => (-(42916885162400 : ℝ)) / 2187 * (1 / (xm m 49)^2))
      ((-(42916885162400 : ℝ)) / 2187 * (A - Asum 16)) := by
    simpa using (CdtTwoCore.hasSum_sq1 16).mul_left ((-(42916885162400 : ℝ)) / 2187)
  have h50 : HasSum (fun m : ℕ => (17930487272588 : ℝ) / 2187 * (1 / (xm m 50)^2))
      ((17930487272588 : ℝ) / 2187 * (B - Bsum 16)) := by
    simpa using (CdtTwoCore.hasSum_sq2 16).mul_left ((17930487272588 : ℝ) / 2187)
  have h52 : HasSum (fun m : ℕ => (4113550681835 : ℝ) / 2187 * (1 / (xm m 52)^2))
      ((4113550681835 : ℝ) / 2187 * (A - Asum 17)) := by
    simpa using (CdtTwoCore.hasSum_sq1 17).mul_left ((4113550681835 : ℝ) / 2187)
  have h53 : HasSum (fun m : ℕ => (-(3975717798800 : ℝ)) / 2187 * (1 / (xm m 53)^2))
      ((-(3975717798800 : ℝ)) / 2187 * (B - Bsum 17)) := by
    simpa using (CdtTwoCore.hasSum_sq2 17).mul_left ((-(3975717798800 : ℝ)) / 2187)
  have h55 : HasSum (fun m : ℕ => (2608593115310 : ℝ) / 6561 * (1 / (xm m 55)^2))
      ((2608593115310 : ℝ) / 6561 * (A - Asum 18)) := by
    simpa using (CdtTwoCore.hasSum_sq1 18).mul_left ((2608593115310 : ℝ) / 6561)
  have h56 : HasSum (fun m : ℕ => (-(711868389650 : ℝ)) / 6561 * (1 / (xm m 56)^2))
      ((-(711868389650 : ℝ)) / 6561 * (B - Bsum 18)) := by
    simpa using (CdtTwoCore.hasSum_sq2 18).mul_left ((-(711868389650 : ℝ)) / 6561)
  exact (((((((((((((((((((((((((((((((h10.add h11).add h13).add h14).add h16).add h17).add h19).add h20).add h22).add h23).add h25).add h26).add h28).add h29).add h31).add h32).add h34).add h35).add h37).add h38).add h40).add h41).add h43).add h44).add h46).add h47).add h49).add h50).add h52).add h53).add h55).add h56)

lemma hasSum_W29 : HasSum W29 V2val9 := by
  have hp10 : HasSum (fun m : ℕ => (73834838343949 : ℝ) / 1565979480 * (1 / xm m 10 - 1 / xm m (10 + 3)))
      ((73834838343949 : ℝ) / 1565979480 * (1 / xm 0 10)) := by
    simpa using (CdtTwoCore.hasSum_pair 10 (by norm_num)).mul_left ((73834838343949 : ℝ) / 1565979480)
  have hp11 : HasSum (fun m : ℕ => (-(358986576880223 : ℝ)) / 1722577428 * (1 / xm m 11 - 1 / xm m (11 + 3)))
      ((-(358986576880223 : ℝ)) / 1722577428 * (1 / xm 0 11)) := by
    simpa using (CdtTwoCore.hasSum_pair 11 (by norm_num)).mul_left ((-(358986576880223 : ℝ)) / 1722577428)
  have hp12 : HasSum (fun m : ℕ => (-(2453663097 : ℝ)) / 1360 * (1 / xm m 12 - 1 / xm m (12 + 3)))
      ((-(2453663097 : ℝ)) / 1360 * (1 / xm 0 12)) := by
    simpa using (CdtTwoCore.hasSum_pair 12 (by norm_num)).mul_left ((-(2453663097 : ℝ)) / 1360)
  have hp13 : HasSum (fun m : ℕ => (180862049695590059 : ℝ) / 17225774280 * (1 / xm m 13 - 1 / xm m (13 + 3)))
      ((180862049695590059 : ℝ) / 17225774280 * (1 / xm 0 13)) := by
    simpa using (CdtTwoCore.hasSum_pair 13 (by norm_num)).mul_left ((180862049695590059 : ℝ) / 17225774280)
  have hp14 : HasSum (fun m : ℕ => (-(5127197954934689 : ℝ)) / 430644357 * (1 / xm m 14 - 1 / xm m (14 + 3)))
      ((-(5127197954934689 : ℝ)) / 430644357 * (1 / xm 0 14)) := by
    simpa using (CdtTwoCore.hasSum_pair 14 (by norm_num)).mul_left ((-(5127197954934689 : ℝ)) / 430644357)
  have hp15 : HasSum (fun m : ℕ => (46619598843 : ℝ) / 9520 * (1 / xm m 15 - 1 / xm m (15 + 3)))
      ((46619598843 : ℝ) / 9520 * (1 / xm 0 15)) := by
    simpa using (CdtTwoCore.hasSum_pair 15 (by norm_num)).mul_left ((46619598843 : ℝ) / 9520)
  have hp16 : HasSum (fun m : ℕ => (-(2747448774152478947 : ℝ)) / 34451548560 * (1 / xm m 16 - 1 / xm m (16 + 3)))
      ((-(2747448774152478947 : ℝ)) / 34451548560 * (1 / xm 0 16)) := by
    simpa using (CdtTwoCore.hasSum_pair 16 (by norm_num)).mul_left ((-(2747448774152478947 : ℝ)) / 34451548560)
  have hp17 : HasSum (fun m : ℕ => (56299376823384077 : ℝ) / 2153221785 * (1 / xm m 17 - 1 / xm m (17 + 3)))
      ((56299376823384077 : ℝ) / 2153221785 * (1 / xm 0 17)) := by
    simpa using (CdtTwoCore.hasSum_pair 17 (by norm_num)).mul_left ((56299376823384077 : ℝ) / 2153221785)
  have hp18 : HasSum (fun m : ℕ => (1023177511449 : ℝ) / 1360 * (1 / xm m 18 - 1 / xm m (18 + 3)))
      ((1023177511449 : ℝ) / 1360 * (1 / xm 0 18)) := by
    simpa using (CdtTwoCore.hasSum_pair 18 (by norm_num)).mul_left ((1023177511449 : ℝ) / 1360)
  have hp19 : HasSum (fun m : ℕ => (-(47083617883937152627 : ℝ)) / 34451548560 * (1 / xm m 19 - 1 / xm m (19 + 3)))
      ((-(47083617883937152627 : ℝ)) / 34451548560 * (1 / xm 0 19)) := by
    simpa using (CdtTwoCore.hasSum_pair 19 (by norm_num)).mul_left ((-(47083617883937152627 : ℝ)) / 34451548560)
  have hp20 : HasSum (fun m : ℕ => (1307468594386437761 : ℝ) / 1325059560 * (1 / xm m 20 - 1 / xm m (20 + 3)))
      ((1307468594386437761 : ℝ) / 1325059560 * (1 / xm 0 20)) := by
    simpa using (CdtTwoCore.hasSum_pair 20 (by norm_num)).mul_left ((1307468594386437761 : ℝ) / 1325059560)
  have hp21 : HasSum (fun m : ℕ => (-(467700083908461 : ℝ)) / 123760 * (1 / xm m 21 - 1 / xm m (21 + 3)))
      ((-(467700083908461 : ℝ)) / 123760 * (1 / xm 0 21)) := by
    simpa using (CdtTwoCore.hasSum_pair 21 (by norm_num)).mul_left ((-(467700083908461 : ℝ)) / 123760)
  have hp22 : HasSum (fun m : ℕ => (278998770269750798717 : ℝ) / 34451548560 * (1 / xm m 22 - 1 / xm m (22 + 3)))
      ((278998770269750798717 : ℝ) / 34451548560 * (1 / xm 0 22)) := by
    simpa using (CdtTwoCore.hasSum_pair 22 (by norm_num)).mul_left ((278998770269750798717 : ℝ) / 34451548560)
  have hp23 : HasSum (fun m : ℕ => (-(12754996673051891857 : ℝ)) / 17225774280 * (1 / xm m 23 - 1 / xm m (23 + 3)))
      ((-(12754996673051891857 : ℝ)) / 17225774280 * (1 / xm 0 23)) := by
    simpa using (CdtTwoCore.hasSum_pair 23 (by norm_num)).mul_left ((-(12754996673051891857 : ℝ)) / 17225774280)
  have hp24 : HasSum (fun m : ℕ => (-(11428065918421641 : ℝ)) / 1361360 * (1 / xm m 24 - 1 / xm m (24 + 3)))
      ((-(11428065918421641 : ℝ)) / 1361360 * (1 / xm 0 24)) := by
    simpa using (CdtTwoCore.hasSum_pair 24 (by norm_num)).mul_left ((-(11428065918421641 : ℝ)) / 1361360)
  have hp25 : HasSum (fun m : ℕ => (37460705804159755853 : ℝ) / 34451548560 * (1 / xm m 25 - 1 / xm m (25 + 3)))
      ((37460705804159755853 : ℝ) / 34451548560 * (1 / xm 0 25)) := by
    simpa using (CdtTwoCore.hasSum_pair 25 (by norm_num)).mul_left ((37460705804159755853 : ℝ) / 34451548560)
  have hp26 : HasSum (fun m : ℕ => (-(149060964191141136461 : ℝ)) / 8612887140 * (1 / xm m 26 - 1 / xm m (26 + 3)))
      ((-(149060964191141136461 : ℝ)) / 8612887140 * (1 / xm 0 26)) := by
    simpa using (CdtTwoCore.hasSum_pair 26 (by norm_num)).mul_left ((-(149060964191141136461 : ℝ)) / 8612887140)
  have hp27 : HasSum (fun m : ℕ => (6983319013446663 : ℝ) / 104720 * (1 / xm m 27 - 1 / xm m (27 + 3)))
      ((6983319013446663 : ℝ) / 104720 * (1 / xm 0 27)) := by
    simpa using (CdtTwoCore.hasSum_pair 27 (by norm_num)).mul_left ((6983319013446663 : ℝ) / 104720)
  have hp28 : HasSum (fun m : ℕ => (-(4904093445886785286 : ℝ)) / 79748955 * (1 / xm m 28 - 1 / xm m (28 + 3)))
      ((-(4904093445886785286 : ℝ)) / 79748955 * (1 / xm 0 28)) := by
    simpa using (CdtTwoCore.hasSum_pair 28 (by norm_num)).mul_left ((-(4904093445886785286 : ℝ)) / 79748955)
  have hp29 : HasSum (fun m : ℕ => (67579794830728691029 : ℝ) / 2232970740 * (1 / xm m 29 - 1 / xm m (29 + 3)))
      ((67579794830728691029 : ℝ) / 2232970740 * (1 / xm 0 29)) := by
    simpa using (CdtTwoCore.hasSum_pair 29 (by norm_num)).mul_left ((67579794830728691029 : ℝ) / 2232970740)
  have hp30 : HasSum (fun m : ℕ => (-(9946764970131771 : ℝ)) / 123760 * (1 / xm m 30 - 1 / xm m (30 + 3)))
      ((-(9946764970131771 : ℝ)) / 123760 * (1 / xm 0 30)) := by
    simpa using (CdtTwoCore.hasSum_pair 30 (by norm_num)).mul_left ((-(9946764970131771 : ℝ)) / 123760)
  have hp31 : HasSum (fun m : ℕ => (53848123721928614497 : ℝ) / 637991640 * (1 / xm m 31 - 1 / xm m (31 + 3)))
      ((53848123721928614497 : ℝ) / 637991640 * (1 / xm 0 31)) := by
    simpa using (CdtTwoCore.hasSum_pair 31 (by norm_num)).mul_left ((53848123721928614497 : ℝ) / 637991640)
  have hp32 : HasSum (fun m : ℕ => (387880612235350374643 : ℝ) / 8931882960 * (1 / xm m 32 - 1 / xm m (32 + 3)))
      ((387880612235350374643 : ℝ) / 8931882960 * (1 / xm 0 32)) := by
    simpa using (CdtTwoCore.hasSum_pair 32 (by norm_num)).mul_left ((387880612235350374643 : ℝ) / 8931882960)
  have hp33 : HasSum (fun m : ℕ => (-(9946764970131771 : ℝ)) / 123760 * (1 / xm m 33 - 1 / xm m (33 + 3)))
      ((-(9946764970131771 : ℝ)) / 123760 * (1 / xm 0 33)) := by
    simpa using (CdtTwoCore.hasSum_pair 33 (by norm_num)).mul_left ((-(9946764970131771 : ℝ)) / 123760)
  have hp34 : HasSum (fun m : ℕ => (708226381220574527 : ℝ) / 24538140 * (1 / xm m 34 - 1 / xm m (34 + 3)))
      ((708226381220574527 : ℝ) / 24538140 * (1 / xm 0 34)) := by
    simpa using (CdtTwoCore.hasSum_pair 34 (by norm_num)).mul_left ((708226381220574527 : ℝ) / 24538140)
  have hp35 : HasSum (fun m : ℕ => (-(1094037352368808966421 : ℝ)) / 8931882960 * (1 / xm m 35 - 1 / xm m (35 + 3)))
      ((-(1094037352368808966421 : ℝ)) / 8931882960 * (1 / xm 0 35)) := by
    simpa using (CdtTwoCore.hasSum_pair 35 (by norm_num)).mul_left ((-(1094037352368808966421 : ℝ)) / 8931882960)
  have hp36 : HasSum (fun m : ℕ => (1612674977829444 : ℝ) / 7735 * (1 / xm m 36 - 1 / xm m (36 + 3)))
      ((1612674977829444 : ℝ) / 7735 * (1 / xm 0 36)) := by
    simpa using (CdtTwoCore.hasSum_pair 36 (by norm_num)).mul_left ((1612674977829444 : ℝ) / 7735)
  have hp37 : HasSum (fun m : ℕ => (-(903814450480016249089 : ℝ)) / 8612887140 * (1 / xm m 37 - 1 / xm m (37 + 3)))
      ((-(903814450480016249089 : ℝ)) / 8612887140 * (1 / xm 0 37)) := by
    simpa using (CdtTwoCore.hasSum_pair 37 (by norm_num)).mul_left ((-(903814450480016249089 : ℝ)) / 8612887140)
  have hp38 : HasSum (fun m : ℕ => (10257883818182378321953 : ℝ) / 241160839920 * (1 / xm m 38 - 1 / xm m (38 + 3)))
      ((10257883818182378321953 : ℝ) / 241160839920 * (1 / xm 0 38)) := by
    simpa using (CdtTwoCore.hasSum_pair 38 (by norm_num)).mul_left ((10257883818182378321953 : ℝ) / 241160839920)
  have hp39 : HasSum (fun m : ℕ => (-(411584808880071 : ℝ)) / 4760 * (1 / xm m 39 - 1 / xm m (39 + 3)))
      ((-(411584808880071 : ℝ)) / 4760 * (1 / xm 0 39)) := by
    simpa using (CdtTwoCore.hasSum_pair 39 (by norm_num)).mul_left ((-(411584808880071 : ℝ)) / 4760)
  have hp40 : HasSum (fun m : ℕ => (1107954397571751413441 : ℝ) / 34451548560 * (1 / xm m 40 - 1 / xm m (40 + 3)))
      ((1107954397571751413441 : ℝ) / 34451548560 * (1 / xm 0 40)) := by
    simpa using (CdtTwoCore.hasSum_pair 40 (by norm_num)).mul_left ((1107954397571751413441 : ℝ) / 34451548560)
  have hp41 : HasSum (fun m : ℕ => (14697144396974365714033 : ℝ) / 241160839920 * (1 / xm m 41 - 1 / xm m (41 + 3)))
      ((14697144396974365714033 : ℝ) / 241160839920 * (1 / xm 0 41)) := by
    simpa using (CdtTwoCore.hasSum_pair 41 (by norm_num)).mul_left ((14697144396974365714033 : ℝ) / 241160839920)
  have hp42 : HasSum (fun m : ℕ => (-(33151442103567 : ℝ)) / 680 * (1 / xm m 42 - 1 / xm m (42 + 3)))
      ((-(33151442103567 : ℝ)) / 680 * (1 / xm 0 42)) := by
    simpa using (CdtTwoCore.hasSum_pair 42 (by norm_num)).mul_left ((-(33151442103567 : ℝ)) / 680)
  have hp43 : HasSum (fun m : ℕ => (722416830631049864441 : ℝ) / 34451548560 * (1 / xm m 43 - 1 / xm m (43 + 3)))
      ((722416830631049864441 : ℝ) / 34451548560 * (1 / xm 0 43)) := by
    simpa using (CdtTwoCore.hasSum_pair 43 (by norm_num)).mul_left ((722416830631049864441 : ℝ) / 34451548560)
  have hp44 : HasSum (fun m : ℕ => (-(49268782689753205811 : ℝ)) / 1289630160 * (1 / xm m 44 - 1 / xm m (44 + 3)))
      ((-(49268782689753205811 : ℝ)) / 1289630160 * (1 / xm 0 44)) := by
    simpa using (CdtTwoCore.hasSum_pair 44 (by norm_num)).mul_left ((-(49268782689753205811 : ℝ)) / 1289630160)
  have hp45 : HasSum (fun m : ℕ => (4585896328293 : ℝ) / 136 * (1 / xm m 45 - 1 / xm m (45 + 3)))
      ((4585896328293 : ℝ) / 136 * (1 / xm 0 45)) := by
    simpa using (CdtTwoCore.hasSum_pair 45 (by norm_num)).mul_left ((4585896328293 : ℝ) / 136)
  have hp46 : HasSum (fun m : ℕ => (-(213348134488954669679 : ℝ)) / 34451548560 * (1 / xm m 46 - 1 / xm m (46 + 3)))
      ((-(213348134488954669679 : ℝ)) / 34451548560 * (1 / xm 0 46)) := by
    simpa using (CdtTwoCore.hasSum_pair 46 (by norm_num)).mul_left ((-(213348134488954669679 : ℝ)) / 34451548560)
  have hp47 : HasSum (fun m : ℕ => (-(51005926223417397431 : ℝ)) / 21923712720 * (1 / xm m 47 - 1 / xm m (47 + 3)))
      ((-(51005926223417397431 : ℝ)) / 21923712720 * (1 / xm 0 47)) := by
    simpa using (CdtTwoCore.hasSum_pair 47 (by norm_num)).mul_left ((-(51005926223417397431 : ℝ)) / 21923712720)
  have hp48 : HasSum (fun m : ℕ => (-(4907326194 : ℝ)) / 17 * (1 / xm m 48 - 1 / xm m (48 + 3)))
      ((-(4907326194 : ℝ)) / 17 * (1 / xm 0 48)) := by
    simpa using (CdtTwoCore.hasSum_pair 48 (by norm_num)).mul_left ((-(4907326194 : ℝ)) / 17)
  have hp49 : HasSum (fun m : ℕ => (-(55959478822287565199 : ℝ)) / 34451548560 * (1 / xm m 49 - 1 / xm m (49 + 3)))
      ((-(55959478822287565199 : ℝ)) / 34451548560 * (1 / xm 0 49)) := by
    simpa using (CdtTwoCore.hasSum_pair 49 (by norm_num)).mul_left ((-(55959478822287565199 : ℝ)) / 34451548560)
  have hp50 : HasSum (fun m : ℕ => (12714323567196633131 : ℝ) / 4384742544 * (1 / xm m 50 - 1 / xm m (50 + 3)))
      ((12714323567196633131 : ℝ) / 4384742544 * (1 / xm 0 50)) := by
    simpa using (CdtTwoCore.hasSum_pair 50 (by norm_num)).mul_left ((12714323567196633131 : ℝ) / 4384742544)
  have hp51 : HasSum (fun m : ℕ => (-(2453663097 : ℝ)) / 2 * (1 / xm m 51 - 1 / xm m (51 + 3)))
      ((-(2453663097 : ℝ)) / 2 * (1 / xm 0 51)) := by
    simpa using (CdtTwoCore.hasSum_pair 51 (by norm_num)).mul_left ((-(2453663097 : ℝ)) / 2)
  have hp52 : HasSum (fun m : ℕ => (62393981797184249 : ℝ) / 1325059560 * (1 / xm m 52 - 1 / xm m (52 + 3)))
      ((62393981797184249 : ℝ) / 1325059560 * (1 / xm 0 52)) := by
    simpa using (CdtTwoCore.hasSum_pair 52 (by norm_num)).mul_left ((62393981797184249 : ℝ) / 1325059560)
  have hp53 : HasSum (fun m : ℕ => (228355373070909923 : ℝ) / 4384742544 * (1 / xm m 53 - 1 / xm m (53 + 3)))
      ((228355373070909923 : ℝ) / 4384742544 * (1 / xm 0 53)) := by
    simpa using (CdtTwoCore.hasSum_pair 53 (by norm_num)).mul_left ((228355373070909923 : ℝ) / 4384742544)
  exact (((((((((((((((((((((((((((((((((((((((((((hp10.add hp11).add hp12).add hp13).add hp14).add hp15).add hp16).add hp17).add hp18).add hp19).add hp20).add hp21).add hp22).add hp23).add hp24).add hp25).add hp26).add hp27).add hp28).add hp29).add hp30).add hp31).add hp32).add hp33).add hp34).add hp35).add hp36).add hp37).add hp38).add hp39).add hp40).add hp41).add hp42).add hp43).add hp44).add hp45).add hp46).add hp47).add hp48).add hp49).add hp50).add hp51).add hp52).add hp53)

/-- `HasSum` for the whole summand. -/
lemma hasSum_Vm9 : HasSum Vm9 Vval9 := by
  have hsum : HasSum (fun m : ℕ => W19 m + W29 m) Vval9 := by
    simpa [Vval9] using hasSum_W19.add hasSum_W29
  apply HasSum.congr_fun hsum
  intro m
  exact vm9_decomp m

set_option maxHeartbeats 0 in
/-- The infinite sum of `Vm9` in closed form. -/
lemma tsum_Vm9 : (∑' m : ℕ, Vm9 m) = 17319837 * A - 17319837 * B - 530455590781 / 39200 := by
  have hval : Vval9 = 17319837 * A - 17319837 * B - 530455590781 / 39200 := by
    unfold Vval9 V1val9 V2val9
    norm_num [xm]
    ring
  rw [hasSum_Vm9.tsum_eq]
  exact hval

end CdtNineCore
open CdtNineCore

/-! ## Final assembly -/

/-- Creative-telescoping evaluation of the degree-9 `(Cintegral)` inner sum:
`Σₘ 387420489·C(m+18,18)·Σᵢ₌₀¹⁹(−1)ⁱC(19,i)·(7142567040/∏_{k=0}^{9}(3m+10+3k+i))²
 = 17319837·Σₖ(1/(3k+1)²−1/(3k+2)²) − 530455590781/39200`. -/
theorem sum_cintegralNine_core :
    (∑' m : ℕ,
        (387420489 : ℝ) * (Nat.choose (m + 18) 18 : ℝ) *
          (∑ i ∈ Finset.range 20,
            ((-1 : ℝ) ^ i * (Nat.choose 19 i : ℝ)) *
              (7142567040 / ((((3 * m + 10 + i : ℕ) : ℝ) * ((3 * m + 13 + i : ℕ) : ℝ) * ((3 * m + 16 + i : ℕ) : ℝ) * ((3 * m + 19 + i : ℕ) : ℝ) * ((3 * m + 22 + i : ℕ) : ℝ) * ((3 * m + 25 + i : ℕ) : ℝ) * ((3 * m + 28 + i : ℕ) : ℝ) * ((3 * m + 31 + i : ℕ) : ℝ) * ((3 * m + 34 + i : ℕ) : ℝ) * ((3 * m + 37 + i : ℕ) : ℝ)))) ^ 2)) =
      17319837 * (∑' k : ℕ,
          ((1 : ℝ) / (((3 * k + 1 : ℕ) : ℝ) ^ 2) - (1 : ℝ) / (((3 * k + 2 : ℕ) : ℝ) ^ 2))) - 530455590781 / 39200 := by
  have hMain := tsum_Vm9
  have hL : (∑' m : ℕ, Vm9 m) =
      (∑' m : ℕ,
        (387420489 : ℝ) * (Nat.choose (m + 18) 18 : ℝ) *
          (∑ i ∈ Finset.range 20,
            ((-1 : ℝ) ^ i * (Nat.choose 19 i : ℝ)) *
              (7142567040 / ((((3 * m + 10 + i : ℕ) : ℝ) * ((3 * m + 13 + i : ℕ) : ℝ) *
                ((3 * m + 16 + i : ℕ) : ℝ) * ((3 * m + 19 + i : ℕ) : ℝ) *
                  ((3 * m + 22 + i : ℕ) : ℝ) * ((3 * m + 25 + i : ℕ) : ℝ) *
                    ((3 * m + 28 + i : ℕ) : ℝ) * ((3 * m + 31 + i : ℕ) : ℝ) *
                      ((3 * m + 34 + i : ℕ) : ℝ) * ((3 * m + 37 + i : ℕ) : ℝ)))) ^ 2)) := by
    apply tsum_congr
    intro m
    exact (vm9_eq_statement m).symm
  rw [← hL]
  rw [hMain]
  have hR : (∑' k : ℕ,
      ((1 : ℝ) / (((3 * k + 1 : ℕ) : ℝ) ^ 2) - (1 : ℝ) / (((3 * k + 2 : ℕ) : ℝ) ^ 2))) = A - B := by
    simpa [Rk, f1, f2, xm] using tsum_Rk
  rw [hR]
  ring

end Commons.Analysis.Summation
