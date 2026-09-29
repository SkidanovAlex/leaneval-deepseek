import Mathlib
import Submission.Commons.Analysis.Summation.sum_cintegralFour_core

noncomputable section
open scoped BigOperators Nat
open Filter Topology

namespace Commons.Analysis.Summation
namespace CdtTenCore

/-! ## Binomial `(m+20 choose 20)` as a degree-20 polynomial -/

set_option maxHeartbeats 0 in
lemma asc20 (n : ℕ) : n.ascFactorial 20 =
    (n + 0) * (n + 1) * (n + 2) * (n + 3) * (n + 4) * (n + 5) * (n + 6) * (n + 7) * (n + 8) * (n + 9) * (n + 10) * (n + 11) * (n + 12) * (n + 13) * (n + 14) * (n + 15) * (n + 16) * (n + 17) * (n + 18) * (n + 19) := by
  simp [Nat.ascFactorial_succ, Nat.ascFactorial_zero]
  ring

lemma factorial_add_twenty (m : ℕ) : (m + 20)! =
    m ! * ((m + 1) * (m + 2) * (m + 3) * (m + 4) * (m + 5) * (m + 6) * (m + 7) * (m + 8) * (m + 9) * (m + 10) * (m + 11) * (m + 12) * (m + 13) * (m + 14) * (m + 15) * (m + 16) * (m + 17) * (m + 18) * (m + 19) * (m + 20)) := by
  rw [← Nat.factorial_mul_ascFactorial m 20]
  have h := asc20 (m + 1)
  rw [h]

set_option maxHeartbeats 0 in
lemma choose2020 (m : ℕ) :
    (Nat.choose (m + 20) 20 : ℝ) =
      (1 / 2432902008176640000 : ℝ) *
        (((m : ℝ) + 1) * ((m : ℝ) + 2) * ((m : ℝ) + 3) * ((m : ℝ) + 4) * ((m : ℝ) + 5) * ((m : ℝ) + 6) * ((m : ℝ) + 7) * ((m : ℝ) + 8) * ((m : ℝ) + 9) * ((m : ℝ) + 10) * ((m : ℝ) + 11) * ((m : ℝ) + 12) * ((m : ℝ) + 13) * ((m : ℝ) + 14) * ((m : ℝ) + 15) * ((m : ℝ) + 16) * ((m : ℝ) + 17) * ((m : ℝ) + 18) * ((m : ℝ) + 19) * ((m : ℝ) + 20)) := by
  have hcast := Nat.cast_choose ℝ (a := 20) (b := m + 20) (by omega : 20 ≤ m + 20)
  rw [hcast]
  have h20 : ((20 : ℕ)! : ℝ) = 2432902008176640000 := by norm_num
  have hsub : ((m + 20 - 20) : ℕ) = m := by omega
  rw [h20, hsub]
  have hfacR : ((m + 20)! : ℝ) = (m ! : ℝ) *
      (((m : ℝ) + 1) * ((m : ℝ) + 2) * ((m : ℝ) + 3) * ((m : ℝ) + 4) * ((m : ℝ) + 5) * ((m : ℝ) + 6) * ((m : ℝ) + 7) * ((m : ℝ) + 8) * ((m : ℝ) + 9) * ((m : ℝ) + 10) * ((m : ℝ) + 11) * ((m : ℝ) + 12) * ((m : ℝ) + 13) * ((m : ℝ) + 14) * ((m : ℝ) + 15) * ((m : ℝ) + 16) * ((m : ℝ) + 17) * ((m : ℝ) + 18) * ((m : ℝ) + 19) * ((m : ℝ) + 20)) := by
    norm_num [factorial_add_twenty, Nat.cast_mul]
  rw [hfacR]
  have hm : (m ! : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_ne_zero m)
  field_simp [hm]

@[simp] lemma c21_0 : (Nat.choose 21 0 : ℝ) = 1 := by
  rw [Nat.cast_choose ℝ (by decide : 0 ≤ 21)]; norm_num
@[simp] lemma c21_1 : (Nat.choose 21 1 : ℝ) = 21 := by
  rw [Nat.cast_choose ℝ (by decide : 1 ≤ 21)]; norm_num
@[simp] lemma c21_2 : (Nat.choose 21 2 : ℝ) = 210 := by
  rw [Nat.cast_choose ℝ (by decide : 2 ≤ 21)]; norm_num
@[simp] lemma c21_3 : (Nat.choose 21 3 : ℝ) = 1330 := by
  rw [Nat.cast_choose ℝ (by decide : 3 ≤ 21)]; norm_num
@[simp] lemma c21_4 : (Nat.choose 21 4 : ℝ) = 5985 := by
  rw [Nat.cast_choose ℝ (by decide : 4 ≤ 21)]; norm_num
@[simp] lemma c21_5 : (Nat.choose 21 5 : ℝ) = 20349 := by
  rw [Nat.cast_choose ℝ (by decide : 5 ≤ 21)]; norm_num
@[simp] lemma c21_6 : (Nat.choose 21 6 : ℝ) = 54264 := by
  rw [Nat.cast_choose ℝ (by decide : 6 ≤ 21)]; norm_num
@[simp] lemma c21_7 : (Nat.choose 21 7 : ℝ) = 116280 := by
  rw [Nat.cast_choose ℝ (by decide : 7 ≤ 21)]; norm_num
@[simp] lemma c21_8 : (Nat.choose 21 8 : ℝ) = 203490 := by
  rw [Nat.cast_choose ℝ (by decide : 8 ≤ 21)]; norm_num
@[simp] lemma c21_9 : (Nat.choose 21 9 : ℝ) = 293930 := by
  rw [Nat.cast_choose ℝ (by decide : 9 ≤ 21)]; norm_num
@[simp] lemma c21_10 : (Nat.choose 21 10 : ℝ) = 352716 := by
  rw [Nat.cast_choose ℝ (by decide : 10 ≤ 21)]; norm_num
@[simp] lemma c21_11 : (Nat.choose 21 11 : ℝ) = 352716 := by
  rw [Nat.cast_choose ℝ (by decide : 11 ≤ 21)]; norm_num
@[simp] lemma c21_12 : (Nat.choose 21 12 : ℝ) = 293930 := by
  rw [Nat.cast_choose ℝ (by decide : 12 ≤ 21)]; norm_num
@[simp] lemma c21_13 : (Nat.choose 21 13 : ℝ) = 203490 := by
  rw [Nat.cast_choose ℝ (by decide : 13 ≤ 21)]; norm_num
@[simp] lemma c21_14 : (Nat.choose 21 14 : ℝ) = 116280 := by
  rw [Nat.cast_choose ℝ (by decide : 14 ≤ 21)]; norm_num
@[simp] lemma c21_15 : (Nat.choose 21 15 : ℝ) = 54264 := by
  rw [Nat.cast_choose ℝ (by decide : 15 ≤ 21)]; norm_num
@[simp] lemma c21_16 : (Nat.choose 21 16 : ℝ) = 20349 := by
  rw [Nat.cast_choose ℝ (by decide : 16 ≤ 21)]; norm_num
@[simp] lemma c21_17 : (Nat.choose 21 17 : ℝ) = 5985 := by
  rw [Nat.cast_choose ℝ (by decide : 17 ≤ 21)]; norm_num
@[simp] lemma c21_18 : (Nat.choose 21 18 : ℝ) = 1330 := by
  rw [Nat.cast_choose ℝ (by decide : 18 ≤ 21)]; norm_num
@[simp] lemma c21_19 : (Nat.choose 21 19 : ℝ) = 210 := by
  rw [Nat.cast_choose ℝ (by decide : 19 ≤ 21)]; norm_num
@[simp] lemma c21_20 : (Nat.choose 21 20 : ℝ) = 21 := by
  rw [Nat.cast_choose ℝ (by decide : 20 ≤ 21)]; norm_num
@[simp] lemma c21_21 : (Nat.choose 21 21 : ℝ) = 1 := by
  rw [Nat.cast_choose ℝ (by decide : 21 ≤ 21)]; norm_num

/-! ## The `m`-summand and its pointwise closed-form decomposition -/

/-- The `m`-summand of the ten-core sum. -/
def Vm10 (m : ℕ) : ℝ :=
  (3486784401 : ℝ) * (Nat.choose (m + 20) 20 : ℝ) *
    (∑ i ∈ Finset.range 22,
      ((-1 : ℝ) ^ i * (Nat.choose 21 i : ℝ)) *
        (214277011200 / (xm m (11 + i) * xm m (14 + i) * xm m (17 + i) * xm m (20 + i) * xm m (23 + i) * xm m (26 + i) * xm m (29 + i) * xm m (32 + i) * xm m (35 + i) * xm m (38 + i) * xm m (41 + i))) ^ 2)

/-- Squared-term part of the closed-form decomposition. -/
def W110 (m : ℕ) : ℝ :=
  ((-(555847670 : ℝ)) / 6561) * (1 / (xm m 11)^2)
    +   ((13855631020 : ℝ) / 2187) * (1 / (xm m 13)^2)
    +   ((-(51160673300 : ℝ)) / 2187) * (1 / (xm m 14)^2)
    +   ((-(11880466598 : ℝ)) / 2187) * (1 / (xm m 16)^2)
    +   ((2913266687870 : ℝ) / 6561) * (1 / (xm m 17)^2)
    +   ((-(345613573760 : ℝ)) / 81) * (1 / (xm m 19)^2)
    +   ((36839215012600 : ℝ) / 6561) * (1 / (xm m 20)^2)
    +   ((55929028741768 : ℝ) / 2187) * (1 / (xm m 22)^2)
    +   ((-(51446784593050 : ℝ)) / 729) * (1 / (xm m 23)^2)
    +   ((165843729010960 : ℝ) / 2187) * (1 / (xm m 25)^2)
    +   ((732385936355150 : ℝ) / 6561) * (1 / (xm m 26)^2)
    +   ((-(189853839346600 : ℝ)) / 243) * (1 / (xm m 28)^2)
    +   ((4761117472711600 : ℝ) / 6561) * (1 / (xm m 29)^2)
    +   ((3167729640200125 : ℝ) / 2187) * (1 / (xm m 31)^2)
    +   ((-(6067012295869525 : ℝ)) / 2187) * (1 / (xm m 32)^2)
    +   ((2217743083130575 : ℝ) / 2187) * (1 / (xm m 34)^2)
    +   ((15673897713273800 : ℝ) / 6561) * (1 / (xm m 35)^2)
    +   ((-(166609791610955 : ℝ)) / 27) * (1 / (xm m 37)^2)
    +   ((21943456798583320 : ℝ) / 6561) * (1 / (xm m 38)^2)
    +   ((13875891882570025 : ℝ) / 2187) * (1 / (xm m 40)^2)
    +   ((-(16767015799493960 : ℝ)) / 2187) * (1 / (xm m 41)^2)
    +   ((399002261396200 : ℝ) / 2187) * (1 / (xm m 43)^2)
    +   ((26561729853626240 : ℝ) / 6561) * (1 / (xm m 44)^2)
    +   ((-(112197662303650 : ℝ)) / 27) * (1 / (xm m 46)^2)
    +   ((8592401835477460 : ℝ) / 6561) * (1 / (xm m 47)^2)
    +   ((4789179327502900 : ℝ) / 2187) * (1 / (xm m 49)^2)
    +   ((-(1356480132489020 : ℝ)) / 729) * (1 / (xm m 50)^2)
    +   ((100412214042490 : ℝ) / 2187) * (1 / (xm m 52)^2)
    +   ((2428318098806600 : ℝ) / 6561) * (1 / (xm m 53)^2)
    +   ((-(58837865488675 : ℝ)) / 243) * (1 / (xm m 55)^2)
    +   ((574822484615170 : ℝ) / 6561) * (1 / (xm m 56)^2)
    +   ((51467325384475 : ℝ) / 2187) * (1 / (xm m 58)^2)
    +   ((-(43011837437800 : ℝ)) / 2187) * (1 / (xm m 59)^2)
    +   ((8067851006215 : ℝ) / 2187) * (1 / (xm m 61)^2)
    +   ((-(6189508314220 : ℝ)) / 6561) * (1 / (xm m 62)^2)

/-- Telescoping-pair part of the closed-form decomposition. -/
def W210 (m : ℕ) : ℝ :=
  ((21973444702042219 : ℝ) / 327289711320) * (1 / xm m 11 - 1 / xm m 14)
    +   ((8135830269 : ℝ) / 6460) * (1 / xm m 12 - 1 / xm m 15)
    +   ((-(26118754940857061 : ℝ)) / 1983574008) * (1 / xm m 13 - 1 / xm m 16)
    +   ((7398088921500804649 : ℝ) / 327289711320) * (1 / xm m 14 - 1 / xm m 17)
    +   ((1537671920841 : ℝ) / 25840) * (1 / xm m 15 - 1 / xm m 18)
    +   ((-(2575669444559325121 : ℝ)) / 19835740080) * (1 / xm m 16 - 1 / xm m 19)
    +   ((1430406153685657243 : ℝ) / 10909657044) * (1 / xm m 17 - 1 / xm m 20)
    +   ((-(812420765433 : ℝ)) / 380) * (1 / xm m 18 - 1 / xm m 21)
    +   ((1410580259001316035829 : ℝ) / 218193140880) * (1 / xm m 19 - 1 / xm m 22)
    +   ((-(124505015881429435253 : ℝ)) / 32728971132) * (1 / xm m 20 - 1 / xm m 23)
    +   ((-(176753237116959 : ℝ)) / 180880) * (1 / xm m 21 - 1 / xm m 24)
    +   ((-(209202929829789839209 : ℝ)) / 14546209392) * (1 / xm m 22 - 1 / xm m 25)
    +   ((-(622975458121977969703 : ℝ)) / 65457942264) * (1 / xm m 23 - 1 / xm m 26)
    +   ((309958058465688303 : ℝ) / 2351440) * (1 / xm m 24 - 1 / xm m 27)
    +   ((-(7318210295899567247123 : ℝ)) / 43638628176) * (1 / xm m 25 - 1 / xm m 28)
    +   ((324129560055939567962 : ℝ) / 2727414261) * (1 / xm m 26 - 1 / xm m 29)
    +   ((-(987988613242027167 : ℝ)) / 2351440) * (1 / xm m 27 - 1 / xm m 30)
    +   ((28362180257517361231465 : ℝ) / 43638628176) * (1 / xm m 28 - 1 / xm m 31)
    +   ((79207613991153529978 : ℝ) / 8182242783) * (1 / xm m 29 - 1 / xm m 32)
    +   ((-(736201502936088129 : ℝ)) / 1989680) * (1 / xm m 30 - 1 / xm m 33)
    +   ((-(1233178738516790211703 : ℝ)) / 10909657044) * (1 / xm m 31 - 1 / xm m 34)
    +   ((-(140996035960153961227535 : ℝ)) / 130915884528) * (1 / xm m 32 - 1 / xm m 35)
    +   ((7332482289755360583 : ℝ) / 2351440) * (1 / xm m 33 - 1 / xm m 36)
    +   ((-(3679152107756964156713 : ℝ)) / 1616245488) * (1 / xm m 34 - 1 / xm m 37)
    +   ((16518754023027036050747 : ℝ) / 11313718416) * (1 / xm m 35 - 1 / xm m 38)
    +   ((-(1670593522315450743 : ℝ)) / 470288) * (1 / xm m 36 - 1 / xm m 39)
    +   ((1419782132197788520514 : ℝ) / 505076715) * (1 / xm m 37 - 1 / xm m 40)
    +   ((64733484688498613906071 : ℝ) / 53906540688) * (1 / xm m 38 - 1 / xm m 41)
    +   ((-(12680087805396747 : ℝ)) / 9044) * (1 / xm m 39 - 1 / xm m 42)
    +   ((78881350566468547298083 : ℝ) / 218193140880) * (1 / xm m 40 - 1 / xm m 43)
    +   ((-(15152482967753182680069449 : ℝ)) / 4582055958480) * (1 / xm m 41 - 1 / xm m 44)
    +   ((24264640736875431 : ℝ) / 5168) * (1 / xm m 42 - 1 / xm m 45)
    +   ((-(448445525759920459998037 : ℝ)) / 218193140880) * (1 / xm m 43 - 1 / xm m 46)
    +   ((170320665503925346136087 : ℝ) / 138850180560) * (1 / xm m 44 - 1 / xm m 47)
    +   ((-(5218603964073081 : ℝ)) / 2584) * (1 / xm m 45 - 1 / xm m 48)
    +   ((129870913346747945633033 : ℝ) / 218193140880) * (1 / xm m 46 - 1 / xm m 49)
    +   ((80607929676583335472699 : ℝ) / 83310108336) * (1 / xm m 47 - 1 / xm m 50)
    +   ((-(402471387577161 : ℝ)) / 646) * (1 / xm m 48 - 1 / xm m 51)
    +   ((21693613135982147632031 : ℝ) / 72731046960) * (1 / xm m 49 - 1 / xm m 52)
    +   ((-(50135369727948829332707 : ℝ)) / 83310108336) * (1 / xm m 50 - 1 / xm m 53)
    +   ((177710940565767 : ℝ) / 380) * (1 / xm m 51 - 1 / xm m 54)
    +   ((-(1294886086590343475117 : ℝ)) / 16784087760) * (1 / xm m 52 - 1 / xm m 55)
    +   ((-(470192726745868768693 : ℝ)) / 27770036112) * (1 / xm m 53 - 1 / xm m 56)
    +   ((-(3880791038313 : ℝ)) / 380) * (1 / xm m 54 - 1 / xm m 57)
    +   ((-(14592562116016539641 : ℝ)) / 762913080) * (1 / xm m 55 - 1 / xm m 58)
    +   ((943859677606613412607 : ℝ) / 29753610120) * (1 / xm m 56 - 1 / xm m 59)
    +   ((-(24407490807 : ℝ)) / 2) * (1 / xm m 57 - 1 / xm m 60)
    +   ((490767876101998873 : ℝ) / 1525826160) * (1 / xm m 58 - 1 / xm m 61)
    +   ((14367253384165633117 : ℝ) / 29753610120) * (1 / xm m 59 - 1 / xm m 62)

/-- The closed-form decomposition of the summand (as `W110 + W210`). -/
def Vd10 (m : ℕ) : ℝ := W110 m + W210 m

set_option maxHeartbeats 0 in
lemma vm10_decomp (m : ℕ) : Vm10 m = Vd10 m := by
  unfold Vm10 Vd10 W110 W210
  rw [choose2020]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero,
    c21_0, c21_1, c21_2, c21_3, c21_4, c21_5, c21_6, c21_7, c21_8, c21_9, c21_10, c21_11, c21_12, c21_13, c21_14, c21_15, c21_16, c21_17, c21_18, c21_19, c21_20, c21_21]
  norm_num
  simp_rw [xm_eq]
  norm_num
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
  have h57 : (3 * (m : ℝ) + 57) ≠ 0 := by positivity
  have h58 : (3 * (m : ℝ) + 58) ≠ 0 := by positivity
  have h59 : (3 * (m : ℝ) + 59) ≠ 0 := by positivity
  have h60 : (3 * (m : ℝ) + 60) ≠ 0 := by positivity
  have h61 : (3 * (m : ℝ) + 61) ≠ 0 := by positivity
  have h62 : (3 * (m : ℝ) + 62) ≠ 0 := by positivity
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
  have hm19 : (m : ℝ) + 19 ≠ 0 := by positivity
  have hm20 : (m : ℝ) + 20 ≠ 0 := by positivity
  field_simp
  ring

/-! ## The statement denominators equal the `xm` denominators -/

lemma denom_statement10 (m : ℕ) : ∀ i : ℕ,
    (((3 * m + 11 + i : ℕ) : ℝ) * ((3 * m + 14 + i : ℕ) : ℝ) * ((3 * m + 17 + i : ℕ) : ℝ) * ((3 * m + 20 + i : ℕ) : ℝ) * ((3 * m + 23 + i : ℕ) : ℝ) * ((3 * m + 26 + i : ℕ) : ℝ) * ((3 * m + 29 + i : ℕ) : ℝ) * ((3 * m + 32 + i : ℕ) : ℝ) * ((3 * m + 35 + i : ℕ) : ℝ) * ((3 * m + 38 + i : ℕ) : ℝ) * ((3 * m + 41 + i : ℕ) : ℝ))
      = xm m (11 + i) * xm m (14 + i) * xm m (17 + i) *
          xm m (20 + i) * xm m (23 + i) * xm m (26 + i) *
            xm m (29 + i) * xm m (32 + i) * xm m (35 + i) *
              xm m (38 + i) * xm m (41 + i) := by
  intro i
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
  have h32 : (((3 * m + 32 + i : ℕ) : ℝ)) = xm m (32 + i) := by
    unfold xm
    congr 1
    omega
  have h35 : (((3 * m + 35 + i : ℕ) : ℝ)) = xm m (35 + i) := by
    unfold xm
    congr 1
    omega
  have h38 : (((3 * m + 38 + i : ℕ) : ℝ)) = xm m (38 + i) := by
    unfold xm
    congr 1
    omega
  have h41 : (((3 * m + 41 + i : ℕ) : ℝ)) = xm m (41 + i) := by
    unfold xm
    congr 1
    omega
  rw [h11, h14, h17, h20, h23, h26, h29, h32, h35, h38, h41]

/-- The inner `i`-sum in the statement's form equals the `xm` form. -/
lemma inner_sum_statement10 (m : ℕ) :
    (∑ i ∈ Finset.range 22,
      ((-1 : ℝ) ^ i * (Nat.choose 21 i : ℝ)) *
        (214277011200 / (((3 * m + 11 + i : ℕ) : ℝ) * ((3 * m + 14 + i : ℕ) : ℝ) * ((3 * m + 17 + i : ℕ) : ℝ) * ((3 * m + 20 + i : ℕ) : ℝ) * ((3 * m + 23 + i : ℕ) : ℝ) * ((3 * m + 26 + i : ℕ) : ℝ) * ((3 * m + 29 + i : ℕ) : ℝ) * ((3 * m + 32 + i : ℕ) : ℝ) * ((3 * m + 35 + i : ℕ) : ℝ) * ((3 * m + 38 + i : ℕ) : ℝ) * ((3 * m + 41 + i : ℕ) : ℝ))) ^ 2)
    = (∑ i ∈ Finset.range 22,
      ((-1 : ℝ) ^ i * (Nat.choose 21 i : ℝ)) *
        (214277011200 / (xm m (11 + i) * xm m (14 + i) * xm m (17 + i) * xm m (20 + i) * xm m (23 + i) * xm m (26 + i) * xm m (29 + i) * xm m (32 + i) * xm m (35 + i) * xm m (38 + i) * xm m (41 + i))) ^ 2) := by
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  rw [denom_statement10 m i]

/-- The `m`-summand of the ten-core sum, in the statement's form. -/
lemma vm10_eq_statement (m : ℕ) :
    (3486784401 : ℝ) * (Nat.choose (m + 20) 20 : ℝ) *
      (∑ i ∈ Finset.range 22,
        ((-1 : ℝ) ^ i * (Nat.choose 21 i : ℝ)) *
          (214277011200 / (((3 * m + 11 + i : ℕ) : ℝ) * ((3 * m + 14 + i : ℕ) : ℝ) * ((3 * m + 17 + i : ℕ) : ℝ) * ((3 * m + 20 + i : ℕ) : ℝ) * ((3 * m + 23 + i : ℕ) : ℝ) * ((3 * m + 26 + i : ℕ) : ℝ) * ((3 * m + 29 + i : ℕ) : ℝ) * ((3 * m + 32 + i : ℕ) : ℝ) * ((3 * m + 35 + i : ℕ) : ℝ) * ((3 * m + 38 + i : ℕ) : ℝ) * ((3 * m + 41 + i : ℕ) : ℝ))) ^ 2) =
      Vm10 m := by
  unfold Vm10
  rw [inner_sum_statement10 m]

/-! ## Small partial sums needed for the shifts -/

@[simp] lemma asum0 : Asum 0 = 0 / 1 := by
  norm_num [Asum, f1, xm]
@[simp] lemma asum1 : Asum 1 = 1 / 1 := by
  norm_num [Asum, f1, xm]
@[simp] lemma asum2 : Asum 2 = 17 / 16 := by
  norm_num [Asum, f1, xm]
@[simp] lemma asum3 : Asum 3 = 849 / 784 := by
  norm_num [Asum, f1, xm]
@[simp] lemma asum4 : Asum 4 = 21421 / 19600 := by
  norm_num [Asum, f1, xm]
@[simp] lemma asum5 : Asum 5 = 3639749 / 3312400 := by
  norm_num [Asum, f1, xm]
@[simp] lemma asum6 : Asum 6 = 58443009 / 52998400 := by
  norm_num [Asum, f1, xm]
@[simp] lemma asum7 : Asum 7 = 21150924649 / 19132422400 := by
  norm_num [Asum, f1, xm]
@[simp] lemma asum8 : Asum 8 = 2564044988129 / 2315023110400 := by
  norm_num [Asum, f1, xm]
@[simp] lemma asum9 : Asum 9 = 64193725627641 / 57875577760000 := by
  norm_num [Asum, f1, xm]
@[simp] lemma asum10 : Asum 10 = 64267546517641 / 57875577760000 := by
  norm_num [Asum, f1, xm]
@[simp] lemma asum11 : Asum 11 = 61818987781213001 / 55618430227360000 := by
  norm_num [Asum, f1, xm]
@[simp] lemma asum12 : Asum 12 = 17879592076327397289 / 16073726335707040000 := by
  norm_num [Asum, f1, xm]
@[simp] lemma asum13 : Asum 13 = 24493235278827913928641 / 22004931353582937760000 := by
  norm_num [Asum, f1, xm]
@[simp] lemma asum14 : Asum 14 = 24506988360923903264741 / 22004931353582937760000 := by
  norm_num [Asum, f1, xm]
@[simp] lemma asum15 : Asum 15 = 45335426410701880074266109 / 40687118072774851918240000 := by
  norm_num [Asum, f1, xm]
@[simp] lemma asum16 : Asum 16 = 23992612350779488272266331661 / 21523485460497896664748960000 := by
  norm_num [Asum, f1, xm]
@[simp] lemma asum17 : Asum 17 = 1176077259993511208946453291389 / 1054650787564396936572699040000 := by
  norm_num [Asum, f1, xm]
@[simp] lemma asum18 : Asum 18 = 1176467293568793900121221301389 / 1054650787564396936572699040000 := by
  norm_num [Asum, f1, xm]
@[simp] lemma asum19 : Asum 19 = 1176815938457244940430832110989 / 1054650787564396936572699040000 := by
  norm_num [Asum, f1, xm]
@[simp] lemma asum20 : Asum 20 = 989965866939434094136472980101749 / 886961312341657823657639892640000 := by
  norm_num [Asum, f1, xm]

@[simp] lemma bsum0 : Bsum 0 = 0 / 1 := by
  norm_num [Bsum, f2, xm]
@[simp] lemma bsum1 : Bsum 1 = 1 / 4 := by
  norm_num [Bsum, f2, xm]
@[simp] lemma bsum2 : Bsum 2 = 29 / 100 := by
  norm_num [Bsum, f2, xm]
@[simp] lemma bsum3 : Bsum 3 = 489 / 1600 := by
  norm_num [Bsum, f2, xm]
@[simp] lemma bsum4 : Bsum 4 = 60769 / 193600 := by
  norm_num [Bsum, f2, xm]
@[simp] lemma bsum5 : Bsum 5 = 3026081 / 9486400 := by
  norm_num [Bsum, f2, xm]
@[simp] lemma bsum6 : Bsum 6 = 884023809 / 2741569600 := by
  norm_num [Bsum, f2, xm]
@[simp] lemma bsum7 : Bsum 7 = 890877733 / 2741569600 := by
  norm_num [Bsum, f2, xm]
@[simp] lemma bsum8 : Bsum 8 = 474015890357 / 1450290318400 := by
  norm_num [Bsum, f2, xm]
@[simp] lemma bsum9 : Bsum 9 = 80471258049933 / 245099063809600 := by
  norm_num [Bsum, f2, xm]
@[simp] lemma bsum10 : Bsum 10 = 67921427083803253 / 206128312663873600 := by
  norm_num [Bsum, f2, xm]
@[simp] lemma bsum11 : Bsum 11 = 1089963588226225073 / 3298053002621977600 := by
  norm_num [Bsum, f2, xm]
@[simp] lemma bsum12 : Bsum 12 = 1092655876391630769 / 3298053002621977600 := by
  norm_num [Bsum, f2, xm]
@[simp] lemma bsum13 : Bsum 13 = 395273284628034202009 / 1190597133946533913600 := by
  norm_num [Bsum, f2, xm]
@[simp] lemma bsum14 : Bsum 14 = 665644988593672027490729 / 2001393782164123508761600 := by
  norm_num [Bsum, f2, xm]
@[simp] lemma bsum15 : Bsum 15 = 666678766373715479716329 / 2001393782164123508761600 := by
  norm_num [Bsum, f2, xm]
@[simp] lemma bsum16 : Bsum 16 = 1474694788701701618202132361 / 4421078864800548830854374400 := by
  norm_num [Bsum, f2, xm]
@[simp] lemma bsum17 : Bsum 17 = 36911580506190545943361852769 / 110526971620013720771359360000 := by
  norm_num [Bsum, f2, xm]
@[simp] lemma bsum18 : Bsum 18 = 103795156613509257275674803788121 / 310470263280618541646748442240000 := by
  norm_num [Bsum, f2, xm]
@[simp] lemma bsum19 : Bsum 19 = 103894158610728842269822363878121 / 310470263280618541646748442240000 := by
  norm_num [Bsum, f2, xm]
@[simp] lemma bsum20 : Bsum 20 = 361966036387227718482898397101979201 / 1080746986479833143472331327437440000 := by
  norm_num [Bsum, f2, xm]

/-! ## The values of the two pieces -/

/-- The value of the `W110`-sum. -/
noncomputable def V1val10 : ℝ :=
  ((-(555847670 : ℝ)) / 6561) * (B - Bsum 3)
    +   ((13855631020 : ℝ) / 2187) * (A - Asum 4)
    +   ((-(51160673300 : ℝ)) / 2187) * (B - Bsum 4)
    +   ((-(11880466598 : ℝ)) / 2187) * (A - Asum 5)
    +   ((2913266687870 : ℝ) / 6561) * (B - Bsum 5)
    +   ((-(345613573760 : ℝ)) / 81) * (A - Asum 6)
    +   ((36839215012600 : ℝ) / 6561) * (B - Bsum 6)
    +   ((55929028741768 : ℝ) / 2187) * (A - Asum 7)
    +   ((-(51446784593050 : ℝ)) / 729) * (B - Bsum 7)
    +   ((165843729010960 : ℝ) / 2187) * (A - Asum 8)
    +   ((732385936355150 : ℝ) / 6561) * (B - Bsum 8)
    +   ((-(189853839346600 : ℝ)) / 243) * (A - Asum 9)
    +   ((4761117472711600 : ℝ) / 6561) * (B - Bsum 9)
    +   ((3167729640200125 : ℝ) / 2187) * (A - Asum 10)
    +   ((-(6067012295869525 : ℝ)) / 2187) * (B - Bsum 10)
    +   ((2217743083130575 : ℝ) / 2187) * (A - Asum 11)
    +   ((15673897713273800 : ℝ) / 6561) * (B - Bsum 11)
    +   ((-(166609791610955 : ℝ)) / 27) * (A - Asum 12)
    +   ((21943456798583320 : ℝ) / 6561) * (B - Bsum 12)
    +   ((13875891882570025 : ℝ) / 2187) * (A - Asum 13)
    +   ((-(16767015799493960 : ℝ)) / 2187) * (B - Bsum 13)
    +   ((399002261396200 : ℝ) / 2187) * (A - Asum 14)
    +   ((26561729853626240 : ℝ) / 6561) * (B - Bsum 14)
    +   ((-(112197662303650 : ℝ)) / 27) * (A - Asum 15)
    +   ((8592401835477460 : ℝ) / 6561) * (B - Bsum 15)
    +   ((4789179327502900 : ℝ) / 2187) * (A - Asum 16)
    +   ((-(1356480132489020 : ℝ)) / 729) * (B - Bsum 16)
    +   ((100412214042490 : ℝ) / 2187) * (A - Asum 17)
    +   ((2428318098806600 : ℝ) / 6561) * (B - Bsum 17)
    +   ((-(58837865488675 : ℝ)) / 243) * (A - Asum 18)
    +   ((574822484615170 : ℝ) / 6561) * (B - Bsum 18)
    +   ((51467325384475 : ℝ) / 2187) * (A - Asum 19)
    +   ((-(43011837437800 : ℝ)) / 2187) * (B - Bsum 19)
    +   ((8067851006215 : ℝ) / 2187) * (A - Asum 20)
    +   ((-(6189508314220 : ℝ)) / 6561) * (B - Bsum 20)

/-- The value of the `W210`-sum. -/
noncomputable def V2val10 : ℝ :=
  ((21973444702042219 : ℝ) / 327289711320) * (1 / xm 0 11)
    +   ((8135830269 : ℝ) / 6460) * (1 / xm 0 12)
    +   ((-(26118754940857061 : ℝ)) / 1983574008) * (1 / xm 0 13)
    +   ((7398088921500804649 : ℝ) / 327289711320) * (1 / xm 0 14)
    +   ((1537671920841 : ℝ) / 25840) * (1 / xm 0 15)
    +   ((-(2575669444559325121 : ℝ)) / 19835740080) * (1 / xm 0 16)
    +   ((1430406153685657243 : ℝ) / 10909657044) * (1 / xm 0 17)
    +   ((-(812420765433 : ℝ)) / 380) * (1 / xm 0 18)
    +   ((1410580259001316035829 : ℝ) / 218193140880) * (1 / xm 0 19)
    +   ((-(124505015881429435253 : ℝ)) / 32728971132) * (1 / xm 0 20)
    +   ((-(176753237116959 : ℝ)) / 180880) * (1 / xm 0 21)
    +   ((-(209202929829789839209 : ℝ)) / 14546209392) * (1 / xm 0 22)
    +   ((-(622975458121977969703 : ℝ)) / 65457942264) * (1 / xm 0 23)
    +   ((309958058465688303 : ℝ) / 2351440) * (1 / xm 0 24)
    +   ((-(7318210295899567247123 : ℝ)) / 43638628176) * (1 / xm 0 25)
    +   ((324129560055939567962 : ℝ) / 2727414261) * (1 / xm 0 26)
    +   ((-(987988613242027167 : ℝ)) / 2351440) * (1 / xm 0 27)
    +   ((28362180257517361231465 : ℝ) / 43638628176) * (1 / xm 0 28)
    +   ((79207613991153529978 : ℝ) / 8182242783) * (1 / xm 0 29)
    +   ((-(736201502936088129 : ℝ)) / 1989680) * (1 / xm 0 30)
    +   ((-(1233178738516790211703 : ℝ)) / 10909657044) * (1 / xm 0 31)
    +   ((-(140996035960153961227535 : ℝ)) / 130915884528) * (1 / xm 0 32)
    +   ((7332482289755360583 : ℝ) / 2351440) * (1 / xm 0 33)
    +   ((-(3679152107756964156713 : ℝ)) / 1616245488) * (1 / xm 0 34)
    +   ((16518754023027036050747 : ℝ) / 11313718416) * (1 / xm 0 35)
    +   ((-(1670593522315450743 : ℝ)) / 470288) * (1 / xm 0 36)
    +   ((1419782132197788520514 : ℝ) / 505076715) * (1 / xm 0 37)
    +   ((64733484688498613906071 : ℝ) / 53906540688) * (1 / xm 0 38)
    +   ((-(12680087805396747 : ℝ)) / 9044) * (1 / xm 0 39)
    +   ((78881350566468547298083 : ℝ) / 218193140880) * (1 / xm 0 40)
    +   ((-(15152482967753182680069449 : ℝ)) / 4582055958480) * (1 / xm 0 41)
    +   ((24264640736875431 : ℝ) / 5168) * (1 / xm 0 42)
    +   ((-(448445525759920459998037 : ℝ)) / 218193140880) * (1 / xm 0 43)
    +   ((170320665503925346136087 : ℝ) / 138850180560) * (1 / xm 0 44)
    +   ((-(5218603964073081 : ℝ)) / 2584) * (1 / xm 0 45)
    +   ((129870913346747945633033 : ℝ) / 218193140880) * (1 / xm 0 46)
    +   ((80607929676583335472699 : ℝ) / 83310108336) * (1 / xm 0 47)
    +   ((-(402471387577161 : ℝ)) / 646) * (1 / xm 0 48)
    +   ((21693613135982147632031 : ℝ) / 72731046960) * (1 / xm 0 49)
    +   ((-(50135369727948829332707 : ℝ)) / 83310108336) * (1 / xm 0 50)
    +   ((177710940565767 : ℝ) / 380) * (1 / xm 0 51)
    +   ((-(1294886086590343475117 : ℝ)) / 16784087760) * (1 / xm 0 52)
    +   ((-(470192726745868768693 : ℝ)) / 27770036112) * (1 / xm 0 53)
    +   ((-(3880791038313 : ℝ)) / 380) * (1 / xm 0 54)
    +   ((-(14592562116016539641 : ℝ)) / 762913080) * (1 / xm 0 55)
    +   ((943859677606613412607 : ℝ) / 29753610120) * (1 / xm 0 56)
    +   ((-(24407490807 : ℝ)) / 2) * (1 / xm 0 57)
    +   ((490767876101998873 : ℝ) / 1525826160) * (1 / xm 0 58)
    +   ((14367253384165633117 : ℝ) / 29753610120) * (1 / xm 0 59)

/-- The value of the whole sum. -/
noncomputable def Vval10 : ℝ := V1val10 + V2val10

/-! ## `HasSum` of the two pieces of the decomposition -/

lemma hasSum_W110 : HasSum W110 V1val10 := by
  have h11 : HasSum (fun m : ℕ => ((-(555847670 : ℝ)) / 6561) * (1 / (xm m 11)^2))
      (((-(555847670 : ℝ)) / 6561) * (B - Bsum 3)) := by
    simpa using (CdtTwoCore.hasSum_sq2 3).mul_left ((-(555847670 : ℝ)) / 6561)
  have h13 : HasSum (fun m : ℕ => ((13855631020 : ℝ) / 2187) * (1 / (xm m 13)^2))
      (((13855631020 : ℝ) / 2187) * (A - Asum 4)) := by
    simpa using (CdtTwoCore.hasSum_sq1 4).mul_left ((13855631020 : ℝ) / 2187)
  have h14 : HasSum (fun m : ℕ => ((-(51160673300 : ℝ)) / 2187) * (1 / (xm m 14)^2))
      (((-(51160673300 : ℝ)) / 2187) * (B - Bsum 4)) := by
    simpa using (CdtTwoCore.hasSum_sq2 4).mul_left ((-(51160673300 : ℝ)) / 2187)
  have h16 : HasSum (fun m : ℕ => ((-(11880466598 : ℝ)) / 2187) * (1 / (xm m 16)^2))
      (((-(11880466598 : ℝ)) / 2187) * (A - Asum 5)) := by
    simpa using (CdtTwoCore.hasSum_sq1 5).mul_left ((-(11880466598 : ℝ)) / 2187)
  have h17 : HasSum (fun m : ℕ => ((2913266687870 : ℝ) / 6561) * (1 / (xm m 17)^2))
      (((2913266687870 : ℝ) / 6561) * (B - Bsum 5)) := by
    simpa using (CdtTwoCore.hasSum_sq2 5).mul_left ((2913266687870 : ℝ) / 6561)
  have h19 : HasSum (fun m : ℕ => ((-(345613573760 : ℝ)) / 81) * (1 / (xm m 19)^2))
      (((-(345613573760 : ℝ)) / 81) * (A - Asum 6)) := by
    simpa using (CdtTwoCore.hasSum_sq1 6).mul_left ((-(345613573760 : ℝ)) / 81)
  have h20 : HasSum (fun m : ℕ => ((36839215012600 : ℝ) / 6561) * (1 / (xm m 20)^2))
      (((36839215012600 : ℝ) / 6561) * (B - Bsum 6)) := by
    simpa using (CdtTwoCore.hasSum_sq2 6).mul_left ((36839215012600 : ℝ) / 6561)
  have h22 : HasSum (fun m : ℕ => ((55929028741768 : ℝ) / 2187) * (1 / (xm m 22)^2))
      (((55929028741768 : ℝ) / 2187) * (A - Asum 7)) := by
    simpa using (CdtTwoCore.hasSum_sq1 7).mul_left ((55929028741768 : ℝ) / 2187)
  have h23 : HasSum (fun m : ℕ => ((-(51446784593050 : ℝ)) / 729) * (1 / (xm m 23)^2))
      (((-(51446784593050 : ℝ)) / 729) * (B - Bsum 7)) := by
    simpa using (CdtTwoCore.hasSum_sq2 7).mul_left ((-(51446784593050 : ℝ)) / 729)
  have h25 : HasSum (fun m : ℕ => ((165843729010960 : ℝ) / 2187) * (1 / (xm m 25)^2))
      (((165843729010960 : ℝ) / 2187) * (A - Asum 8)) := by
    simpa using (CdtTwoCore.hasSum_sq1 8).mul_left ((165843729010960 : ℝ) / 2187)
  have h26 : HasSum (fun m : ℕ => ((732385936355150 : ℝ) / 6561) * (1 / (xm m 26)^2))
      (((732385936355150 : ℝ) / 6561) * (B - Bsum 8)) := by
    simpa using (CdtTwoCore.hasSum_sq2 8).mul_left ((732385936355150 : ℝ) / 6561)
  have h28 : HasSum (fun m : ℕ => ((-(189853839346600 : ℝ)) / 243) * (1 / (xm m 28)^2))
      (((-(189853839346600 : ℝ)) / 243) * (A - Asum 9)) := by
    simpa using (CdtTwoCore.hasSum_sq1 9).mul_left ((-(189853839346600 : ℝ)) / 243)
  have h29 : HasSum (fun m : ℕ => ((4761117472711600 : ℝ) / 6561) * (1 / (xm m 29)^2))
      (((4761117472711600 : ℝ) / 6561) * (B - Bsum 9)) := by
    simpa using (CdtTwoCore.hasSum_sq2 9).mul_left ((4761117472711600 : ℝ) / 6561)
  have h31 : HasSum (fun m : ℕ => ((3167729640200125 : ℝ) / 2187) * (1 / (xm m 31)^2))
      (((3167729640200125 : ℝ) / 2187) * (A - Asum 10)) := by
    simpa using (CdtTwoCore.hasSum_sq1 10).mul_left ((3167729640200125 : ℝ) / 2187)
  have h32 : HasSum (fun m : ℕ => ((-(6067012295869525 : ℝ)) / 2187) * (1 / (xm m 32)^2))
      (((-(6067012295869525 : ℝ)) / 2187) * (B - Bsum 10)) := by
    simpa using (CdtTwoCore.hasSum_sq2 10).mul_left ((-(6067012295869525 : ℝ)) / 2187)
  have h34 : HasSum (fun m : ℕ => ((2217743083130575 : ℝ) / 2187) * (1 / (xm m 34)^2))
      (((2217743083130575 : ℝ) / 2187) * (A - Asum 11)) := by
    simpa using (CdtTwoCore.hasSum_sq1 11).mul_left ((2217743083130575 : ℝ) / 2187)
  have h35 : HasSum (fun m : ℕ => ((15673897713273800 : ℝ) / 6561) * (1 / (xm m 35)^2))
      (((15673897713273800 : ℝ) / 6561) * (B - Bsum 11)) := by
    simpa using (CdtTwoCore.hasSum_sq2 11).mul_left ((15673897713273800 : ℝ) / 6561)
  have h37 : HasSum (fun m : ℕ => ((-(166609791610955 : ℝ)) / 27) * (1 / (xm m 37)^2))
      (((-(166609791610955 : ℝ)) / 27) * (A - Asum 12)) := by
    simpa using (CdtTwoCore.hasSum_sq1 12).mul_left ((-(166609791610955 : ℝ)) / 27)
  have h38 : HasSum (fun m : ℕ => ((21943456798583320 : ℝ) / 6561) * (1 / (xm m 38)^2))
      (((21943456798583320 : ℝ) / 6561) * (B - Bsum 12)) := by
    simpa using (CdtTwoCore.hasSum_sq2 12).mul_left ((21943456798583320 : ℝ) / 6561)
  have h40 : HasSum (fun m : ℕ => ((13875891882570025 : ℝ) / 2187) * (1 / (xm m 40)^2))
      (((13875891882570025 : ℝ) / 2187) * (A - Asum 13)) := by
    simpa using (CdtTwoCore.hasSum_sq1 13).mul_left ((13875891882570025 : ℝ) / 2187)
  have h41 : HasSum (fun m : ℕ => ((-(16767015799493960 : ℝ)) / 2187) * (1 / (xm m 41)^2))
      (((-(16767015799493960 : ℝ)) / 2187) * (B - Bsum 13)) := by
    simpa using (CdtTwoCore.hasSum_sq2 13).mul_left ((-(16767015799493960 : ℝ)) / 2187)
  have h43 : HasSum (fun m : ℕ => ((399002261396200 : ℝ) / 2187) * (1 / (xm m 43)^2))
      (((399002261396200 : ℝ) / 2187) * (A - Asum 14)) := by
    simpa using (CdtTwoCore.hasSum_sq1 14).mul_left ((399002261396200 : ℝ) / 2187)
  have h44 : HasSum (fun m : ℕ => ((26561729853626240 : ℝ) / 6561) * (1 / (xm m 44)^2))
      (((26561729853626240 : ℝ) / 6561) * (B - Bsum 14)) := by
    simpa using (CdtTwoCore.hasSum_sq2 14).mul_left ((26561729853626240 : ℝ) / 6561)
  have h46 : HasSum (fun m : ℕ => ((-(112197662303650 : ℝ)) / 27) * (1 / (xm m 46)^2))
      (((-(112197662303650 : ℝ)) / 27) * (A - Asum 15)) := by
    simpa using (CdtTwoCore.hasSum_sq1 15).mul_left ((-(112197662303650 : ℝ)) / 27)
  have h47 : HasSum (fun m : ℕ => ((8592401835477460 : ℝ) / 6561) * (1 / (xm m 47)^2))
      (((8592401835477460 : ℝ) / 6561) * (B - Bsum 15)) := by
    simpa using (CdtTwoCore.hasSum_sq2 15).mul_left ((8592401835477460 : ℝ) / 6561)
  have h49 : HasSum (fun m : ℕ => ((4789179327502900 : ℝ) / 2187) * (1 / (xm m 49)^2))
      (((4789179327502900 : ℝ) / 2187) * (A - Asum 16)) := by
    simpa using (CdtTwoCore.hasSum_sq1 16).mul_left ((4789179327502900 : ℝ) / 2187)
  have h50 : HasSum (fun m : ℕ => ((-(1356480132489020 : ℝ)) / 729) * (1 / (xm m 50)^2))
      (((-(1356480132489020 : ℝ)) / 729) * (B - Bsum 16)) := by
    simpa using (CdtTwoCore.hasSum_sq2 16).mul_left ((-(1356480132489020 : ℝ)) / 729)
  have h52 : HasSum (fun m : ℕ => ((100412214042490 : ℝ) / 2187) * (1 / (xm m 52)^2))
      (((100412214042490 : ℝ) / 2187) * (A - Asum 17)) := by
    simpa using (CdtTwoCore.hasSum_sq1 17).mul_left ((100412214042490 : ℝ) / 2187)
  have h53 : HasSum (fun m : ℕ => ((2428318098806600 : ℝ) / 6561) * (1 / (xm m 53)^2))
      (((2428318098806600 : ℝ) / 6561) * (B - Bsum 17)) := by
    simpa using (CdtTwoCore.hasSum_sq2 17).mul_left ((2428318098806600 : ℝ) / 6561)
  have h55 : HasSum (fun m : ℕ => ((-(58837865488675 : ℝ)) / 243) * (1 / (xm m 55)^2))
      (((-(58837865488675 : ℝ)) / 243) * (A - Asum 18)) := by
    simpa using (CdtTwoCore.hasSum_sq1 18).mul_left ((-(58837865488675 : ℝ)) / 243)
  have h56 : HasSum (fun m : ℕ => ((574822484615170 : ℝ) / 6561) * (1 / (xm m 56)^2))
      (((574822484615170 : ℝ) / 6561) * (B - Bsum 18)) := by
    simpa using (CdtTwoCore.hasSum_sq2 18).mul_left ((574822484615170 : ℝ) / 6561)
  have h58 : HasSum (fun m : ℕ => ((51467325384475 : ℝ) / 2187) * (1 / (xm m 58)^2))
      (((51467325384475 : ℝ) / 2187) * (A - Asum 19)) := by
    simpa using (CdtTwoCore.hasSum_sq1 19).mul_left ((51467325384475 : ℝ) / 2187)
  have h59 : HasSum (fun m : ℕ => ((-(43011837437800 : ℝ)) / 2187) * (1 / (xm m 59)^2))
      (((-(43011837437800 : ℝ)) / 2187) * (B - Bsum 19)) := by
    simpa using (CdtTwoCore.hasSum_sq2 19).mul_left ((-(43011837437800 : ℝ)) / 2187)
  have h61 : HasSum (fun m : ℕ => ((8067851006215 : ℝ) / 2187) * (1 / (xm m 61)^2))
      (((8067851006215 : ℝ) / 2187) * (A - Asum 20)) := by
    simpa using (CdtTwoCore.hasSum_sq1 20).mul_left ((8067851006215 : ℝ) / 2187)
  have h62 : HasSum (fun m : ℕ => ((-(6189508314220 : ℝ)) / 6561) * (1 / (xm m 62)^2))
      (((-(6189508314220 : ℝ)) / 6561) * (B - Bsum 20)) := by
    simpa using (CdtTwoCore.hasSum_sq2 20).mul_left ((-(6189508314220 : ℝ)) / 6561)
  exact ((((((((((((((((((((((((((((((((((h11.add h13).add h14).add h16).add h17).add h19).add h20).add h22).add h23).add h25).add h26).add h28).add h29).add h31).add h32).add h34).add h35).add h37).add h38).add h40).add h41).add h43).add h44).add h46).add h47).add h49).add h50).add h52).add h53).add h55).add h56).add h58).add h59).add h61).add h62)

lemma hasSum_W210 : HasSum W210 V2val10 := by
  have hp11 : HasSum (fun m : ℕ => ((21973444702042219 : ℝ) / 327289711320) * (1 / xm m 11 - 1 / xm m 14))
      (((21973444702042219 : ℝ) / 327289711320) * (1 / xm 0 11)) := by
    simpa using (CdtTwoCore.hasSum_pair 11 (by norm_num)).mul_left ((21973444702042219 : ℝ) / 327289711320)
  have hp12 : HasSum (fun m : ℕ => ((8135830269 : ℝ) / 6460) * (1 / xm m 12 - 1 / xm m 15))
      (((8135830269 : ℝ) / 6460) * (1 / xm 0 12)) := by
    simpa using (CdtTwoCore.hasSum_pair 12 (by norm_num)).mul_left ((8135830269 : ℝ) / 6460)
  have hp13 : HasSum (fun m : ℕ => ((-(26118754940857061 : ℝ)) / 1983574008) * (1 / xm m 13 - 1 / xm m 16))
      (((-(26118754940857061 : ℝ)) / 1983574008) * (1 / xm 0 13)) := by
    simpa using (CdtTwoCore.hasSum_pair 13 (by norm_num)).mul_left ((-(26118754940857061 : ℝ)) / 1983574008)
  have hp14 : HasSum (fun m : ℕ => ((7398088921500804649 : ℝ) / 327289711320) * (1 / xm m 14 - 1 / xm m 17))
      (((7398088921500804649 : ℝ) / 327289711320) * (1 / xm 0 14)) := by
    simpa using (CdtTwoCore.hasSum_pair 14 (by norm_num)).mul_left ((7398088921500804649 : ℝ) / 327289711320)
  have hp15 : HasSum (fun m : ℕ => ((1537671920841 : ℝ) / 25840) * (1 / xm m 15 - 1 / xm m 18))
      (((1537671920841 : ℝ) / 25840) * (1 / xm 0 15)) := by
    simpa using (CdtTwoCore.hasSum_pair 15 (by norm_num)).mul_left ((1537671920841 : ℝ) / 25840)
  have hp16 : HasSum (fun m : ℕ => ((-(2575669444559325121 : ℝ)) / 19835740080) * (1 / xm m 16 - 1 / xm m 19))
      (((-(2575669444559325121 : ℝ)) / 19835740080) * (1 / xm 0 16)) := by
    simpa using (CdtTwoCore.hasSum_pair 16 (by norm_num)).mul_left ((-(2575669444559325121 : ℝ)) / 19835740080)
  have hp17 : HasSum (fun m : ℕ => ((1430406153685657243 : ℝ) / 10909657044) * (1 / xm m 17 - 1 / xm m 20))
      (((1430406153685657243 : ℝ) / 10909657044) * (1 / xm 0 17)) := by
    simpa using (CdtTwoCore.hasSum_pair 17 (by norm_num)).mul_left ((1430406153685657243 : ℝ) / 10909657044)
  have hp18 : HasSum (fun m : ℕ => ((-(812420765433 : ℝ)) / 380) * (1 / xm m 18 - 1 / xm m 21))
      (((-(812420765433 : ℝ)) / 380) * (1 / xm 0 18)) := by
    simpa using (CdtTwoCore.hasSum_pair 18 (by norm_num)).mul_left ((-(812420765433 : ℝ)) / 380)
  have hp19 : HasSum (fun m : ℕ => ((1410580259001316035829 : ℝ) / 218193140880) * (1 / xm m 19 - 1 / xm m 22))
      (((1410580259001316035829 : ℝ) / 218193140880) * (1 / xm 0 19)) := by
    simpa using (CdtTwoCore.hasSum_pair 19 (by norm_num)).mul_left ((1410580259001316035829 : ℝ) / 218193140880)
  have hp20 : HasSum (fun m : ℕ => ((-(124505015881429435253 : ℝ)) / 32728971132) * (1 / xm m 20 - 1 / xm m 23))
      (((-(124505015881429435253 : ℝ)) / 32728971132) * (1 / xm 0 20)) := by
    simpa using (CdtTwoCore.hasSum_pair 20 (by norm_num)).mul_left ((-(124505015881429435253 : ℝ)) / 32728971132)
  have hp21 : HasSum (fun m : ℕ => ((-(176753237116959 : ℝ)) / 180880) * (1 / xm m 21 - 1 / xm m 24))
      (((-(176753237116959 : ℝ)) / 180880) * (1 / xm 0 21)) := by
    simpa using (CdtTwoCore.hasSum_pair 21 (by norm_num)).mul_left ((-(176753237116959 : ℝ)) / 180880)
  have hp22 : HasSum (fun m : ℕ => ((-(209202929829789839209 : ℝ)) / 14546209392) * (1 / xm m 22 - 1 / xm m 25))
      (((-(209202929829789839209 : ℝ)) / 14546209392) * (1 / xm 0 22)) := by
    simpa using (CdtTwoCore.hasSum_pair 22 (by norm_num)).mul_left ((-(209202929829789839209 : ℝ)) / 14546209392)
  have hp23 : HasSum (fun m : ℕ => ((-(622975458121977969703 : ℝ)) / 65457942264) * (1 / xm m 23 - 1 / xm m 26))
      (((-(622975458121977969703 : ℝ)) / 65457942264) * (1 / xm 0 23)) := by
    simpa using (CdtTwoCore.hasSum_pair 23 (by norm_num)).mul_left ((-(622975458121977969703 : ℝ)) / 65457942264)
  have hp24 : HasSum (fun m : ℕ => ((309958058465688303 : ℝ) / 2351440) * (1 / xm m 24 - 1 / xm m 27))
      (((309958058465688303 : ℝ) / 2351440) * (1 / xm 0 24)) := by
    simpa using (CdtTwoCore.hasSum_pair 24 (by norm_num)).mul_left ((309958058465688303 : ℝ) / 2351440)
  have hp25 : HasSum (fun m : ℕ => ((-(7318210295899567247123 : ℝ)) / 43638628176) * (1 / xm m 25 - 1 / xm m 28))
      (((-(7318210295899567247123 : ℝ)) / 43638628176) * (1 / xm 0 25)) := by
    simpa using (CdtTwoCore.hasSum_pair 25 (by norm_num)).mul_left ((-(7318210295899567247123 : ℝ)) / 43638628176)
  have hp26 : HasSum (fun m : ℕ => ((324129560055939567962 : ℝ) / 2727414261) * (1 / xm m 26 - 1 / xm m 29))
      (((324129560055939567962 : ℝ) / 2727414261) * (1 / xm 0 26)) := by
    simpa using (CdtTwoCore.hasSum_pair 26 (by norm_num)).mul_left ((324129560055939567962 : ℝ) / 2727414261)
  have hp27 : HasSum (fun m : ℕ => ((-(987988613242027167 : ℝ)) / 2351440) * (1 / xm m 27 - 1 / xm m 30))
      (((-(987988613242027167 : ℝ)) / 2351440) * (1 / xm 0 27)) := by
    simpa using (CdtTwoCore.hasSum_pair 27 (by norm_num)).mul_left ((-(987988613242027167 : ℝ)) / 2351440)
  have hp28 : HasSum (fun m : ℕ => ((28362180257517361231465 : ℝ) / 43638628176) * (1 / xm m 28 - 1 / xm m 31))
      (((28362180257517361231465 : ℝ) / 43638628176) * (1 / xm 0 28)) := by
    simpa using (CdtTwoCore.hasSum_pair 28 (by norm_num)).mul_left ((28362180257517361231465 : ℝ) / 43638628176)
  have hp29 : HasSum (fun m : ℕ => ((79207613991153529978 : ℝ) / 8182242783) * (1 / xm m 29 - 1 / xm m 32))
      (((79207613991153529978 : ℝ) / 8182242783) * (1 / xm 0 29)) := by
    simpa using (CdtTwoCore.hasSum_pair 29 (by norm_num)).mul_left ((79207613991153529978 : ℝ) / 8182242783)
  have hp30 : HasSum (fun m : ℕ => ((-(736201502936088129 : ℝ)) / 1989680) * (1 / xm m 30 - 1 / xm m 33))
      (((-(736201502936088129 : ℝ)) / 1989680) * (1 / xm 0 30)) := by
    simpa using (CdtTwoCore.hasSum_pair 30 (by norm_num)).mul_left ((-(736201502936088129 : ℝ)) / 1989680)
  have hp31 : HasSum (fun m : ℕ => ((-(1233178738516790211703 : ℝ)) / 10909657044) * (1 / xm m 31 - 1 / xm m 34))
      (((-(1233178738516790211703 : ℝ)) / 10909657044) * (1 / xm 0 31)) := by
    simpa using (CdtTwoCore.hasSum_pair 31 (by norm_num)).mul_left ((-(1233178738516790211703 : ℝ)) / 10909657044)
  have hp32 : HasSum (fun m : ℕ => ((-(140996035960153961227535 : ℝ)) / 130915884528) * (1 / xm m 32 - 1 / xm m 35))
      (((-(140996035960153961227535 : ℝ)) / 130915884528) * (1 / xm 0 32)) := by
    simpa using (CdtTwoCore.hasSum_pair 32 (by norm_num)).mul_left ((-(140996035960153961227535 : ℝ)) / 130915884528)
  have hp33 : HasSum (fun m : ℕ => ((7332482289755360583 : ℝ) / 2351440) * (1 / xm m 33 - 1 / xm m 36))
      (((7332482289755360583 : ℝ) / 2351440) * (1 / xm 0 33)) := by
    simpa using (CdtTwoCore.hasSum_pair 33 (by norm_num)).mul_left ((7332482289755360583 : ℝ) / 2351440)
  have hp34 : HasSum (fun m : ℕ => ((-(3679152107756964156713 : ℝ)) / 1616245488) * (1 / xm m 34 - 1 / xm m 37))
      (((-(3679152107756964156713 : ℝ)) / 1616245488) * (1 / xm 0 34)) := by
    simpa using (CdtTwoCore.hasSum_pair 34 (by norm_num)).mul_left ((-(3679152107756964156713 : ℝ)) / 1616245488)
  have hp35 : HasSum (fun m : ℕ => ((16518754023027036050747 : ℝ) / 11313718416) * (1 / xm m 35 - 1 / xm m 38))
      (((16518754023027036050747 : ℝ) / 11313718416) * (1 / xm 0 35)) := by
    simpa using (CdtTwoCore.hasSum_pair 35 (by norm_num)).mul_left ((16518754023027036050747 : ℝ) / 11313718416)
  have hp36 : HasSum (fun m : ℕ => ((-(1670593522315450743 : ℝ)) / 470288) * (1 / xm m 36 - 1 / xm m 39))
      (((-(1670593522315450743 : ℝ)) / 470288) * (1 / xm 0 36)) := by
    simpa using (CdtTwoCore.hasSum_pair 36 (by norm_num)).mul_left ((-(1670593522315450743 : ℝ)) / 470288)
  have hp37 : HasSum (fun m : ℕ => ((1419782132197788520514 : ℝ) / 505076715) * (1 / xm m 37 - 1 / xm m 40))
      (((1419782132197788520514 : ℝ) / 505076715) * (1 / xm 0 37)) := by
    simpa using (CdtTwoCore.hasSum_pair 37 (by norm_num)).mul_left ((1419782132197788520514 : ℝ) / 505076715)
  have hp38 : HasSum (fun m : ℕ => ((64733484688498613906071 : ℝ) / 53906540688) * (1 / xm m 38 - 1 / xm m 41))
      (((64733484688498613906071 : ℝ) / 53906540688) * (1 / xm 0 38)) := by
    simpa using (CdtTwoCore.hasSum_pair 38 (by norm_num)).mul_left ((64733484688498613906071 : ℝ) / 53906540688)
  have hp39 : HasSum (fun m : ℕ => ((-(12680087805396747 : ℝ)) / 9044) * (1 / xm m 39 - 1 / xm m 42))
      (((-(12680087805396747 : ℝ)) / 9044) * (1 / xm 0 39)) := by
    simpa using (CdtTwoCore.hasSum_pair 39 (by norm_num)).mul_left ((-(12680087805396747 : ℝ)) / 9044)
  have hp40 : HasSum (fun m : ℕ => ((78881350566468547298083 : ℝ) / 218193140880) * (1 / xm m 40 - 1 / xm m 43))
      (((78881350566468547298083 : ℝ) / 218193140880) * (1 / xm 0 40)) := by
    simpa using (CdtTwoCore.hasSum_pair 40 (by norm_num)).mul_left ((78881350566468547298083 : ℝ) / 218193140880)
  have hp41 : HasSum (fun m : ℕ => ((-(15152482967753182680069449 : ℝ)) / 4582055958480) * (1 / xm m 41 - 1 / xm m 44))
      (((-(15152482967753182680069449 : ℝ)) / 4582055958480) * (1 / xm 0 41)) := by
    simpa using (CdtTwoCore.hasSum_pair 41 (by norm_num)).mul_left ((-(15152482967753182680069449 : ℝ)) / 4582055958480)
  have hp42 : HasSum (fun m : ℕ => ((24264640736875431 : ℝ) / 5168) * (1 / xm m 42 - 1 / xm m 45))
      (((24264640736875431 : ℝ) / 5168) * (1 / xm 0 42)) := by
    simpa using (CdtTwoCore.hasSum_pair 42 (by norm_num)).mul_left ((24264640736875431 : ℝ) / 5168)
  have hp43 : HasSum (fun m : ℕ => ((-(448445525759920459998037 : ℝ)) / 218193140880) * (1 / xm m 43 - 1 / xm m 46))
      (((-(448445525759920459998037 : ℝ)) / 218193140880) * (1 / xm 0 43)) := by
    simpa using (CdtTwoCore.hasSum_pair 43 (by norm_num)).mul_left ((-(448445525759920459998037 : ℝ)) / 218193140880)
  have hp44 : HasSum (fun m : ℕ => ((170320665503925346136087 : ℝ) / 138850180560) * (1 / xm m 44 - 1 / xm m 47))
      (((170320665503925346136087 : ℝ) / 138850180560) * (1 / xm 0 44)) := by
    simpa using (CdtTwoCore.hasSum_pair 44 (by norm_num)).mul_left ((170320665503925346136087 : ℝ) / 138850180560)
  have hp45 : HasSum (fun m : ℕ => ((-(5218603964073081 : ℝ)) / 2584) * (1 / xm m 45 - 1 / xm m 48))
      (((-(5218603964073081 : ℝ)) / 2584) * (1 / xm 0 45)) := by
    simpa using (CdtTwoCore.hasSum_pair 45 (by norm_num)).mul_left ((-(5218603964073081 : ℝ)) / 2584)
  have hp46 : HasSum (fun m : ℕ => ((129870913346747945633033 : ℝ) / 218193140880) * (1 / xm m 46 - 1 / xm m 49))
      (((129870913346747945633033 : ℝ) / 218193140880) * (1 / xm 0 46)) := by
    simpa using (CdtTwoCore.hasSum_pair 46 (by norm_num)).mul_left ((129870913346747945633033 : ℝ) / 218193140880)
  have hp47 : HasSum (fun m : ℕ => ((80607929676583335472699 : ℝ) / 83310108336) * (1 / xm m 47 - 1 / xm m 50))
      (((80607929676583335472699 : ℝ) / 83310108336) * (1 / xm 0 47)) := by
    simpa using (CdtTwoCore.hasSum_pair 47 (by norm_num)).mul_left ((80607929676583335472699 : ℝ) / 83310108336)
  have hp48 : HasSum (fun m : ℕ => ((-(402471387577161 : ℝ)) / 646) * (1 / xm m 48 - 1 / xm m 51))
      (((-(402471387577161 : ℝ)) / 646) * (1 / xm 0 48)) := by
    simpa using (CdtTwoCore.hasSum_pair 48 (by norm_num)).mul_left ((-(402471387577161 : ℝ)) / 646)
  have hp49 : HasSum (fun m : ℕ => ((21693613135982147632031 : ℝ) / 72731046960) * (1 / xm m 49 - 1 / xm m 52))
      (((21693613135982147632031 : ℝ) / 72731046960) * (1 / xm 0 49)) := by
    simpa using (CdtTwoCore.hasSum_pair 49 (by norm_num)).mul_left ((21693613135982147632031 : ℝ) / 72731046960)
  have hp50 : HasSum (fun m : ℕ => ((-(50135369727948829332707 : ℝ)) / 83310108336) * (1 / xm m 50 - 1 / xm m 53))
      (((-(50135369727948829332707 : ℝ)) / 83310108336) * (1 / xm 0 50)) := by
    simpa using (CdtTwoCore.hasSum_pair 50 (by norm_num)).mul_left ((-(50135369727948829332707 : ℝ)) / 83310108336)
  have hp51 : HasSum (fun m : ℕ => ((177710940565767 : ℝ) / 380) * (1 / xm m 51 - 1 / xm m 54))
      (((177710940565767 : ℝ) / 380) * (1 / xm 0 51)) := by
    simpa using (CdtTwoCore.hasSum_pair 51 (by norm_num)).mul_left ((177710940565767 : ℝ) / 380)
  have hp52 : HasSum (fun m : ℕ => ((-(1294886086590343475117 : ℝ)) / 16784087760) * (1 / xm m 52 - 1 / xm m 55))
      (((-(1294886086590343475117 : ℝ)) / 16784087760) * (1 / xm 0 52)) := by
    simpa using (CdtTwoCore.hasSum_pair 52 (by norm_num)).mul_left ((-(1294886086590343475117 : ℝ)) / 16784087760)
  have hp53 : HasSum (fun m : ℕ => ((-(470192726745868768693 : ℝ)) / 27770036112) * (1 / xm m 53 - 1 / xm m 56))
      (((-(470192726745868768693 : ℝ)) / 27770036112) * (1 / xm 0 53)) := by
    simpa using (CdtTwoCore.hasSum_pair 53 (by norm_num)).mul_left ((-(470192726745868768693 : ℝ)) / 27770036112)
  have hp54 : HasSum (fun m : ℕ => ((-(3880791038313 : ℝ)) / 380) * (1 / xm m 54 - 1 / xm m 57))
      (((-(3880791038313 : ℝ)) / 380) * (1 / xm 0 54)) := by
    simpa using (CdtTwoCore.hasSum_pair 54 (by norm_num)).mul_left ((-(3880791038313 : ℝ)) / 380)
  have hp55 : HasSum (fun m : ℕ => ((-(14592562116016539641 : ℝ)) / 762913080) * (1 / xm m 55 - 1 / xm m 58))
      (((-(14592562116016539641 : ℝ)) / 762913080) * (1 / xm 0 55)) := by
    simpa using (CdtTwoCore.hasSum_pair 55 (by norm_num)).mul_left ((-(14592562116016539641 : ℝ)) / 762913080)
  have hp56 : HasSum (fun m : ℕ => ((943859677606613412607 : ℝ) / 29753610120) * (1 / xm m 56 - 1 / xm m 59))
      (((943859677606613412607 : ℝ) / 29753610120) * (1 / xm 0 56)) := by
    simpa using (CdtTwoCore.hasSum_pair 56 (by norm_num)).mul_left ((943859677606613412607 : ℝ) / 29753610120)
  have hp57 : HasSum (fun m : ℕ => ((-(24407490807 : ℝ)) / 2) * (1 / xm m 57 - 1 / xm m 60))
      (((-(24407490807 : ℝ)) / 2) * (1 / xm 0 57)) := by
    simpa using (CdtTwoCore.hasSum_pair 57 (by norm_num)).mul_left ((-(24407490807 : ℝ)) / 2)
  have hp58 : HasSum (fun m : ℕ => ((490767876101998873 : ℝ) / 1525826160) * (1 / xm m 58 - 1 / xm m 61))
      (((490767876101998873 : ℝ) / 1525826160) * (1 / xm 0 58)) := by
    simpa using (CdtTwoCore.hasSum_pair 58 (by norm_num)).mul_left ((490767876101998873 : ℝ) / 1525826160)
  have hp59 : HasSum (fun m : ℕ => ((14367253384165633117 : ℝ) / 29753610120) * (1 / xm m 59 - 1 / xm m 62))
      (((14367253384165633117 : ℝ) / 29753610120) * (1 / xm 0 59)) := by
    simpa using (CdtTwoCore.hasSum_pair 59 (by norm_num)).mul_left ((14367253384165633117 : ℝ) / 29753610120)
  exact ((((((((((((((((((((((((((((((((((((((((((((((((hp11.add hp12).add hp13).add hp14).add hp15).add hp16).add hp17).add hp18).add hp19).add hp20).add hp21).add hp22).add hp23).add hp24).add hp25).add hp26).add hp27).add hp28).add hp29).add hp30).add hp31).add hp32).add hp33).add hp34).add hp35).add hp36).add hp37).add hp38).add hp39).add hp40).add hp41).add hp42).add hp43).add hp44).add hp45).add hp46).add hp47).add hp48).add hp49).add hp50).add hp51).add hp52).add hp53).add hp54).add hp55).add hp56).add hp57).add hp58).add hp59)

/-- `HasSum` for the whole summand. -/
lemma hasSum_Vm10 : HasSum Vm10 Vval10 := by
  have hsum : HasSum (fun m : ℕ => W110 m + W210 m) Vval10 := by
    simpa [Vval10] using hasSum_W110.add hasSum_W210
  apply HasSum.congr_fun hsum
  intro m
  exact vm10_decomp m

set_option maxHeartbeats 0 in
/-- The infinite sum of `Vm10` in closed form. -/
lemma tsum_Vm10 : (∑' m : ℕ, Vm10 m) = 140668065 * A - 140668065 * B - 4308248502993 / 39200 := by
  have hval : Vval10 = 140668065 * A - 140668065 * B - 4308248502993 / 39200 := by
    unfold Vval10 V1val10 V2val10
    norm_num [xm]
    ring
  rw [hasSum_Vm10.tsum_eq]
  exact hval

end CdtTenCore
open CdtTenCore

/-! ## Final assembly -/

/-- Creative-telescoping evaluation of the degree-10 `(Cintegral)` inner sum. -/
theorem sum_cintegralTen_core :
    (∑' m : ℕ,
        (3486784401 : ℝ) * (Nat.choose (m + 20) 20 : ℝ) *
          (∑ i ∈ Finset.range 22,
            ((-1 : ℝ) ^ i * (Nat.choose 21 i : ℝ)) *
              (214277011200 / ((((3 * m + 11 + i : ℕ) : ℝ) * ((3 * m + 14 + i : ℕ) : ℝ) * ((3 * m + 17 + i : ℕ) : ℝ) * ((3 * m + 20 + i : ℕ) : ℝ) * ((3 * m + 23 + i : ℕ) : ℝ) * ((3 * m + 26 + i : ℕ) : ℝ) * ((3 * m + 29 + i : ℕ) : ℝ) * ((3 * m + 32 + i : ℕ) : ℝ) * ((3 * m + 35 + i : ℕ) : ℝ) * ((3 * m + 38 + i : ℕ) : ℝ) * ((3 * m + 41 + i : ℕ) : ℝ)))) ^ 2)) =
      140668065 * (∑' k : ℕ,
          ((1 : ℝ) / (((3 * k + 1 : ℕ) : ℝ) ^ 2) - (1 : ℝ) / (((3 * k + 2 : ℕ) : ℝ) ^ 2))) - 4308248502993 / 39200 := by
  have hMain := tsum_Vm10
  have hL : (∑' m : ℕ, Vm10 m) =
      (∑' m : ℕ,
        (3486784401 : ℝ) * (Nat.choose (m + 20) 20 : ℝ) *
          (∑ i ∈ Finset.range 22,
            ((-1 : ℝ) ^ i * (Nat.choose 21 i : ℝ)) *
              (214277011200 / ((((3 * m + 11 + i : ℕ) : ℝ) * ((3 * m + 14 + i : ℕ) : ℝ) * ((3 * m + 17 + i : ℕ) : ℝ) * ((3 * m + 20 + i : ℕ) : ℝ) * ((3 * m + 23 + i : ℕ) : ℝ) * ((3 * m + 26 + i : ℕ) : ℝ) * ((3 * m + 29 + i : ℕ) : ℝ) * ((3 * m + 32 + i : ℕ) : ℝ) * ((3 * m + 35 + i : ℕ) : ℝ) * ((3 * m + 38 + i : ℕ) : ℝ) * ((3 * m + 41 + i : ℕ) : ℝ)))) ^ 2)) := by
    apply tsum_congr
    intro m
    exact (vm10_eq_statement m).symm
  rw [← hL]
  rw [hMain]
  have hR : (∑' k : ℕ,
      ((1 : ℝ) / (((3 * k + 1 : ℕ) : ℝ) ^ 2) - (1 : ℝ) / (((3 * k + 2 : ℕ) : ℝ) ^ 2))) = A - B := by
    simpa [Rk, f1, f2, xm] using tsum_Rk
  rw [hR]
  ring

end Commons.Analysis.Summation
