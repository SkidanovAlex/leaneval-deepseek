import Mathlib
import Submission.Commons.Analysis.Summation.sum_cintegralFour_core

noncomputable section
open scoped BigOperators Nat
open Filter Topology

namespace Commons.Analysis.Summation
namespace CdtElevenCore

/-! ## Binomial `(m+22 choose 22)` as a degree-22 polynomial -/

set_option maxHeartbeats 0 in
lemma asc22 (n : ℕ) : n.ascFactorial 22 =
    (n + 0) * (n + 1) * (n + 2) * (n + 3) * (n + 4) * (n + 5) * (n + 6) * (n + 7) * (n + 8) * (n + 9) * (n + 10) * (n + 11) * (n + 12) * (n + 13) * (n + 14) * (n + 15) * (n + 16) * (n + 17) * (n + 18) * (n + 19) * (n + 20) * (n + 21) := by
  simp [Nat.ascFactorial_succ, Nat.ascFactorial_zero]
  ring

set_option maxHeartbeats 0 in
lemma factorial_add_twenty_two (m : ℕ) : (m + 22)! =
    m ! * ((m + 1) * (m + 2) * (m + 3) * (m + 4) * (m + 5) * (m + 6) * (m + 7) * (m + 8) * (m + 9) * (m + 10) * (m + 11) * (m + 12) * (m + 13) * (m + 14) * (m + 15) * (m + 16) * (m + 17) * (m + 18) * (m + 19) * (m + 20) * (m + 21) * (m + 22)) := by
  rw [← Nat.factorial_mul_ascFactorial m 22]
  have h := asc22 (m + 1)
  rw [h]

set_option maxHeartbeats 0 in
lemma choose2222 (m : ℕ) :
    (Nat.choose (m + 22) 22 : ℝ) =
      (1 / 1124000727777607680000 : ℝ) *
        (((m : ℝ) + 1) * ((m : ℝ) + 2) * ((m : ℝ) + 3) * ((m : ℝ) + 4) * ((m : ℝ) + 5) * ((m : ℝ) + 6) * ((m : ℝ) + 7) * ((m : ℝ) + 8) * ((m : ℝ) + 9) * ((m : ℝ) + 10) * ((m : ℝ) + 11) * ((m : ℝ) + 12) * ((m : ℝ) + 13) * ((m : ℝ) + 14) * ((m : ℝ) + 15) * ((m : ℝ) + 16) * ((m : ℝ) + 17) * ((m : ℝ) + 18) * ((m : ℝ) + 19) * ((m : ℝ) + 20) * ((m : ℝ) + 21) * ((m : ℝ) + 22)) := by
  have hcast := Nat.cast_choose ℝ (a := 22) (b := m + 22) (by omega : 22 ≤ m + 22)
  rw [hcast]
  have h22 : ((22 : ℕ)! : ℝ) = 1124000727777607680000 := by norm_num
  have hsub : ((m + 22 - 22) : ℕ) = m := by omega
  rw [h22, hsub]
  have hfacR : ((m + 22)! : ℝ) = (m ! : ℝ) *
      (((m : ℝ) + 1) * ((m : ℝ) + 2) * ((m : ℝ) + 3) * ((m : ℝ) + 4) * ((m : ℝ) + 5) * ((m : ℝ) + 6) * ((m : ℝ) + 7) * ((m : ℝ) + 8) * ((m : ℝ) + 9) * ((m : ℝ) + 10) * ((m : ℝ) + 11) * ((m : ℝ) + 12) * ((m : ℝ) + 13) * ((m : ℝ) + 14) * ((m : ℝ) + 15) * ((m : ℝ) + 16) * ((m : ℝ) + 17) * ((m : ℝ) + 18) * ((m : ℝ) + 19) * ((m : ℝ) + 20) * ((m : ℝ) + 21) * ((m : ℝ) + 22)) := by
    norm_num [factorial_add_twenty_two, Nat.cast_mul]
  rw [hfacR]
  have hm : (m ! : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_ne_zero m)
  field_simp [hm]

@[simp] lemma c23_0 : (Nat.choose 23 0 : ℝ) = 1 := by
  rw [Nat.cast_choose ℝ (by decide : 0 ≤ 23)]; norm_num
@[simp] lemma c23_1 : (Nat.choose 23 1 : ℝ) = 23 := by
  rw [Nat.cast_choose ℝ (by decide : 1 ≤ 23)]; norm_num
@[simp] lemma c23_2 : (Nat.choose 23 2 : ℝ) = 253 := by
  rw [Nat.cast_choose ℝ (by decide : 2 ≤ 23)]; norm_num
@[simp] lemma c23_3 : (Nat.choose 23 3 : ℝ) = 1771 := by
  rw [Nat.cast_choose ℝ (by decide : 3 ≤ 23)]; norm_num
@[simp] lemma c23_4 : (Nat.choose 23 4 : ℝ) = 8855 := by
  rw [Nat.cast_choose ℝ (by decide : 4 ≤ 23)]; norm_num
@[simp] lemma c23_5 : (Nat.choose 23 5 : ℝ) = 33649 := by
  rw [Nat.cast_choose ℝ (by decide : 5 ≤ 23)]; norm_num
@[simp] lemma c23_6 : (Nat.choose 23 6 : ℝ) = 100947 := by
  rw [Nat.cast_choose ℝ (by decide : 6 ≤ 23)]; norm_num
@[simp] lemma c23_7 : (Nat.choose 23 7 : ℝ) = 245157 := by
  rw [Nat.cast_choose ℝ (by decide : 7 ≤ 23)]; norm_num
@[simp] lemma c23_8 : (Nat.choose 23 8 : ℝ) = 490314 := by
  rw [Nat.cast_choose ℝ (by decide : 8 ≤ 23)]; norm_num
@[simp] lemma c23_9 : (Nat.choose 23 9 : ℝ) = 817190 := by
  rw [Nat.cast_choose ℝ (by decide : 9 ≤ 23)]; norm_num
@[simp] lemma c23_10 : (Nat.choose 23 10 : ℝ) = 1144066 := by
  rw [Nat.cast_choose ℝ (by decide : 10 ≤ 23)]; norm_num
@[simp] lemma c23_11 : (Nat.choose 23 11 : ℝ) = 1352078 := by
  rw [Nat.cast_choose ℝ (by decide : 11 ≤ 23)]; norm_num
@[simp] lemma c23_12 : (Nat.choose 23 12 : ℝ) = 1352078 := by
  rw [Nat.cast_choose ℝ (by decide : 12 ≤ 23)]; norm_num
@[simp] lemma c23_13 : (Nat.choose 23 13 : ℝ) = 1144066 := by
  rw [Nat.cast_choose ℝ (by decide : 13 ≤ 23)]; norm_num
@[simp] lemma c23_14 : (Nat.choose 23 14 : ℝ) = 817190 := by
  rw [Nat.cast_choose ℝ (by decide : 14 ≤ 23)]; norm_num
@[simp] lemma c23_15 : (Nat.choose 23 15 : ℝ) = 490314 := by
  rw [Nat.cast_choose ℝ (by decide : 15 ≤ 23)]; norm_num
@[simp] lemma c23_16 : (Nat.choose 23 16 : ℝ) = 245157 := by
  rw [Nat.cast_choose ℝ (by decide : 16 ≤ 23)]; norm_num
@[simp] lemma c23_17 : (Nat.choose 23 17 : ℝ) = 100947 := by
  rw [Nat.cast_choose ℝ (by decide : 17 ≤ 23)]; norm_num
@[simp] lemma c23_18 : (Nat.choose 23 18 : ℝ) = 33649 := by
  rw [Nat.cast_choose ℝ (by decide : 18 ≤ 23)]; norm_num
@[simp] lemma c23_19 : (Nat.choose 23 19 : ℝ) = 8855 := by
  rw [Nat.cast_choose ℝ (by decide : 19 ≤ 23)]; norm_num
@[simp] lemma c23_20 : (Nat.choose 23 20 : ℝ) = 1771 := by
  rw [Nat.cast_choose ℝ (by decide : 20 ≤ 23)]; norm_num
@[simp] lemma c23_21 : (Nat.choose 23 21 : ℝ) = 253 := by
  rw [Nat.cast_choose ℝ (by decide : 21 ≤ 23)]; norm_num
@[simp] lemma c23_22 : (Nat.choose 23 22 : ℝ) = 23 := by
  rw [Nat.cast_choose ℝ (by decide : 22 ≤ 23)]; norm_num
@[simp] lemma c23_23 : (Nat.choose 23 23 : ℝ) = 1 := by
  rw [Nat.cast_choose ℝ (by decide : 23 ≤ 23)]; norm_num

/-! ## The `m`-summand and its pointwise closed-form decomposition -/

/-- The `m`-summand of the eleven-core sum. -/
def Vm11 (m : ℕ) : ℝ :=
  (31381059609 : ℝ) * (Nat.choose (m + 22) 22 : ℝ) *
    (∑ i ∈ Finset.range 24,
      ((-1 : ℝ) ^ i * (Nat.choose 23 i : ℝ)) *
        (7071141369600 / (xm m (12 + i) * xm m (15 + i) * xm m (18 + i) * xm m (21 + i) * xm m (24 + i) * xm m (27 + i) * xm m (30 + i) * xm m (33 + i) * xm m (36 + i) * xm m (39 + i) * xm m (42 + i) * xm m (45 + i))) ^ 2)

/-- Squared-term part of the closed-form decomposition. -/
def W111 (m : ℕ) : ℝ :=
  ((-(78339583550 : ℝ)) / 19683) * (1 / (xm m 13)^2)
    +   ((522337996180 : ℝ) / 19683) * (1 / (xm m 14)^2)
    +   ((-(1690952520400 : ℝ)) / 6561) * (1 / (xm m 16)^2)
    +   ((562517842040 : ℝ) / 6561) * (1 / (xm m 17)^2)
    +   ((67435186513552 : ℝ) / 6561) * (1 / (xm m 19)^2)
    +   ((-(181010205599300 : ℝ)) / 6561) * (1 / (xm m 20)^2)
    +   ((85009579857488 : ℝ) / 6561) * (1 / (xm m 22)^2)
    +   ((1031983607849600 : ℝ) / 6561) * (1 / (xm m 23)^2)
    +   ((-(6587900650679920 : ℝ)) / 6561) * (1 / (xm m 25)^2)
    +   ((6456174388304300 : ℝ) / 6561) * (1 / (xm m 26)^2)
    +   ((26276215779985600 : ℝ) / 6561) * (1 / (xm m 28)^2)
    +   ((-(55845231074686625 : ℝ)) / 6561) * (1 / (xm m 29)^2)
    +   ((23498580125020000 : ℝ) / 6561) * (1 / (xm m 31)^2)
    +   ((90756265764221200 : ℝ) / 6561) * (1 / (xm m 32)^2)
    +   ((-(313546476451046800 : ℝ)) / 6561) * (1 / (xm m 34)^2)
    +   ((199260323885090000 : ℝ) / 6561) * (1 / (xm m 35)^2)
    +   ((570358606100384530 : ℝ) / 6561) * (1 / (xm m 37)^2)
    +   ((-(820192712334195200 : ℝ)) / 6561) * (1 / (xm m 38)^2)
    +   ((0 : ℝ) / 1) * (1 / (xm m 40)^2)
    +   ((265918374264228400 : ℝ) / 2187) * (1 / (xm m 41)^2)
    +   ((-(1119536786510038600 : ℝ)) / 6561) * (1 / (xm m 43)^2)
    +   ((343613891405933720 : ℝ) / 6561) * (1 / (xm m 44)^2)
    +   ((1222536551229884500 : ℝ) / 6561) * (1 / (xm m 46)^2)
    +   ((-(1170533969172751040 : ℝ)) / 6561) * (1 / (xm m 47)^2)
    +   ((-(186647868471806500 : ℝ)) / 6561) * (1 / (xm m 49)^2)
    +   ((677443588019884400 : ℝ) / 6561) * (1 / (xm m 50)^2)
    +   ((-(443267434634572240 : ℝ)) / 6561) * (1 / (xm m 52)^2)
    +   ((68714438045031350 : ℝ) / 6561) * (1 / (xm m 53)^2)
    +   ((251699010219256600 : ℝ) / 6561) * (1 / (xm m 55)^2)
    +   ((-(181350672583814600 : ℝ)) / 6561) * (1 / (xm m 56)^2)
    +   ((-(8119744150618100 : ℝ)) / 6561) * (1 / (xm m 58)^2)
    +   ((38576163021836440 : ℝ) / 6561) * (1 / (xm m 59)^2)
    +   ((-(18877948104440425 : ℝ)) / 6561) * (1 / (xm m 61)^2)
    +   ((5911864655553560 : ℝ) / 6561) * (1 / (xm m 62)^2)
    +   ((1848031830484840 : ℝ) / 6561) * (1 / (xm m 64)^2)
    +   ((-(1370533983863000 : ℝ)) / 6561) * (1 / (xm m 65)^2)
    +   ((672011574721760 : ℝ) / 19683) * (1 / (xm m 67)^2)
    +   ((-(161972198092900 : ℝ)) / 19683) * (1 / (xm m 68)^2)

/-- Telescoping-pair part of the closed-form decomposition. -/
def W211 (m : ℕ) : ℝ :=
  ((-(10460353203 : ℝ)) / 29260) * (1 / xm m 12 - 1 / xm m 15)
    +   ((22979834417835971629 : ℝ) / 2749233575088) * (1 / xm m 13 - 1 / xm m 16)
    +   ((-(589752713661955937 : ℝ)) / 24031762020) * (1 / xm m 14 - 1 / xm m 17)
    +   ((-(3845923194303 : ℝ)) / 29260) * (1 / xm m 15 - 1 / xm m 18)
    +   ((106770018516046364165 : ℝ) / 161719622064) * (1 / xm m 16 - 1 / xm m 19)
    +   ((-(46257936490474335187 : ℝ)) / 62482581252) * (1 / xm m 17 - 1 / xm m 20)
    +   ((1216814533476579 : ℝ) / 497420) * (1 / xm m 18 - 1 / xm m 21)
    +   ((-(181985894706236778816751 : ℝ)) / 13746167875440) * (1 / xm m 19 - 1 / xm m 22)
    +   ((139031538388232398886 : ℝ) / 15620645313) * (1 / xm m 20 - 1 / xm m 23)
    +   ((110644912509177051 : ℝ) / 1989680) * (1 / xm m 21 - 1 / xm m 24)
    +   ((-(236883056754292922329403 : ℝ)) / 2749233575088) * (1 / xm m 22 - 1 / xm m 25)
    +   ((15233037352297344431578 : ℝ) / 171827098443) * (1 / xm m 23 - 1 / xm m 26)
    +   ((-(1188892785894283521 : ℝ)) / 1989680) * (1 / xm m 24 - 1 / xm m 27)
    +   ((3453701270768741997759565 : ℝ) / 2749233575088) * (1 / xm m 25 - 1 / xm m 28)
    +   ((-(311116735461465230093639 : ℝ)) / 687308393772) * (1 / xm m 26 - 1 / xm m 29)
    +   ((-(41763995737944597 : ℝ)) / 1989680) * (1 / xm m 27 - 1 / xm m 30)
    +   ((-(5053397914818780388195667 : ℝ)) / 2749233575088) * (1 / xm m 28 - 1 / xm m 31)
    +   ((-(5245958982321092598604553 : ℝ)) / 2749233575088) * (1 / xm m 29 - 1 / xm m 32)
    +   ((317532296798468484939 : ℝ) / 25865840) * (1 / xm m 30 - 1 / xm m 33)
    +   ((-(32285423602968746893537187 : ℝ)) / 2749233575088) * (1 / xm m 31 - 1 / xm m 34)
    +   ((26685916736540273874070183 : ℝ) / 2749233575088) * (1 / xm m 32 - 1 / xm m 35)
    +   ((-(62723034097796637297 : ℝ)) / 1989680) * (1 / xm m 33 - 1 / xm m 36)
    +   ((101648130000370270917630997 : ℝ) / 2749233575088) * (1 / xm m 34 - 1 / xm m 37)
    +   ((1987291845999927464565823 : ℝ) / 2749233575088) * (1 / xm m 35 - 1 / xm m 38)
    +   ((-(21464023333432562973 : ℝ)) / 3695120) * (1 / xm m 36 - 1 / xm m 39)
    +   ((-(26042350278493626797429959 : ℝ)) / 1963738267920) * (1 / xm m 37 - 1 / xm m 40)
    +   ((-(134492902121995335078095681 : ℝ)) / 2749233575088) * (1 / xm m 38 - 1 / xm m 41)
    +   ((11695740090101721099 : ℝ) / 104720) * (1 / xm m 39 - 1 / xm m 42)
    +   ((-(923589327565702456071470513 : ℝ)) / 13746167875440) * (1 / xm m 40 - 1 / xm m 43)
    +   ((161894305276494010433398583 : ℝ) / 2749233575088) * (1 / xm m 41 - 1 / xm m 44)
    +   ((-(49789350917107409187 : ℝ)) / 397936) * (1 / xm m 42 - 1 / xm m 45)
    +   ((1087599717796934030952068647 : ℝ) / 13746167875440) * (1 / xm m 43 - 1 / xm m 46)
    +   ((328080302811962663173477111 : ℝ) / 13746167875440) * (1 / xm m 44 - 1 / xm m 47)
    +   ((-(284786888652396882 : ℝ)) / 24871) * (1 / xm m 45 - 1 / xm m 48)
    +   ((6764952488387424150279547 : ℝ) / 13746167875440) * (1 / xm m 46 - 1 / xm m 49)
    +   ((-(212332086265051040067689941 : ℝ)) / 2749233575088) * (1 / xm m 47 - 1 / xm m 50)
    +   ((2312100868240277253 : ℝ) / 24871) * (1 / xm m 48 - 1 / xm m 51)
    +   ((-(506827321783160786341706873 : ℝ)) / 13746167875440) * (1 / xm m 49 - 1 / xm m 52)
    +   ((82494137795471831640577907 : ℝ) / 2749233575088) * (1 / xm m 50 - 1 / xm m 53)
    +   ((-(17273184730898301 : ℝ)) / 418) * (1 / xm m 51 - 1 / xm m 54)
    +   ((10795296005161482509425747 : ℝ) / 1057397528880) * (1 / xm m 52 - 1 / xm m 55)
    +   ((1120236040399568623985819 : ℝ) / 80859811032) * (1 / xm m 53 - 1 / xm m 56)
    +   ((-(51305898548661588 : ℝ)) / 7315) * (1 / xm m 54 - 1 / xm m 57)
    +   ((4352215853044440090727627 : ℝ) / 1057397528880) * (1 / xm m 55 - 1 / xm m 58)
    +   ((-(12258245126055317618228039 : ℝ)) / 1374616787544) * (1 / xm m 56 - 1 / xm m 59)
    +   ((43305862260420 : ℝ) / 7) * (1 / xm m 57 - 1 / xm m 60)
    +   ((-(1002091581864100896550553 : ℝ)) / 1057397528880) * (1 / xm m 58 - 1 / xm m 61)
    +   ((-(387462672374836265948941 : ℝ)) / 6873083937720) * (1 / xm m 59 - 1 / xm m 62)
    +   ((-(2646469360359 : ℝ)) / 14) * (1 / xm m 60 - 1 / xm m 63)
    +   ((-(14580088722403719730148 : ℝ)) / 66087345555) * (1 / xm m 61 - 1 / xm m 64)
    +   ((66903851674058524782403 : ℝ) / 196373826792) * (1 / xm m 62 - 1 / xm m 65)
    +   ((-(240588123669 : ℝ)) / 2) * (1 / xm m 63 - 1 / xm m 66)
    +   ((264449074987121296043 : ℝ) / 132174691110) * (1 / xm m 64 - 1 / xm m 67)
    +   ((470699230432790569267 : ℝ) / 105739752888) * (1 / xm m 65 - 1 / xm m 68)

/-- The closed-form decomposition of the summand (as `W111 + W211`). -/
def Vd11 (m : ℕ) : ℝ := W111 m + W211 m

set_option maxHeartbeats 0 in
lemma vm11_decomp (m : ℕ) : Vm11 m = Vd11 m := by
  unfold Vm11 Vd11 W111 W211
  rw [choose2222]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero,
    c23_0, c23_1, c23_2, c23_3, c23_4, c23_5, c23_6, c23_7, c23_8, c23_9, c23_10, c23_11, c23_12, c23_13, c23_14, c23_15, c23_16, c23_17, c23_18, c23_19, c23_20, c23_21, c23_22, c23_23]
  norm_num
  simp_rw [xm_eq]
  norm_num
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
  have h63 : (3 * (m : ℝ) + 63) ≠ 0 := by positivity
  have h64 : (3 * (m : ℝ) + 64) ≠ 0 := by positivity
  have h65 : (3 * (m : ℝ) + 65) ≠ 0 := by positivity
  have h66 : (3 * (m : ℝ) + 66) ≠ 0 := by positivity
  have h67 : (3 * (m : ℝ) + 67) ≠ 0 := by positivity
  have h68 : (3 * (m : ℝ) + 68) ≠ 0 := by positivity
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
  have hm21 : (m : ℝ) + 21 ≠ 0 := by positivity
  have hm22 : (m : ℝ) + 22 ≠ 0 := by positivity
  field_simp
  ring

/-! ## The statement denominators equal the `xm` denominators -/

lemma denom_statement11 (m : ℕ) : ∀ i : ℕ,
    (((3 * m + 12 + i : ℕ) : ℝ) * ((3 * m + 15 + i : ℕ) : ℝ) * ((3 * m + 18 + i : ℕ) : ℝ) * ((3 * m + 21 + i : ℕ) : ℝ) * ((3 * m + 24 + i : ℕ) : ℝ) * ((3 * m + 27 + i : ℕ) : ℝ) * ((3 * m + 30 + i : ℕ) : ℝ) * ((3 * m + 33 + i : ℕ) : ℝ) * ((3 * m + 36 + i : ℕ) : ℝ) * ((3 * m + 39 + i : ℕ) : ℝ) * ((3 * m + 42 + i : ℕ) : ℝ) * ((3 * m + 45 + i : ℕ) : ℝ))
      = xm m (12 + i) * xm m (15 + i) * xm m (18 + i) * xm m (21 + i) * xm m (24 + i) * xm m (27 + i) * xm m (30 + i) * xm m (33 + i) * xm m (36 + i) * xm m (39 + i) * xm m (42 + i) * xm m (45 + i) := by
  intro i
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
  have h24 : (((3 * m + 24 + i : ℕ) : ℝ)) = xm m (24 + i) := by
    unfold xm
    congr 1
    omega
  have h27 : (((3 * m + 27 + i : ℕ) : ℝ)) = xm m (27 + i) := by
    unfold xm
    congr 1
    omega
  have h30 : (((3 * m + 30 + i : ℕ) : ℝ)) = xm m (30 + i) := by
    unfold xm
    congr 1
    omega
  have h33 : (((3 * m + 33 + i : ℕ) : ℝ)) = xm m (33 + i) := by
    unfold xm
    congr 1
    omega
  have h36 : (((3 * m + 36 + i : ℕ) : ℝ)) = xm m (36 + i) := by
    unfold xm
    congr 1
    omega
  have h39 : (((3 * m + 39 + i : ℕ) : ℝ)) = xm m (39 + i) := by
    unfold xm
    congr 1
    omega
  have h42 : (((3 * m + 42 + i : ℕ) : ℝ)) = xm m (42 + i) := by
    unfold xm
    congr 1
    omega
  have h45 : (((3 * m + 45 + i : ℕ) : ℝ)) = xm m (45 + i) := by
    unfold xm
    congr 1
    omega
  rw [h12, h15, h18, h21, h24, h27, h30, h33, h36, h39, h42, h45]

/-- The inner `i`-sum in the statement's form equals the `xm` form. -/
lemma inner_sum_statement11 (m : ℕ) :
    (∑ i ∈ Finset.range 24,
      ((-1 : ℝ) ^ i * (Nat.choose 23 i : ℝ)) *
        (7071141369600 / (((3 * m + 12 + i : ℕ) : ℝ) * ((3 * m + 15 + i : ℕ) : ℝ) * ((3 * m + 18 + i : ℕ) : ℝ) * ((3 * m + 21 + i : ℕ) : ℝ) * ((3 * m + 24 + i : ℕ) : ℝ) * ((3 * m + 27 + i : ℕ) : ℝ) * ((3 * m + 30 + i : ℕ) : ℝ) * ((3 * m + 33 + i : ℕ) : ℝ) * ((3 * m + 36 + i : ℕ) : ℝ) * ((3 * m + 39 + i : ℕ) : ℝ) * ((3 * m + 42 + i : ℕ) : ℝ) * ((3 * m + 45 + i : ℕ) : ℝ))) ^ 2)
    = (∑ i ∈ Finset.range 24,
      ((-1 : ℝ) ^ i * (Nat.choose 23 i : ℝ)) *
        (7071141369600 / (xm m (12 + i) * xm m (15 + i) * xm m (18 + i) * xm m (21 + i) * xm m (24 + i) * xm m (27 + i) * xm m (30 + i) * xm m (33 + i) * xm m (36 + i) * xm m (39 + i) * xm m (42 + i) * xm m (45 + i))) ^ 2) := by
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  rw [denom_statement11 m i]

/-- The `m`-summand of the eleven-core sum, in the statement's form. -/
lemma vm11_eq_statement (m : ℕ) :
            (31381059609 : ℝ) * (Nat.choose (m + 22) 22 : ℝ) *
          (∑ i ∈ Finset.range 24,
            ((-1 : ℝ) ^ i * (Nat.choose 23 i : ℝ)) *
              (7071141369600 / ((((3 * m + 12 + i : ℕ) : ℝ) * ((3 * m + 15 + i : ℕ) : ℝ) * ((3 * m + 18 + i : ℕ) : ℝ) * ((3 * m + 21 + i : ℕ) : ℝ) * ((3 * m + 24 + i : ℕ) : ℝ) * ((3 * m + 27 + i : ℕ) : ℝ) * ((3 * m + 30 + i : ℕ) : ℝ) * ((3 * m + 33 + i : ℕ) : ℝ) * ((3 * m + 36 + i : ℕ) : ℝ) * ((3 * m + 39 + i : ℕ) : ℝ) * ((3 * m + 42 + i : ℕ) : ℝ) * ((3 * m + 45 + i : ℕ) : ℝ)))) ^ 2)
      = Vm11 m := by
  unfold Vm11
  rw [inner_sum_statement11 m]

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
@[simp] lemma asum21 : Asum 21 = 3684549952193975922105473598851248029 / 3300383043223308761830078040513440000 := by
  norm_num [Asum, f1, xm]
@[simp] lemma asum22 : Asum 22 = 58965691356366205803538476323965724089 / 52806128691572940189281248648215040000 := by
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
@[simp] lemma bsum21 : Bsum 21 = 348119547714745795747933442446861372161 / 1038597854007119650876910405667379840000 := by
  norm_num [Bsum, f2, xm]
@[simp] lemma bsum22 : Bsum 22 = 348365369692025587381277089880155426561 / 1038597854007119650876910405667379840000 := by
  norm_num [Bsum, f2, xm]

/-! ## The values of the two pieces -/

/-- The value of the `W111`-sum. -/
noncomputable def V1val11 : ℝ :=
  ((-(78339583550 : ℝ)) / 19683) * (A - Asum 4)
    +   ((522337996180 : ℝ) / 19683) * (B - Bsum 4)
    +   ((-(1690952520400 : ℝ)) / 6561) * (A - Asum 5)
    +   ((562517842040 : ℝ) / 6561) * (B - Bsum 5)
    +   ((67435186513552 : ℝ) / 6561) * (A - Asum 6)
    +   ((-(181010205599300 : ℝ)) / 6561) * (B - Bsum 6)
    +   ((85009579857488 : ℝ) / 6561) * (A - Asum 7)
    +   ((1031983607849600 : ℝ) / 6561) * (B - Bsum 7)
    +   ((-(6587900650679920 : ℝ)) / 6561) * (A - Asum 8)
    +   ((6456174388304300 : ℝ) / 6561) * (B - Bsum 8)
    +   ((26276215779985600 : ℝ) / 6561) * (A - Asum 9)
    +   ((-(55845231074686625 : ℝ)) / 6561) * (B - Bsum 9)
    +   ((23498580125020000 : ℝ) / 6561) * (A - Asum 10)
    +   ((90756265764221200 : ℝ) / 6561) * (B - Bsum 10)
    +   ((-(313546476451046800 : ℝ)) / 6561) * (A - Asum 11)
    +   ((199260323885090000 : ℝ) / 6561) * (B - Bsum 11)
    +   ((570358606100384530 : ℝ) / 6561) * (A - Asum 12)
    +   ((-(820192712334195200 : ℝ)) / 6561) * (B - Bsum 12)
    +   ((0 : ℝ) / 1) * (A - Asum 13)
    +   ((265918374264228400 : ℝ) / 2187) * (B - Bsum 13)
    +   ((-(1119536786510038600 : ℝ)) / 6561) * (A - Asum 14)
    +   ((343613891405933720 : ℝ) / 6561) * (B - Bsum 14)
    +   ((1222536551229884500 : ℝ) / 6561) * (A - Asum 15)
    +   ((-(1170533969172751040 : ℝ)) / 6561) * (B - Bsum 15)
    +   ((-(186647868471806500 : ℝ)) / 6561) * (A - Asum 16)
    +   ((677443588019884400 : ℝ) / 6561) * (B - Bsum 16)
    +   ((-(443267434634572240 : ℝ)) / 6561) * (A - Asum 17)
    +   ((68714438045031350 : ℝ) / 6561) * (B - Bsum 17)
    +   ((251699010219256600 : ℝ) / 6561) * (A - Asum 18)
    +   ((-(181350672583814600 : ℝ)) / 6561) * (B - Bsum 18)
    +   ((-(8119744150618100 : ℝ)) / 6561) * (A - Asum 19)
    +   ((38576163021836440 : ℝ) / 6561) * (B - Bsum 19)
    +   ((-(18877948104440425 : ℝ)) / 6561) * (A - Asum 20)
    +   ((5911864655553560 : ℝ) / 6561) * (B - Bsum 20)
    +   ((1848031830484840 : ℝ) / 6561) * (A - Asum 21)
    +   ((-(1370533983863000 : ℝ)) / 6561) * (B - Bsum 21)
    +   ((672011574721760 : ℝ) / 19683) * (A - Asum 22)
    +   ((-(161972198092900 : ℝ)) / 19683) * (B - Bsum 22)

/-- The value of the `W211`-sum. -/
noncomputable def V2val11 : ℝ :=
  ((-(10460353203 : ℝ)) / 29260) * (1 / xm 0 12)
    +   ((22979834417835971629 : ℝ) / 2749233575088) * (1 / xm 0 13)
    +   ((-(589752713661955937 : ℝ)) / 24031762020) * (1 / xm 0 14)
    +   ((-(3845923194303 : ℝ)) / 29260) * (1 / xm 0 15)
    +   ((106770018516046364165 : ℝ) / 161719622064) * (1 / xm 0 16)
    +   ((-(46257936490474335187 : ℝ)) / 62482581252) * (1 / xm 0 17)
    +   ((1216814533476579 : ℝ) / 497420) * (1 / xm 0 18)
    +   ((-(181985894706236778816751 : ℝ)) / 13746167875440) * (1 / xm 0 19)
    +   ((139031538388232398886 : ℝ) / 15620645313) * (1 / xm 0 20)
    +   ((110644912509177051 : ℝ) / 1989680) * (1 / xm 0 21)
    +   ((-(236883056754292922329403 : ℝ)) / 2749233575088) * (1 / xm 0 22)
    +   ((15233037352297344431578 : ℝ) / 171827098443) * (1 / xm 0 23)
    +   ((-(1188892785894283521 : ℝ)) / 1989680) * (1 / xm 0 24)
    +   ((3453701270768741997759565 : ℝ) / 2749233575088) * (1 / xm 0 25)
    +   ((-(311116735461465230093639 : ℝ)) / 687308393772) * (1 / xm 0 26)
    +   ((-(41763995737944597 : ℝ)) / 1989680) * (1 / xm 0 27)
    +   ((-(5053397914818780388195667 : ℝ)) / 2749233575088) * (1 / xm 0 28)
    +   ((-(5245958982321092598604553 : ℝ)) / 2749233575088) * (1 / xm 0 29)
    +   ((317532296798468484939 : ℝ) / 25865840) * (1 / xm 0 30)
    +   ((-(32285423602968746893537187 : ℝ)) / 2749233575088) * (1 / xm 0 31)
    +   ((26685916736540273874070183 : ℝ) / 2749233575088) * (1 / xm 0 32)
    +   ((-(62723034097796637297 : ℝ)) / 1989680) * (1 / xm 0 33)
    +   ((101648130000370270917630997 : ℝ) / 2749233575088) * (1 / xm 0 34)
    +   ((1987291845999927464565823 : ℝ) / 2749233575088) * (1 / xm 0 35)
    +   ((-(21464023333432562973 : ℝ)) / 3695120) * (1 / xm 0 36)
    +   ((-(26042350278493626797429959 : ℝ)) / 1963738267920) * (1 / xm 0 37)
    +   ((-(134492902121995335078095681 : ℝ)) / 2749233575088) * (1 / xm 0 38)
    +   ((11695740090101721099 : ℝ) / 104720) * (1 / xm 0 39)
    +   ((-(923589327565702456071470513 : ℝ)) / 13746167875440) * (1 / xm 0 40)
    +   ((161894305276494010433398583 : ℝ) / 2749233575088) * (1 / xm 0 41)
    +   ((-(49789350917107409187 : ℝ)) / 397936) * (1 / xm 0 42)
    +   ((1087599717796934030952068647 : ℝ) / 13746167875440) * (1 / xm 0 43)
    +   ((328080302811962663173477111 : ℝ) / 13746167875440) * (1 / xm 0 44)
    +   ((-(284786888652396882 : ℝ)) / 24871) * (1 / xm 0 45)
    +   ((6764952488387424150279547 : ℝ) / 13746167875440) * (1 / xm 0 46)
    +   ((-(212332086265051040067689941 : ℝ)) / 2749233575088) * (1 / xm 0 47)
    +   ((2312100868240277253 : ℝ) / 24871) * (1 / xm 0 48)
    +   ((-(506827321783160786341706873 : ℝ)) / 13746167875440) * (1 / xm 0 49)
    +   ((82494137795471831640577907 : ℝ) / 2749233575088) * (1 / xm 0 50)
    +   ((-(17273184730898301 : ℝ)) / 418) * (1 / xm 0 51)
    +   ((10795296005161482509425747 : ℝ) / 1057397528880) * (1 / xm 0 52)
    +   ((1120236040399568623985819 : ℝ) / 80859811032) * (1 / xm 0 53)
    +   ((-(51305898548661588 : ℝ)) / 7315) * (1 / xm 0 54)
    +   ((4352215853044440090727627 : ℝ) / 1057397528880) * (1 / xm 0 55)
    +   ((-(12258245126055317618228039 : ℝ)) / 1374616787544) * (1 / xm 0 56)
    +   ((43305862260420 : ℝ) / 7) * (1 / xm 0 57)
    +   ((-(1002091581864100896550553 : ℝ)) / 1057397528880) * (1 / xm 0 58)
    +   ((-(387462672374836265948941 : ℝ)) / 6873083937720) * (1 / xm 0 59)
    +   ((-(2646469360359 : ℝ)) / 14) * (1 / xm 0 60)
    +   ((-(14580088722403719730148 : ℝ)) / 66087345555) * (1 / xm 0 61)
    +   ((66903851674058524782403 : ℝ) / 196373826792) * (1 / xm 0 62)
    +   ((-(240588123669 : ℝ)) / 2) * (1 / xm 0 63)
    +   ((264449074987121296043 : ℝ) / 132174691110) * (1 / xm 0 64)
    +   ((470699230432790569267 : ℝ) / 105739752888) * (1 / xm 0 65)

/-- The value of the whole sum. -/
noncomputable def Vval11 : ℝ := V1val11 + V2val11

/-! ## `HasSum` of the two pieces of the decomposition -/

lemma hasSum_W111 : HasSum W111 V1val11 := by
  have h13 : HasSum (fun m : ℕ => ((-(78339583550 : ℝ)) / 19683) * (1 / (xm m 13)^2))
      (((-(78339583550 : ℝ)) / 19683) * (A - Asum 4)) := by
    simpa using (CdtTwoCore.hasSum_sq1 4).mul_left ((-(78339583550 : ℝ)) / 19683)
  have h14 : HasSum (fun m : ℕ => ((522337996180 : ℝ) / 19683) * (1 / (xm m 14)^2))
      (((522337996180 : ℝ) / 19683) * (B - Bsum 4)) := by
    simpa using (CdtTwoCore.hasSum_sq2 4).mul_left ((522337996180 : ℝ) / 19683)
  have h16 : HasSum (fun m : ℕ => ((-(1690952520400 : ℝ)) / 6561) * (1 / (xm m 16)^2))
      (((-(1690952520400 : ℝ)) / 6561) * (A - Asum 5)) := by
    simpa using (CdtTwoCore.hasSum_sq1 5).mul_left ((-(1690952520400 : ℝ)) / 6561)
  have h17 : HasSum (fun m : ℕ => ((562517842040 : ℝ) / 6561) * (1 / (xm m 17)^2))
      (((562517842040 : ℝ) / 6561) * (B - Bsum 5)) := by
    simpa using (CdtTwoCore.hasSum_sq2 5).mul_left ((562517842040 : ℝ) / 6561)
  have h19 : HasSum (fun m : ℕ => ((67435186513552 : ℝ) / 6561) * (1 / (xm m 19)^2))
      (((67435186513552 : ℝ) / 6561) * (A - Asum 6)) := by
    simpa using (CdtTwoCore.hasSum_sq1 6).mul_left ((67435186513552 : ℝ) / 6561)
  have h20 : HasSum (fun m : ℕ => ((-(181010205599300 : ℝ)) / 6561) * (1 / (xm m 20)^2))
      (((-(181010205599300 : ℝ)) / 6561) * (B - Bsum 6)) := by
    simpa using (CdtTwoCore.hasSum_sq2 6).mul_left ((-(181010205599300 : ℝ)) / 6561)
  have h22 : HasSum (fun m : ℕ => ((85009579857488 : ℝ) / 6561) * (1 / (xm m 22)^2))
      (((85009579857488 : ℝ) / 6561) * (A - Asum 7)) := by
    simpa using (CdtTwoCore.hasSum_sq1 7).mul_left ((85009579857488 : ℝ) / 6561)
  have h23 : HasSum (fun m : ℕ => ((1031983607849600 : ℝ) / 6561) * (1 / (xm m 23)^2))
      (((1031983607849600 : ℝ) / 6561) * (B - Bsum 7)) := by
    simpa using (CdtTwoCore.hasSum_sq2 7).mul_left ((1031983607849600 : ℝ) / 6561)
  have h25 : HasSum (fun m : ℕ => ((-(6587900650679920 : ℝ)) / 6561) * (1 / (xm m 25)^2))
      (((-(6587900650679920 : ℝ)) / 6561) * (A - Asum 8)) := by
    simpa using (CdtTwoCore.hasSum_sq1 8).mul_left ((-(6587900650679920 : ℝ)) / 6561)
  have h26 : HasSum (fun m : ℕ => ((6456174388304300 : ℝ) / 6561) * (1 / (xm m 26)^2))
      (((6456174388304300 : ℝ) / 6561) * (B - Bsum 8)) := by
    simpa using (CdtTwoCore.hasSum_sq2 8).mul_left ((6456174388304300 : ℝ) / 6561)
  have h28 : HasSum (fun m : ℕ => ((26276215779985600 : ℝ) / 6561) * (1 / (xm m 28)^2))
      (((26276215779985600 : ℝ) / 6561) * (A - Asum 9)) := by
    simpa using (CdtTwoCore.hasSum_sq1 9).mul_left ((26276215779985600 : ℝ) / 6561)
  have h29 : HasSum (fun m : ℕ => ((-(55845231074686625 : ℝ)) / 6561) * (1 / (xm m 29)^2))
      (((-(55845231074686625 : ℝ)) / 6561) * (B - Bsum 9)) := by
    simpa using (CdtTwoCore.hasSum_sq2 9).mul_left ((-(55845231074686625 : ℝ)) / 6561)
  have h31 : HasSum (fun m : ℕ => ((23498580125020000 : ℝ) / 6561) * (1 / (xm m 31)^2))
      (((23498580125020000 : ℝ) / 6561) * (A - Asum 10)) := by
    simpa using (CdtTwoCore.hasSum_sq1 10).mul_left ((23498580125020000 : ℝ) / 6561)
  have h32 : HasSum (fun m : ℕ => ((90756265764221200 : ℝ) / 6561) * (1 / (xm m 32)^2))
      (((90756265764221200 : ℝ) / 6561) * (B - Bsum 10)) := by
    simpa using (CdtTwoCore.hasSum_sq2 10).mul_left ((90756265764221200 : ℝ) / 6561)
  have h34 : HasSum (fun m : ℕ => ((-(313546476451046800 : ℝ)) / 6561) * (1 / (xm m 34)^2))
      (((-(313546476451046800 : ℝ)) / 6561) * (A - Asum 11)) := by
    simpa using (CdtTwoCore.hasSum_sq1 11).mul_left ((-(313546476451046800 : ℝ)) / 6561)
  have h35 : HasSum (fun m : ℕ => ((199260323885090000 : ℝ) / 6561) * (1 / (xm m 35)^2))
      (((199260323885090000 : ℝ) / 6561) * (B - Bsum 11)) := by
    simpa using (CdtTwoCore.hasSum_sq2 11).mul_left ((199260323885090000 : ℝ) / 6561)
  have h37 : HasSum (fun m : ℕ => ((570358606100384530 : ℝ) / 6561) * (1 / (xm m 37)^2))
      (((570358606100384530 : ℝ) / 6561) * (A - Asum 12)) := by
    simpa using (CdtTwoCore.hasSum_sq1 12).mul_left ((570358606100384530 : ℝ) / 6561)
  have h38 : HasSum (fun m : ℕ => ((-(820192712334195200 : ℝ)) / 6561) * (1 / (xm m 38)^2))
      (((-(820192712334195200 : ℝ)) / 6561) * (B - Bsum 12)) := by
    simpa using (CdtTwoCore.hasSum_sq2 12).mul_left ((-(820192712334195200 : ℝ)) / 6561)
  have h40 : HasSum (fun m : ℕ => ((0 : ℝ) / 1) * (1 / (xm m 40)^2))
      (((0 : ℝ) / 1) * (A - Asum 13)) := by
    simpa using (CdtTwoCore.hasSum_sq1 13).mul_left ((0 : ℝ) / 1)
  have h41 : HasSum (fun m : ℕ => ((265918374264228400 : ℝ) / 2187) * (1 / (xm m 41)^2))
      (((265918374264228400 : ℝ) / 2187) * (B - Bsum 13)) := by
    simpa using (CdtTwoCore.hasSum_sq2 13).mul_left ((265918374264228400 : ℝ) / 2187)
  have h43 : HasSum (fun m : ℕ => ((-(1119536786510038600 : ℝ)) / 6561) * (1 / (xm m 43)^2))
      (((-(1119536786510038600 : ℝ)) / 6561) * (A - Asum 14)) := by
    simpa using (CdtTwoCore.hasSum_sq1 14).mul_left ((-(1119536786510038600 : ℝ)) / 6561)
  have h44 : HasSum (fun m : ℕ => ((343613891405933720 : ℝ) / 6561) * (1 / (xm m 44)^2))
      (((343613891405933720 : ℝ) / 6561) * (B - Bsum 14)) := by
    simpa using (CdtTwoCore.hasSum_sq2 14).mul_left ((343613891405933720 : ℝ) / 6561)
  have h46 : HasSum (fun m : ℕ => ((1222536551229884500 : ℝ) / 6561) * (1 / (xm m 46)^2))
      (((1222536551229884500 : ℝ) / 6561) * (A - Asum 15)) := by
    simpa using (CdtTwoCore.hasSum_sq1 15).mul_left ((1222536551229884500 : ℝ) / 6561)
  have h47 : HasSum (fun m : ℕ => ((-(1170533969172751040 : ℝ)) / 6561) * (1 / (xm m 47)^2))
      (((-(1170533969172751040 : ℝ)) / 6561) * (B - Bsum 15)) := by
    simpa using (CdtTwoCore.hasSum_sq2 15).mul_left ((-(1170533969172751040 : ℝ)) / 6561)
  have h49 : HasSum (fun m : ℕ => ((-(186647868471806500 : ℝ)) / 6561) * (1 / (xm m 49)^2))
      (((-(186647868471806500 : ℝ)) / 6561) * (A - Asum 16)) := by
    simpa using (CdtTwoCore.hasSum_sq1 16).mul_left ((-(186647868471806500 : ℝ)) / 6561)
  have h50 : HasSum (fun m : ℕ => ((677443588019884400 : ℝ) / 6561) * (1 / (xm m 50)^2))
      (((677443588019884400 : ℝ) / 6561) * (B - Bsum 16)) := by
    simpa using (CdtTwoCore.hasSum_sq2 16).mul_left ((677443588019884400 : ℝ) / 6561)
  have h52 : HasSum (fun m : ℕ => ((-(443267434634572240 : ℝ)) / 6561) * (1 / (xm m 52)^2))
      (((-(443267434634572240 : ℝ)) / 6561) * (A - Asum 17)) := by
    simpa using (CdtTwoCore.hasSum_sq1 17).mul_left ((-(443267434634572240 : ℝ)) / 6561)
  have h53 : HasSum (fun m : ℕ => ((68714438045031350 : ℝ) / 6561) * (1 / (xm m 53)^2))
      (((68714438045031350 : ℝ) / 6561) * (B - Bsum 17)) := by
    simpa using (CdtTwoCore.hasSum_sq2 17).mul_left ((68714438045031350 : ℝ) / 6561)
  have h55 : HasSum (fun m : ℕ => ((251699010219256600 : ℝ) / 6561) * (1 / (xm m 55)^2))
      (((251699010219256600 : ℝ) / 6561) * (A - Asum 18)) := by
    simpa using (CdtTwoCore.hasSum_sq1 18).mul_left ((251699010219256600 : ℝ) / 6561)
  have h56 : HasSum (fun m : ℕ => ((-(181350672583814600 : ℝ)) / 6561) * (1 / (xm m 56)^2))
      (((-(181350672583814600 : ℝ)) / 6561) * (B - Bsum 18)) := by
    simpa using (CdtTwoCore.hasSum_sq2 18).mul_left ((-(181350672583814600 : ℝ)) / 6561)
  have h58 : HasSum (fun m : ℕ => ((-(8119744150618100 : ℝ)) / 6561) * (1 / (xm m 58)^2))
      (((-(8119744150618100 : ℝ)) / 6561) * (A - Asum 19)) := by
    simpa using (CdtTwoCore.hasSum_sq1 19).mul_left ((-(8119744150618100 : ℝ)) / 6561)
  have h59 : HasSum (fun m : ℕ => ((38576163021836440 : ℝ) / 6561) * (1 / (xm m 59)^2))
      (((38576163021836440 : ℝ) / 6561) * (B - Bsum 19)) := by
    simpa using (CdtTwoCore.hasSum_sq2 19).mul_left ((38576163021836440 : ℝ) / 6561)
  have h61 : HasSum (fun m : ℕ => ((-(18877948104440425 : ℝ)) / 6561) * (1 / (xm m 61)^2))
      (((-(18877948104440425 : ℝ)) / 6561) * (A - Asum 20)) := by
    simpa using (CdtTwoCore.hasSum_sq1 20).mul_left ((-(18877948104440425 : ℝ)) / 6561)
  have h62 : HasSum (fun m : ℕ => ((5911864655553560 : ℝ) / 6561) * (1 / (xm m 62)^2))
      (((5911864655553560 : ℝ) / 6561) * (B - Bsum 20)) := by
    simpa using (CdtTwoCore.hasSum_sq2 20).mul_left ((5911864655553560 : ℝ) / 6561)
  have h64 : HasSum (fun m : ℕ => ((1848031830484840 : ℝ) / 6561) * (1 / (xm m 64)^2))
      (((1848031830484840 : ℝ) / 6561) * (A - Asum 21)) := by
    simpa using (CdtTwoCore.hasSum_sq1 21).mul_left ((1848031830484840 : ℝ) / 6561)
  have h65 : HasSum (fun m : ℕ => ((-(1370533983863000 : ℝ)) / 6561) * (1 / (xm m 65)^2))
      (((-(1370533983863000 : ℝ)) / 6561) * (B - Bsum 21)) := by
    simpa using (CdtTwoCore.hasSum_sq2 21).mul_left ((-(1370533983863000 : ℝ)) / 6561)
  have h67 : HasSum (fun m : ℕ => ((672011574721760 : ℝ) / 19683) * (1 / (xm m 67)^2))
      (((672011574721760 : ℝ) / 19683) * (A - Asum 22)) := by
    simpa using (CdtTwoCore.hasSum_sq1 22).mul_left ((672011574721760 : ℝ) / 19683)
  have h68 : HasSum (fun m : ℕ => ((-(161972198092900 : ℝ)) / 19683) * (1 / (xm m 68)^2))
      (((-(161972198092900 : ℝ)) / 19683) * (B - Bsum 22)) := by
    simpa using (CdtTwoCore.hasSum_sq2 22).mul_left ((-(161972198092900 : ℝ)) / 19683)
  exact (((((((((((((((((((((((((((((((((((((h13.add h14).add h16).add h17).add h19).add h20).add h22).add h23).add h25).add h26).add h28).add h29).add h31).add h32).add h34).add h35).add h37).add h38).add h40).add h41).add h43).add h44).add h46).add h47).add h49).add h50).add h52).add h53).add h55).add h56).add h58).add h59).add h61).add h62).add h64).add h65).add h67).add h68)

lemma hasSum_W211 : HasSum W211 V2val11 := by
  have hp12 : HasSum (fun m : ℕ => ((-(10460353203 : ℝ)) / 29260) * (1 / xm m 12 - 1 / xm m 15))
      (((-(10460353203 : ℝ)) / 29260) * (1 / xm 0 12)) := by
    simpa using (CdtTwoCore.hasSum_pair 12 (by norm_num)).mul_left ((-(10460353203 : ℝ)) / 29260)
  have hp13 : HasSum (fun m : ℕ => ((22979834417835971629 : ℝ) / 2749233575088) * (1 / xm m 13 - 1 / xm m 16))
      (((22979834417835971629 : ℝ) / 2749233575088) * (1 / xm 0 13)) := by
    simpa using (CdtTwoCore.hasSum_pair 13 (by norm_num)).mul_left ((22979834417835971629 : ℝ) / 2749233575088)
  have hp14 : HasSum (fun m : ℕ => ((-(589752713661955937 : ℝ)) / 24031762020) * (1 / xm m 14 - 1 / xm m 17))
      (((-(589752713661955937 : ℝ)) / 24031762020) * (1 / xm 0 14)) := by
    simpa using (CdtTwoCore.hasSum_pair 14 (by norm_num)).mul_left ((-(589752713661955937 : ℝ)) / 24031762020)
  have hp15 : HasSum (fun m : ℕ => ((-(3845923194303 : ℝ)) / 29260) * (1 / xm m 15 - 1 / xm m 18))
      (((-(3845923194303 : ℝ)) / 29260) * (1 / xm 0 15)) := by
    simpa using (CdtTwoCore.hasSum_pair 15 (by norm_num)).mul_left ((-(3845923194303 : ℝ)) / 29260)
  have hp16 : HasSum (fun m : ℕ => ((106770018516046364165 : ℝ) / 161719622064) * (1 / xm m 16 - 1 / xm m 19))
      (((106770018516046364165 : ℝ) / 161719622064) * (1 / xm 0 16)) := by
    simpa using (CdtTwoCore.hasSum_pair 16 (by norm_num)).mul_left ((106770018516046364165 : ℝ) / 161719622064)
  have hp17 : HasSum (fun m : ℕ => ((-(46257936490474335187 : ℝ)) / 62482581252) * (1 / xm m 17 - 1 / xm m 20))
      (((-(46257936490474335187 : ℝ)) / 62482581252) * (1 / xm 0 17)) := by
    simpa using (CdtTwoCore.hasSum_pair 17 (by norm_num)).mul_left ((-(46257936490474335187 : ℝ)) / 62482581252)
  have hp18 : HasSum (fun m : ℕ => ((1216814533476579 : ℝ) / 497420) * (1 / xm m 18 - 1 / xm m 21))
      (((1216814533476579 : ℝ) / 497420) * (1 / xm 0 18)) := by
    simpa using (CdtTwoCore.hasSum_pair 18 (by norm_num)).mul_left ((1216814533476579 : ℝ) / 497420)
  have hp19 : HasSum (fun m : ℕ => ((-(181985894706236778816751 : ℝ)) / 13746167875440) * (1 / xm m 19 - 1 / xm m 22))
      (((-(181985894706236778816751 : ℝ)) / 13746167875440) * (1 / xm 0 19)) := by
    simpa using (CdtTwoCore.hasSum_pair 19 (by norm_num)).mul_left ((-(181985894706236778816751 : ℝ)) / 13746167875440)
  have hp20 : HasSum (fun m : ℕ => ((139031538388232398886 : ℝ) / 15620645313) * (1 / xm m 20 - 1 / xm m 23))
      (((139031538388232398886 : ℝ) / 15620645313) * (1 / xm 0 20)) := by
    simpa using (CdtTwoCore.hasSum_pair 20 (by norm_num)).mul_left ((139031538388232398886 : ℝ) / 15620645313)
  have hp21 : HasSum (fun m : ℕ => ((110644912509177051 : ℝ) / 1989680) * (1 / xm m 21 - 1 / xm m 24))
      (((110644912509177051 : ℝ) / 1989680) * (1 / xm 0 21)) := by
    simpa using (CdtTwoCore.hasSum_pair 21 (by norm_num)).mul_left ((110644912509177051 : ℝ) / 1989680)
  have hp22 : HasSum (fun m : ℕ => ((-(236883056754292922329403 : ℝ)) / 2749233575088) * (1 / xm m 22 - 1 / xm m 25))
      (((-(236883056754292922329403 : ℝ)) / 2749233575088) * (1 / xm 0 22)) := by
    simpa using (CdtTwoCore.hasSum_pair 22 (by norm_num)).mul_left ((-(236883056754292922329403 : ℝ)) / 2749233575088)
  have hp23 : HasSum (fun m : ℕ => ((15233037352297344431578 : ℝ) / 171827098443) * (1 / xm m 23 - 1 / xm m 26))
      (((15233037352297344431578 : ℝ) / 171827098443) * (1 / xm 0 23)) := by
    simpa using (CdtTwoCore.hasSum_pair 23 (by norm_num)).mul_left ((15233037352297344431578 : ℝ) / 171827098443)
  have hp24 : HasSum (fun m : ℕ => ((-(1188892785894283521 : ℝ)) / 1989680) * (1 / xm m 24 - 1 / xm m 27))
      (((-(1188892785894283521 : ℝ)) / 1989680) * (1 / xm 0 24)) := by
    simpa using (CdtTwoCore.hasSum_pair 24 (by norm_num)).mul_left ((-(1188892785894283521 : ℝ)) / 1989680)
  have hp25 : HasSum (fun m : ℕ => ((3453701270768741997759565 : ℝ) / 2749233575088) * (1 / xm m 25 - 1 / xm m 28))
      (((3453701270768741997759565 : ℝ) / 2749233575088) * (1 / xm 0 25)) := by
    simpa using (CdtTwoCore.hasSum_pair 25 (by norm_num)).mul_left ((3453701270768741997759565 : ℝ) / 2749233575088)
  have hp26 : HasSum (fun m : ℕ => ((-(311116735461465230093639 : ℝ)) / 687308393772) * (1 / xm m 26 - 1 / xm m 29))
      (((-(311116735461465230093639 : ℝ)) / 687308393772) * (1 / xm 0 26)) := by
    simpa using (CdtTwoCore.hasSum_pair 26 (by norm_num)).mul_left ((-(311116735461465230093639 : ℝ)) / 687308393772)
  have hp27 : HasSum (fun m : ℕ => ((-(41763995737944597 : ℝ)) / 1989680) * (1 / xm m 27 - 1 / xm m 30))
      (((-(41763995737944597 : ℝ)) / 1989680) * (1 / xm 0 27)) := by
    simpa using (CdtTwoCore.hasSum_pair 27 (by norm_num)).mul_left ((-(41763995737944597 : ℝ)) / 1989680)
  have hp28 : HasSum (fun m : ℕ => ((-(5053397914818780388195667 : ℝ)) / 2749233575088) * (1 / xm m 28 - 1 / xm m 31))
      (((-(5053397914818780388195667 : ℝ)) / 2749233575088) * (1 / xm 0 28)) := by
    simpa using (CdtTwoCore.hasSum_pair 28 (by norm_num)).mul_left ((-(5053397914818780388195667 : ℝ)) / 2749233575088)
  have hp29 : HasSum (fun m : ℕ => ((-(5245958982321092598604553 : ℝ)) / 2749233575088) * (1 / xm m 29 - 1 / xm m 32))
      (((-(5245958982321092598604553 : ℝ)) / 2749233575088) * (1 / xm 0 29)) := by
    simpa using (CdtTwoCore.hasSum_pair 29 (by norm_num)).mul_left ((-(5245958982321092598604553 : ℝ)) / 2749233575088)
  have hp30 : HasSum (fun m : ℕ => ((317532296798468484939 : ℝ) / 25865840) * (1 / xm m 30 - 1 / xm m 33))
      (((317532296798468484939 : ℝ) / 25865840) * (1 / xm 0 30)) := by
    simpa using (CdtTwoCore.hasSum_pair 30 (by norm_num)).mul_left ((317532296798468484939 : ℝ) / 25865840)
  have hp31 : HasSum (fun m : ℕ => ((-(32285423602968746893537187 : ℝ)) / 2749233575088) * (1 / xm m 31 - 1 / xm m 34))
      (((-(32285423602968746893537187 : ℝ)) / 2749233575088) * (1 / xm 0 31)) := by
    simpa using (CdtTwoCore.hasSum_pair 31 (by norm_num)).mul_left ((-(32285423602968746893537187 : ℝ)) / 2749233575088)
  have hp32 : HasSum (fun m : ℕ => ((26685916736540273874070183 : ℝ) / 2749233575088) * (1 / xm m 32 - 1 / xm m 35))
      (((26685916736540273874070183 : ℝ) / 2749233575088) * (1 / xm 0 32)) := by
    simpa using (CdtTwoCore.hasSum_pair 32 (by norm_num)).mul_left ((26685916736540273874070183 : ℝ) / 2749233575088)
  have hp33 : HasSum (fun m : ℕ => ((-(62723034097796637297 : ℝ)) / 1989680) * (1 / xm m 33 - 1 / xm m 36))
      (((-(62723034097796637297 : ℝ)) / 1989680) * (1 / xm 0 33)) := by
    simpa using (CdtTwoCore.hasSum_pair 33 (by norm_num)).mul_left ((-(62723034097796637297 : ℝ)) / 1989680)
  have hp34 : HasSum (fun m : ℕ => ((101648130000370270917630997 : ℝ) / 2749233575088) * (1 / xm m 34 - 1 / xm m 37))
      (((101648130000370270917630997 : ℝ) / 2749233575088) * (1 / xm 0 34)) := by
    simpa using (CdtTwoCore.hasSum_pair 34 (by norm_num)).mul_left ((101648130000370270917630997 : ℝ) / 2749233575088)
  have hp35 : HasSum (fun m : ℕ => ((1987291845999927464565823 : ℝ) / 2749233575088) * (1 / xm m 35 - 1 / xm m 38))
      (((1987291845999927464565823 : ℝ) / 2749233575088) * (1 / xm 0 35)) := by
    simpa using (CdtTwoCore.hasSum_pair 35 (by norm_num)).mul_left ((1987291845999927464565823 : ℝ) / 2749233575088)
  have hp36 : HasSum (fun m : ℕ => ((-(21464023333432562973 : ℝ)) / 3695120) * (1 / xm m 36 - 1 / xm m 39))
      (((-(21464023333432562973 : ℝ)) / 3695120) * (1 / xm 0 36)) := by
    simpa using (CdtTwoCore.hasSum_pair 36 (by norm_num)).mul_left ((-(21464023333432562973 : ℝ)) / 3695120)
  have hp37 : HasSum (fun m : ℕ => ((-(26042350278493626797429959 : ℝ)) / 1963738267920) * (1 / xm m 37 - 1 / xm m 40))
      (((-(26042350278493626797429959 : ℝ)) / 1963738267920) * (1 / xm 0 37)) := by
    simpa using (CdtTwoCore.hasSum_pair 37 (by norm_num)).mul_left ((-(26042350278493626797429959 : ℝ)) / 1963738267920)
  have hp38 : HasSum (fun m : ℕ => ((-(134492902121995335078095681 : ℝ)) / 2749233575088) * (1 / xm m 38 - 1 / xm m 41))
      (((-(134492902121995335078095681 : ℝ)) / 2749233575088) * (1 / xm 0 38)) := by
    simpa using (CdtTwoCore.hasSum_pair 38 (by norm_num)).mul_left ((-(134492902121995335078095681 : ℝ)) / 2749233575088)
  have hp39 : HasSum (fun m : ℕ => ((11695740090101721099 : ℝ) / 104720) * (1 / xm m 39 - 1 / xm m 42))
      (((11695740090101721099 : ℝ) / 104720) * (1 / xm 0 39)) := by
    simpa using (CdtTwoCore.hasSum_pair 39 (by norm_num)).mul_left ((11695740090101721099 : ℝ) / 104720)
  have hp40 : HasSum (fun m : ℕ => ((-(923589327565702456071470513 : ℝ)) / 13746167875440) * (1 / xm m 40 - 1 / xm m 43))
      (((-(923589327565702456071470513 : ℝ)) / 13746167875440) * (1 / xm 0 40)) := by
    simpa using (CdtTwoCore.hasSum_pair 40 (by norm_num)).mul_left ((-(923589327565702456071470513 : ℝ)) / 13746167875440)
  have hp41 : HasSum (fun m : ℕ => ((161894305276494010433398583 : ℝ) / 2749233575088) * (1 / xm m 41 - 1 / xm m 44))
      (((161894305276494010433398583 : ℝ) / 2749233575088) * (1 / xm 0 41)) := by
    simpa using (CdtTwoCore.hasSum_pair 41 (by norm_num)).mul_left ((161894305276494010433398583 : ℝ) / 2749233575088)
  have hp42 : HasSum (fun m : ℕ => ((-(49789350917107409187 : ℝ)) / 397936) * (1 / xm m 42 - 1 / xm m 45))
      (((-(49789350917107409187 : ℝ)) / 397936) * (1 / xm 0 42)) := by
    simpa using (CdtTwoCore.hasSum_pair 42 (by norm_num)).mul_left ((-(49789350917107409187 : ℝ)) / 397936)
  have hp43 : HasSum (fun m : ℕ => ((1087599717796934030952068647 : ℝ) / 13746167875440) * (1 / xm m 43 - 1 / xm m 46))
      (((1087599717796934030952068647 : ℝ) / 13746167875440) * (1 / xm 0 43)) := by
    simpa using (CdtTwoCore.hasSum_pair 43 (by norm_num)).mul_left ((1087599717796934030952068647 : ℝ) / 13746167875440)
  have hp44 : HasSum (fun m : ℕ => ((328080302811962663173477111 : ℝ) / 13746167875440) * (1 / xm m 44 - 1 / xm m 47))
      (((328080302811962663173477111 : ℝ) / 13746167875440) * (1 / xm 0 44)) := by
    simpa using (CdtTwoCore.hasSum_pair 44 (by norm_num)).mul_left ((328080302811962663173477111 : ℝ) / 13746167875440)
  have hp45 : HasSum (fun m : ℕ => ((-(284786888652396882 : ℝ)) / 24871) * (1 / xm m 45 - 1 / xm m 48))
      (((-(284786888652396882 : ℝ)) / 24871) * (1 / xm 0 45)) := by
    simpa using (CdtTwoCore.hasSum_pair 45 (by norm_num)).mul_left ((-(284786888652396882 : ℝ)) / 24871)
  have hp46 : HasSum (fun m : ℕ => ((6764952488387424150279547 : ℝ) / 13746167875440) * (1 / xm m 46 - 1 / xm m 49))
      (((6764952488387424150279547 : ℝ) / 13746167875440) * (1 / xm 0 46)) := by
    simpa using (CdtTwoCore.hasSum_pair 46 (by norm_num)).mul_left ((6764952488387424150279547 : ℝ) / 13746167875440)
  have hp47 : HasSum (fun m : ℕ => ((-(212332086265051040067689941 : ℝ)) / 2749233575088) * (1 / xm m 47 - 1 / xm m 50))
      (((-(212332086265051040067689941 : ℝ)) / 2749233575088) * (1 / xm 0 47)) := by
    simpa using (CdtTwoCore.hasSum_pair 47 (by norm_num)).mul_left ((-(212332086265051040067689941 : ℝ)) / 2749233575088)
  have hp48 : HasSum (fun m : ℕ => ((2312100868240277253 : ℝ) / 24871) * (1 / xm m 48 - 1 / xm m 51))
      (((2312100868240277253 : ℝ) / 24871) * (1 / xm 0 48)) := by
    simpa using (CdtTwoCore.hasSum_pair 48 (by norm_num)).mul_left ((2312100868240277253 : ℝ) / 24871)
  have hp49 : HasSum (fun m : ℕ => ((-(506827321783160786341706873 : ℝ)) / 13746167875440) * (1 / xm m 49 - 1 / xm m 52))
      (((-(506827321783160786341706873 : ℝ)) / 13746167875440) * (1 / xm 0 49)) := by
    simpa using (CdtTwoCore.hasSum_pair 49 (by norm_num)).mul_left ((-(506827321783160786341706873 : ℝ)) / 13746167875440)
  have hp50 : HasSum (fun m : ℕ => ((82494137795471831640577907 : ℝ) / 2749233575088) * (1 / xm m 50 - 1 / xm m 53))
      (((82494137795471831640577907 : ℝ) / 2749233575088) * (1 / xm 0 50)) := by
    simpa using (CdtTwoCore.hasSum_pair 50 (by norm_num)).mul_left ((82494137795471831640577907 : ℝ) / 2749233575088)
  have hp51 : HasSum (fun m : ℕ => ((-(17273184730898301 : ℝ)) / 418) * (1 / xm m 51 - 1 / xm m 54))
      (((-(17273184730898301 : ℝ)) / 418) * (1 / xm 0 51)) := by
    simpa using (CdtTwoCore.hasSum_pair 51 (by norm_num)).mul_left ((-(17273184730898301 : ℝ)) / 418)
  have hp52 : HasSum (fun m : ℕ => ((10795296005161482509425747 : ℝ) / 1057397528880) * (1 / xm m 52 - 1 / xm m 55))
      (((10795296005161482509425747 : ℝ) / 1057397528880) * (1 / xm 0 52)) := by
    simpa using (CdtTwoCore.hasSum_pair 52 (by norm_num)).mul_left ((10795296005161482509425747 : ℝ) / 1057397528880)
  have hp53 : HasSum (fun m : ℕ => ((1120236040399568623985819 : ℝ) / 80859811032) * (1 / xm m 53 - 1 / xm m 56))
      (((1120236040399568623985819 : ℝ) / 80859811032) * (1 / xm 0 53)) := by
    simpa using (CdtTwoCore.hasSum_pair 53 (by norm_num)).mul_left ((1120236040399568623985819 : ℝ) / 80859811032)
  have hp54 : HasSum (fun m : ℕ => ((-(51305898548661588 : ℝ)) / 7315) * (1 / xm m 54 - 1 / xm m 57))
      (((-(51305898548661588 : ℝ)) / 7315) * (1 / xm 0 54)) := by
    simpa using (CdtTwoCore.hasSum_pair 54 (by norm_num)).mul_left ((-(51305898548661588 : ℝ)) / 7315)
  have hp55 : HasSum (fun m : ℕ => ((4352215853044440090727627 : ℝ) / 1057397528880) * (1 / xm m 55 - 1 / xm m 58))
      (((4352215853044440090727627 : ℝ) / 1057397528880) * (1 / xm 0 55)) := by
    simpa using (CdtTwoCore.hasSum_pair 55 (by norm_num)).mul_left ((4352215853044440090727627 : ℝ) / 1057397528880)
  have hp56 : HasSum (fun m : ℕ => ((-(12258245126055317618228039 : ℝ)) / 1374616787544) * (1 / xm m 56 - 1 / xm m 59))
      (((-(12258245126055317618228039 : ℝ)) / 1374616787544) * (1 / xm 0 56)) := by
    simpa using (CdtTwoCore.hasSum_pair 56 (by norm_num)).mul_left ((-(12258245126055317618228039 : ℝ)) / 1374616787544)
  have hp57 : HasSum (fun m : ℕ => ((43305862260420 : ℝ) / 7) * (1 / xm m 57 - 1 / xm m 60))
      (((43305862260420 : ℝ) / 7) * (1 / xm 0 57)) := by
    simpa using (CdtTwoCore.hasSum_pair 57 (by norm_num)).mul_left ((43305862260420 : ℝ) / 7)
  have hp58 : HasSum (fun m : ℕ => ((-(1002091581864100896550553 : ℝ)) / 1057397528880) * (1 / xm m 58 - 1 / xm m 61))
      (((-(1002091581864100896550553 : ℝ)) / 1057397528880) * (1 / xm 0 58)) := by
    simpa using (CdtTwoCore.hasSum_pair 58 (by norm_num)).mul_left ((-(1002091581864100896550553 : ℝ)) / 1057397528880)
  have hp59 : HasSum (fun m : ℕ => ((-(387462672374836265948941 : ℝ)) / 6873083937720) * (1 / xm m 59 - 1 / xm m 62))
      (((-(387462672374836265948941 : ℝ)) / 6873083937720) * (1 / xm 0 59)) := by
    simpa using (CdtTwoCore.hasSum_pair 59 (by norm_num)).mul_left ((-(387462672374836265948941 : ℝ)) / 6873083937720)
  have hp60 : HasSum (fun m : ℕ => ((-(2646469360359 : ℝ)) / 14) * (1 / xm m 60 - 1 / xm m 63))
      (((-(2646469360359 : ℝ)) / 14) * (1 / xm 0 60)) := by
    simpa using (CdtTwoCore.hasSum_pair 60 (by norm_num)).mul_left ((-(2646469360359 : ℝ)) / 14)
  have hp61 : HasSum (fun m : ℕ => ((-(14580088722403719730148 : ℝ)) / 66087345555) * (1 / xm m 61 - 1 / xm m 64))
      (((-(14580088722403719730148 : ℝ)) / 66087345555) * (1 / xm 0 61)) := by
    simpa using (CdtTwoCore.hasSum_pair 61 (by norm_num)).mul_left ((-(14580088722403719730148 : ℝ)) / 66087345555)
  have hp62 : HasSum (fun m : ℕ => ((66903851674058524782403 : ℝ) / 196373826792) * (1 / xm m 62 - 1 / xm m 65))
      (((66903851674058524782403 : ℝ) / 196373826792) * (1 / xm 0 62)) := by
    simpa using (CdtTwoCore.hasSum_pair 62 (by norm_num)).mul_left ((66903851674058524782403 : ℝ) / 196373826792)
  have hp63 : HasSum (fun m : ℕ => ((-(240588123669 : ℝ)) / 2) * (1 / xm m 63 - 1 / xm m 66))
      (((-(240588123669 : ℝ)) / 2) * (1 / xm 0 63)) := by
    simpa using (CdtTwoCore.hasSum_pair 63 (by norm_num)).mul_left ((-(240588123669 : ℝ)) / 2)
  have hp64 : HasSum (fun m : ℕ => ((264449074987121296043 : ℝ) / 132174691110) * (1 / xm m 64 - 1 / xm m 67))
      (((264449074987121296043 : ℝ) / 132174691110) * (1 / xm 0 64)) := by
    simpa using (CdtTwoCore.hasSum_pair 64 (by norm_num)).mul_left ((264449074987121296043 : ℝ) / 132174691110)
  have hp65 : HasSum (fun m : ℕ => ((470699230432790569267 : ℝ) / 105739752888) * (1 / xm m 65 - 1 / xm m 68))
      (((470699230432790569267 : ℝ) / 105739752888) * (1 / xm 0 65)) := by
    simpa using (CdtTwoCore.hasSum_pair 65 (by norm_num)).mul_left ((470699230432790569267 : ℝ) / 105739752888)
  exact (((((((((((((((((((((((((((((((((((((((((((((((((((((hp12.add hp13).add hp14).add hp15).add hp16).add hp17).add hp18).add hp19).add hp20).add hp21).add hp22).add hp23).add hp24).add hp25).add hp26).add hp27).add hp28).add hp29).add hp30).add hp31).add hp32).add hp33).add hp34).add hp35).add hp36).add hp37).add hp38).add hp39).add hp40).add hp41).add hp42).add hp43).add hp44).add hp45).add hp46).add hp47).add hp48).add hp49).add hp50).add hp51).add hp52).add hp53).add hp54).add hp55).add hp56).add hp57).add hp58).add hp59).add hp60).add hp61).add hp62).add hp63).add hp64).add hp65)

/-- `HasSum` for the whole summand. -/
lemma hasSum_Vm11 : HasSum Vm11 Vval11 := by
  have hsum : HasSum (fun m : ℕ => W111 m + W211 m) Vval11 := by
    simpa [Vval11] using hasSum_W111.add hasSum_W211
  apply HasSum.congr_fun hsum
  intro m
  exact vm11_decomp m

set_option maxHeartbeats 0 in
/-- The infinite sum of `Vm11` in closed form. -/
lemma tsum_Vm11 : (∑' m : ℕ, Vm11 m) = 1153462995 * A - 1153462995 * B - 4274588067098379 / 4743200 := by
  have hval : Vval11 = 1153462995 * A - 1153462995 * B - 4274588067098379 / 4743200 := by
    unfold Vval11 V1val11 V2val11
    norm_num [xm]
    ring
  rw [hasSum_Vm11.tsum_eq]
  exact hval

set_option maxHeartbeats 0 in
/-- The statement form, summed, in closed form. -/
lemma tsum_stmt11 :
    (∑' m : ℕ,
        (31381059609 : ℝ) * (Nat.choose (m + 22) 22 : ℝ) *
          (∑ i ∈ Finset.range 24,
            ((-1 : ℝ) ^ i * (Nat.choose 23 i : ℝ)) *
              (7071141369600 / ((((3 * m + 12 + i : ℕ) : ℝ) * ((3 * m + 15 + i : ℕ) : ℝ) * ((3 * m + 18 + i : ℕ) : ℝ) * ((3 * m + 21 + i : ℕ) : ℝ) * ((3 * m + 24 + i : ℕ) : ℝ) * ((3 * m + 27 + i : ℕ) : ℝ) * ((3 * m + 30 + i : ℕ) : ℝ) * ((3 * m + 33 + i : ℕ) : ℝ) * ((3 * m + 36 + i : ℕ) : ℝ) * ((3 * m + 39 + i : ℕ) : ℝ) * ((3 * m + 42 + i : ℕ) : ℝ) * ((3 * m + 45 + i : ℕ) : ℝ)))) ^ 2))
      = 1153462995 * A - 1153462995 * B - 4274588067098379 / 4743200 := by
  calc
    (∑' m : ℕ,
        (31381059609 : ℝ) * (Nat.choose (m + 22) 22 : ℝ) *
          (∑ i ∈ Finset.range 24,
            ((-1 : ℝ) ^ i * (Nat.choose 23 i : ℝ)) *
              (7071141369600 / ((((3 * m + 12 + i : ℕ) : ℝ) * ((3 * m + 15 + i : ℕ) : ℝ) * ((3 * m + 18 + i : ℕ) : ℝ) * ((3 * m + 21 + i : ℕ) : ℝ) * ((3 * m + 24 + i : ℕ) : ℝ) * ((3 * m + 27 + i : ℕ) : ℝ) * ((3 * m + 30 + i : ℕ) : ℝ) * ((3 * m + 33 + i : ℕ) : ℝ) * ((3 * m + 36 + i : ℕ) : ℝ) * ((3 * m + 39 + i : ℕ) : ℝ) * ((3 * m + 42 + i : ℕ) : ℝ) * ((3 * m + 45 + i : ℕ) : ℝ)))) ^ 2)) = (∑' m : ℕ, Vm11 m) := by
        apply tsum_congr
        intro m
        exact vm11_eq_statement m
    _ = 1153462995 * A - 1153462995 * B - 4274588067098379 / 4743200 := tsum_Vm11

end CdtElevenCore
open CdtElevenCore
theorem sum_cintegralEleven_core :
    (∑' m : ℕ,
        (31381059609 : ℝ) * (Nat.choose (m + 22) 22 : ℝ) *
          (∑ i ∈ Finset.range 24,
            ((-1 : ℝ) ^ i * (Nat.choose 23 i : ℝ)) *
              (7071141369600 / ((((3 * m + 12 + i : ℕ) : ℝ) * ((3 * m + 15 + i : ℕ) : ℝ) * ((3 * m + 18 + i : ℕ) : ℝ) * ((3 * m + 21 + i : ℕ) : ℝ) * ((3 * m + 24 + i : ℕ) : ℝ) * ((3 * m + 27 + i : ℕ) : ℝ) * ((3 * m + 30 + i : ℕ) : ℝ) * ((3 * m + 33 + i : ℕ) : ℝ) * ((3 * m + 36 + i : ℕ) : ℝ) * ((3 * m + 39 + i : ℕ) : ℝ) * ((3 * m + 42 + i : ℕ) : ℝ) * ((3 * m + 45 + i : ℕ) : ℝ)))) ^ 2)) =
      1153462995 * (∑' k : ℕ,
          ((1 : ℝ) / (((3 * k + 1 : ℕ) : ℝ) ^ 2) - (1 : ℝ) / (((3 * k + 2 : ℕ) : ℝ) ^ 2))) - 4274588067098379 / 4743200 := by
  have hMain := tsum_stmt11
  rw [hMain]
  have hR : (∑' k : ℕ,
          ((1 : ℝ) / (((3 * k + 1 : ℕ) : ℝ) ^ 2) - (1 : ℝ) / (((3 * k + 2 : ℕ) : ℝ) ^ 2))) = A - B := by
    simpa [Rk, f1, f2, xm] using tsum_Rk
  rw [hR]
  ring
end Commons.Analysis.Summation
