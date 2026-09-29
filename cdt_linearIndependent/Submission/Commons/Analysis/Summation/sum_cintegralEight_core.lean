import Mathlib
import Submission.Commons.Analysis.Summation.sum_cintegralFour_core

noncomputable section
open scoped BigOperators Nat
open Filter Topology

namespace Commons.Analysis.Summation
namespace CdtEightCore

/-! ## Binomial `(m+16 choose 16)` as a degree-16 polynomial -/

lemma asc16 (n : ℕ) : n.ascFactorial 16 =
    n * (n + 1) * (n + 2) * (n + 3) * (n + 4) * (n + 5) * (n + 6) * (n + 7) *
      (n + 8) * (n + 9) * (n + 10) * (n + 11) * (n + 12) * (n + 13) * (n + 14) *
        (n + 15) := by
  simp [Nat.ascFactorial_succ, Nat.ascFactorial_zero]
  ring

lemma factorial_add_sixteen (m : ℕ) : (m + 16)! =
    m ! * (m + 1) * (m + 2) * (m + 3) * (m + 4) * (m + 5) * (m + 6) * (m + 7) *
      (m + 8) * (m + 9) * (m + 10) * (m + 11) * (m + 12) * (m + 13) * (m + 14) *
        (m + 15) * (m + 16) := by
  rw [← Nat.factorial_mul_ascFactorial m 16]
  have h := asc16 (m + 1)
  rw [h]
  ring

lemma choose216 (m : ℕ) :
    (Nat.choose (m + 16) 16 : ℝ) =
      (1 / 20922789888000 : ℝ) *
        (((m : ℝ) + 1) * ((m : ℝ) + 2) * ((m : ℝ) + 3) * ((m : ℝ) + 4) *
          ((m : ℝ) + 5) * ((m : ℝ) + 6) * ((m : ℝ) + 7) * ((m : ℝ) + 8) *
          ((m : ℝ) + 9) * ((m : ℝ) + 10) * ((m : ℝ) + 11) * ((m : ℝ) + 12) *
          ((m : ℝ) + 13) * ((m : ℝ) + 14) * ((m : ℝ) + 15) * ((m : ℝ) + 16)) := by
  have hcast := Nat.cast_choose ℝ (a := 16) (b := m + 16) (by omega : 16 ≤ m + 16)
  rw [hcast]
  have h16 : ((16 : ℕ)! : ℝ) = 20922789888000 := by norm_num
  have hsub : ((m + 16 - 16) : ℕ) = m := by omega
  rw [h16, hsub]
  have hfacR : ((m + 16)! : ℝ) = (m ! : ℝ) *
      (((m : ℝ) + 1) * ((m : ℝ) + 2) * ((m : ℝ) + 3) * ((m : ℝ) + 4) *
        ((m : ℝ) + 5) * ((m : ℝ) + 6) * ((m : ℝ) + 7) * ((m : ℝ) + 8) *
        ((m : ℝ) + 9) * ((m : ℝ) + 10) * ((m : ℝ) + 11) * ((m : ℝ) + 12) *
        ((m : ℝ) + 13) * ((m : ℝ) + 14) * ((m : ℝ) + 15) * ((m : ℝ) + 16)) := by
    norm_num [factorial_add_sixteen, Nat.cast_mul]
    ring
  rw [hfacR]
  have hm : (m ! : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_ne_zero m)
  field_simp [hm]

@[simp] lemma c17_0 : (Nat.choose 17 0 : ℝ) = 1 := by
  rw [Nat.cast_choose ℝ (by decide : 0 ≤ 17)]; norm_num
@[simp] lemma c17_1 : (Nat.choose 17 1 : ℝ) = 17 := by
  rw [Nat.cast_choose ℝ (by decide : 1 ≤ 17)]; norm_num
@[simp] lemma c17_2 : (Nat.choose 17 2 : ℝ) = 136 := by
  rw [Nat.cast_choose ℝ (by decide : 2 ≤ 17)]; norm_num
@[simp] lemma c17_3 : (Nat.choose 17 3 : ℝ) = 680 := by
  rw [Nat.cast_choose ℝ (by decide : 3 ≤ 17)]; norm_num
@[simp] lemma c17_4 : (Nat.choose 17 4 : ℝ) = 2380 := by
  rw [Nat.cast_choose ℝ (by decide : 4 ≤ 17)]; norm_num
@[simp] lemma c17_5 : (Nat.choose 17 5 : ℝ) = 6188 := by
  rw [Nat.cast_choose ℝ (by decide : 5 ≤ 17)]; norm_num
@[simp] lemma c17_6 : (Nat.choose 17 6 : ℝ) = 12376 := by
  rw [Nat.cast_choose ℝ (by decide : 6 ≤ 17)]; norm_num
@[simp] lemma c17_7 : (Nat.choose 17 7 : ℝ) = 19448 := by
  rw [Nat.cast_choose ℝ (by decide : 7 ≤ 17)]; norm_num
@[simp] lemma c17_8 : (Nat.choose 17 8 : ℝ) = 24310 := by
  rw [Nat.cast_choose ℝ (by decide : 8 ≤ 17)]; norm_num
@[simp] lemma c17_9 : (Nat.choose 17 9 : ℝ) = 24310 := by
  rw [Nat.cast_choose ℝ (by decide : 9 ≤ 17)]; norm_num
@[simp] lemma c17_10 : (Nat.choose 17 10 : ℝ) = 19448 := by
  rw [Nat.cast_choose ℝ (by decide : 10 ≤ 17)]; norm_num
@[simp] lemma c17_11 : (Nat.choose 17 11 : ℝ) = 12376 := by
  rw [Nat.cast_choose ℝ (by decide : 11 ≤ 17)]; norm_num
@[simp] lemma c17_12 : (Nat.choose 17 12 : ℝ) = 6188 := by
  rw [Nat.cast_choose ℝ (by decide : 12 ≤ 17)]; norm_num
@[simp] lemma c17_13 : (Nat.choose 17 13 : ℝ) = 2380 := by
  rw [Nat.cast_choose ℝ (by decide : 13 ≤ 17)]; norm_num
@[simp] lemma c17_14 : (Nat.choose 17 14 : ℝ) = 680 := by
  rw [Nat.cast_choose ℝ (by decide : 14 ≤ 17)]; norm_num
@[simp] lemma c17_15 : (Nat.choose 17 15 : ℝ) = 136 := by
  rw [Nat.cast_choose ℝ (by decide : 15 ≤ 17)]; norm_num
@[simp] lemma c17_16 : (Nat.choose 17 16 : ℝ) = 17 := by
  rw [Nat.cast_choose ℝ (by decide : 16 ≤ 17)]; norm_num
@[simp] lemma c17_17 : (Nat.choose 17 17 : ℝ) = 1 := by
  rw [Nat.cast_choose ℝ (by decide : 17 ≤ 17)]; norm_num

/-! ## The `m`-summand and its pointwise closed-form decomposition -/

/-- The `m`-summand of the eight-core sum. -/
def Vm8 (m : ℕ) : ℝ :=
  (43046721 : ℝ) * (Nat.choose (m + 16) 16 : ℝ) *
    (∑ i ∈ Finset.range 18,
      ((-1 : ℝ) ^ i * (Nat.choose 17 i : ℝ)) *
        (264539520 / (xm m (9 + i) * xm m (12 + i) * xm m (15 + i) * xm m (18 + i) *
          xm m (21 + i) * xm m (24 + i) * xm m (27 + i) * xm m (30 + i) * xm m (33 + i))) ^ 2)

/-- Squared-term part of the closed-form decomposition. -/
def W18 (m : ℕ) : ℝ :=
    ((51274958 : ℝ) / 729) * (1 / (xm m 10)^2)
    +   ((-(251927080 : ℝ)) / 729) * (1 / (xm m 11)^2)
    +   ((1025499160 : ℝ) / 729) * (1 / (xm m 13)^2)
    +   ((1385598940 : ℝ) / 729) * (1 / (xm m 14)^2)
    +   ((-(11747748272 : ℝ)) / 243) * (1 / (xm m 16)^2)
    +   ((20038315990 : ℝ) / 243) * (1 / (xm m 17)^2)
    +   ((86584513288 : ℝ) / 729) * (1 / (xm m 19)^2)
    +   ((-(358320476360 : ℝ)) / 729) * (1 / (xm m 20)^2)
    +   ((639780131120 : ℝ) / 729) * (1 / (xm m 22)^2)
    +   ((41882053400 : ℝ) / 729) * (1 / (xm m 23)^2)
    +   ((-(311306814401 : ℝ)) / 81) * (1 / (xm m 25)^2)
    +   ((333070218481 : ℝ) / 81) * (1 / (xm m 26)^2)
    +   ((850373598800 : ℝ) / 243) * (1 / (xm m 28)^2)
    +   ((-(1981179805384 : ℝ)) / 243) * (1 / (xm m 29)^2)
    +   ((1190523038320 : ℝ) / 243) * (1 / (xm m 31)^2)
    +   ((633003394192 : ℝ) / 243) * (1 / (xm m 32)^2)
    +   ((-(863856505435 : ℝ)) / 81) * (1 / (xm m 34)^2)
    +   ((550946044688 : ℝ) / 81) * (1 / (xm m 35)^2)
    +   ((3648244560400 : ℝ) / 729) * (1 / (xm m 37)^2)
    +   ((-(4782661388960 : ℝ)) / 729) * (1 / (xm m 38)^2)
    +   ((1088073058520 : ℝ) / 729) * (1 / (xm m 40)^2)
    +   ((717155691980 : ℝ) / 729) * (1 / (xm m 41)^2)
    +   ((-(369073172200 : ℝ)) / 243) * (1 / (xm m 43)^2)
    +   ((178781559440 : ℝ) / 243) * (1 / (xm m 44)^2)
    +   ((102912212180 : ℝ) / 729) * (1 / (xm m 46)^2)
    +   ((-(119705913712 : ℝ)) / 729) * (1 / (xm m 47)^2)
    +   ((31144485265 : ℝ) / 729) * (1 / (xm m 49)^2)
    +   ((-(9133405754 : ℝ)) / 729) * (1 / (xm m 50)^2)

/-- Telescoping-pair part of the closed-form decomposition. -/
def W28 (m : ℕ) : ℝ :=
    ((4782969 : ℝ) / 560) * (1 / xm m 9 - 1 / xm m 12)
    +   ((-(3354168039797 : ℝ)) / 25019280) * (1 / xm m 10 - 1 / xm m 13)
    +   ((802066797977 : ℝ) / 3127410) * (1 / xm m 11 - 1 / xm m 14)
    +   ((8901105309 : ℝ) / 7280) * (1 / xm m 12 - 1 / xm m 15)
    +   ((-(32370577837619 : ℝ)) / 8339760) * (1 / xm m 13 - 1 / xm m 16)
    +   ((2469444645223 : ℝ) / 694980) * (1 / xm m 14 - 1 / xm m 17)
    +   ((-(136309833531 : ℝ)) / 7280) * (1 / xm m 15 - 1 / xm m 18)
    +   ((165752655015239 : ℝ) / 2779920) * (1 / xm m 16 - 1 / xm m 19)
    +   ((-(93326952415661 : ℝ)) / 4169880) * (1 / xm m 17 - 1 / xm m 20)
    +   ((-(7185640864491 : ℝ)) / 80080) * (1 / xm m 18 - 1 / xm m 21)
    +   ((855383417069287 : ℝ) / 25019280) * (1 / xm m 19 - 1 / xm m 22)
    +   ((-(2146715569158547 : ℝ)) / 12509640) * (1 / xm m 20 - 1 / xm m 23)
    +   ((79274444407173 : ℝ) / 80080) * (1 / xm m 21 - 1 / xm m 24)
    +   ((-(10163865131132851 : ℝ)) / 8339760) * (1 / xm m 22 - 1 / xm m 25)
    +   ((5119894340141599 : ℝ) / 9729720) * (1 / xm m 23 - 1 / xm m 26)
    +   ((-(21686282773047 : ℝ)) / 16016) * (1 / xm m 24 - 1 / xm m 27)
    +   ((2830627203036401 : ℝ) / 1389960) * (1 / xm m 25 - 1 / xm m 28)
    +   ((63604182470978257 : ℝ) / 58378320) * (1 / xm m 26 - 1 / xm m 29)
    +   ((-(252206467147683 : ℝ)) / 80080) * (1 / xm m 27 - 1 / xm m 30)
    +   ((6216573019597883 : ℝ) / 4169880) * (1 / xm m 28 - 1 / xm m 31)
    +   ((-(220552428259402807 : ℝ)) / 58378320) * (1 / xm m 29 - 1 / xm m 32)
    +   ((630853623072549 : ℝ) / 80080) * (1 / xm m 30 - 1 / xm m 33)
    +   ((-(3979252899375913 : ℝ)) / 833976) * (1 / xm m 31 - 1 / xm m 34)
    +   ((23180425052601203 : ℝ) / 19459440) * (1 / xm m 32 - 1 / xm m 35)
    +   ((-(11199785861493 : ℝ)) / 3640) * (1 / xm m 33 - 1 / xm m 36)
    +   ((4368554334908443 : ℝ) / 2779920) * (1 / xm m 34 - 1 / xm m 37)
    +   ((198777969169267921 : ℝ) / 58378320) * (1 / xm m 35 - 1 / xm m 38)
    +   ((-(12327399501057 : ℝ)) / 3640) * (1 / xm m 36 - 1 / xm m 39)
    +   ((35433594005659667 : ℝ) / 25019280) * (1 / xm m 37 - 1 / xm m 40)
    +   ((-(393850279549053757 : ℝ)) / 175134960) * (1 / xm m 38 - 1 / xm m 41)
    +   ((128389236867 : ℝ) / 56) * (1 / xm m 39 - 1 / xm m 42)
    +   ((-(4063357025722343 : ℝ)) / 8339760) * (1 / xm m 40 - 1 / xm m 43)
    +   ((-(445064479001173 : ℝ)) / 1769040) * (1 / xm m 41 - 1 / xm m 44)
    +   ((569173311 : ℝ) / 20) * (1 / xm m 42 - 1 / xm m 45)
    +   ((-(34041827709551 : ℝ)) / 252720) * (1 / xm m 43 - 1 / xm m 46)
    +   ((105776709633757 : ℝ) / 408240) * (1 / xm m 44 - 1 / xm m 47)
    +   ((-(243931419 : ℝ)) / 2) * (1 / xm m 45 - 1 / xm m 48)
    +   ((163397000158727 : ℝ) / 25019280) * (1 / xm m 46 - 1 / xm m 49)
    +   ((88723790914147 : ℝ) / 15921360) * (1 / xm m 47 - 1 / xm m 50)

/-- The closed-form decomposition of the summand (as `W18 + W28`). -/
def Vd8 (m : ℕ) : ℝ := W18 m + W28 m

set_option maxHeartbeats 0 in
lemma vm8_decomp (m : ℕ) : Vm8 m = Vd8 m := by
  unfold Vm8 Vd8 W18 W28
  rw [choose216]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero,
    c17_0, c17_1, c17_2, c17_3, c17_4, c17_5, c17_6, c17_7, c17_8, c17_9, c17_10, c17_11, c17_12, c17_13, c17_14, c17_15, c17_16, c17_17]
  norm_num
  simp_rw [xm_eq]
  norm_num
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
  have h45 : (3 * (m : ℝ) + 45) ≠ 0 := by positivity
  have h46 : (3 * (m : ℝ) + 46) ≠ 0 := by positivity
  have h47 : (3 * (m : ℝ) + 47) ≠ 0 := by positivity
  have h48 : (3 * (m : ℝ) + 48) ≠ 0 := by positivity
  have h49 : (3 * (m : ℝ) + 49) ≠ 0 := by positivity
  have h50 : (3 * (m : ℝ) + 50) ≠ 0 := by positivity
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
  field_simp
  ring

/-! ## The statement denominators equal the `xm` denominators -/

lemma denom_statement8 (m : ℕ) : ∀ i : ℕ,
    ((((3 * m + 9 + i : ℕ) : ℝ) * ((3 * m + 12 + i : ℕ) : ℝ) *
        ((3 * m + 15 + i : ℕ) : ℝ) * ((3 * m + 18 + i : ℕ) : ℝ) *
          ((3 * m + 21 + i : ℕ) : ℝ) * ((3 * m + 24 + i : ℕ) : ℝ) *
            ((3 * m + 27 + i : ℕ) : ℝ) * ((3 * m + 30 + i : ℕ) : ℝ) *
              ((3 * m + 33 + i : ℕ) : ℝ)))
      = xm m (9 + i) * xm m (12 + i) * xm m (15 + i) * xm m (18 + i) *
          xm m (21 + i) * xm m (24 + i) * xm m (27 + i) * xm m (30 + i) * xm m (33 + i) := by
  intro i
  have h1 : (((3 * m + 9 + i : ℕ) : ℝ)) = xm m (9 + i) := by
    unfold xm
    congr 1
    omega
  have h2 : (((3 * m + 12 + i : ℕ) : ℝ)) = xm m (12 + i) := by
    unfold xm
    congr 1
    omega
  have h3 : (((3 * m + 15 + i : ℕ) : ℝ)) = xm m (15 + i) := by
    unfold xm
    congr 1
    omega
  have h4 : (((3 * m + 18 + i : ℕ) : ℝ)) = xm m (18 + i) := by
    unfold xm
    congr 1
    omega
  have h5 : (((3 * m + 21 + i : ℕ) : ℝ)) = xm m (21 + i) := by
    unfold xm
    congr 1
    omega
  have h6 : (((3 * m + 24 + i : ℕ) : ℝ)) = xm m (24 + i) := by
    unfold xm
    congr 1
    omega
  have h7 : (((3 * m + 27 + i : ℕ) : ℝ)) = xm m (27 + i) := by
    unfold xm
    congr 1
    omega
  have h8 : (((3 * m + 30 + i : ℕ) : ℝ)) = xm m (30 + i) := by
    unfold xm
    congr 1
    omega
  have h9 : (((3 * m + 33 + i : ℕ) : ℝ)) = xm m (33 + i) := by
    unfold xm
    congr 1
    omega
  rw [h1, h2, h3, h4, h5, h6, h7, h8, h9]

/-- The inner `i`-sum in the statement's form equals the `xm` form. -/
lemma inner_sum_statement8 (m : ℕ) :
    (∑ i ∈ Finset.range 18,
      ((-1 : ℝ) ^ i * (Nat.choose 17 i : ℝ)) *
        (264539520 / ((((3 * m + 9 + i : ℕ) : ℝ) * ((3 * m + 12 + i : ℕ) : ℝ) *
          ((3 * m + 15 + i : ℕ) : ℝ) * ((3 * m + 18 + i : ℕ) : ℝ) *
            ((3 * m + 21 + i : ℕ) : ℝ) * ((3 * m + 24 + i : ℕ) : ℝ) *
              ((3 * m + 27 + i : ℕ) : ℝ) * ((3 * m + 30 + i : ℕ) : ℝ) *
                ((3 * m + 33 + i : ℕ) : ℝ)))) ^ 2)
    = (∑ i ∈ Finset.range 18,
      ((-1 : ℝ) ^ i * (Nat.choose 17 i : ℝ)) *
        (264539520 / (xm m (9 + i) * xm m (12 + i) * xm m (15 + i) * xm m (18 + i) *
          xm m (21 + i) * xm m (24 + i) * xm m (27 + i) * xm m (30 + i) * xm m (33 + i))) ^ 2) := by
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  rw [denom_statement8 m i]

/-- The `m`-summand of the eight-core sum, in the statement's form. -/
lemma vm8_eq_statement (m : ℕ) :
    (43046721 : ℝ) * (Nat.choose (m + 16) 16 : ℝ) *
      (∑ i ∈ Finset.range 18,
        ((-1 : ℝ) ^ i * (Nat.choose 17 i : ℝ)) *
          (264539520 / ((((3 * m + 9 + i : ℕ) : ℝ) * ((3 * m + 12 + i : ℕ) : ℝ) *
            ((3 * m + 15 + i : ℕ) : ℝ) * ((3 * m + 18 + i : ℕ) : ℝ) *
              ((3 * m + 21 + i : ℕ) : ℝ) * ((3 * m + 24 + i : ℕ) : ℝ) *
                ((3 * m + 27 + i : ℕ) : ℝ) * ((3 * m + 30 + i : ℕ) : ℝ) *
                  ((3 * m + 33 + i : ℕ) : ℝ)))) ^ 2) =
      Vm8 m := by
  unfold Vm8
  rw [inner_sum_statement8 m]

/-! ## Small partial sums needed for the shifts -/

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

/-! ## The values of the two pieces -/

/-- The value of the `W18`-sum. -/
noncomputable def V1val8 : ℝ :=
    ((51274958 : ℝ) / 729) * (A - Asum 3)
    +   ((-(251927080 : ℝ)) / 729) * (B - Bsum 3)
    +   ((1025499160 : ℝ) / 729) * (A - Asum 4)
    +   ((1385598940 : ℝ) / 729) * (B - Bsum 4)
    +   ((-(11747748272 : ℝ)) / 243) * (A - Asum 5)
    +   ((20038315990 : ℝ) / 243) * (B - Bsum 5)
    +   ((86584513288 : ℝ) / 729) * (A - Asum 6)
    +   ((-(358320476360 : ℝ)) / 729) * (B - Bsum 6)
    +   ((639780131120 : ℝ) / 729) * (A - Asum 7)
    +   ((41882053400 : ℝ) / 729) * (B - Bsum 7)
    +   ((-(311306814401 : ℝ)) / 81) * (A - Asum 8)
    +   ((333070218481 : ℝ) / 81) * (B - Bsum 8)
    +   ((850373598800 : ℝ) / 243) * (A - Asum 9)
    +   ((-(1981179805384 : ℝ)) / 243) * (B - Bsum 9)
    +   ((1190523038320 : ℝ) / 243) * (A - Asum 10)
    +   ((633003394192 : ℝ) / 243) * (B - Bsum 10)
    +   ((-(863856505435 : ℝ)) / 81) * (A - Asum 11)
    +   ((550946044688 : ℝ) / 81) * (B - Bsum 11)
    +   ((3648244560400 : ℝ) / 729) * (A - Asum 12)
    +   ((-(4782661388960 : ℝ)) / 729) * (B - Bsum 12)
    +   ((1088073058520 : ℝ) / 729) * (A - Asum 13)
    +   ((717155691980 : ℝ) / 729) * (B - Bsum 13)
    +   ((-(369073172200 : ℝ)) / 243) * (A - Asum 14)
    +   ((178781559440 : ℝ) / 243) * (B - Bsum 14)
    +   ((102912212180 : ℝ) / 729) * (A - Asum 15)
    +   ((-(119705913712 : ℝ)) / 729) * (B - Bsum 15)
    +   ((31144485265 : ℝ) / 729) * (A - Asum 16)
    +   ((-(9133405754 : ℝ)) / 729) * (B - Bsum 16)

/-- The value of the `W28`-sum. -/
noncomputable def V2val8 : ℝ :=
    ((4782969 : ℝ) / 560) * (1 / xm 0 9)
    +   ((-(3354168039797 : ℝ)) / 25019280) * (1 / xm 0 10)
    +   ((802066797977 : ℝ) / 3127410) * (1 / xm 0 11)
    +   ((8901105309 : ℝ) / 7280) * (1 / xm 0 12)
    +   ((-(32370577837619 : ℝ)) / 8339760) * (1 / xm 0 13)
    +   ((2469444645223 : ℝ) / 694980) * (1 / xm 0 14)
    +   ((-(136309833531 : ℝ)) / 7280) * (1 / xm 0 15)
    +   ((165752655015239 : ℝ) / 2779920) * (1 / xm 0 16)
    +   ((-(93326952415661 : ℝ)) / 4169880) * (1 / xm 0 17)
    +   ((-(7185640864491 : ℝ)) / 80080) * (1 / xm 0 18)
    +   ((855383417069287 : ℝ) / 25019280) * (1 / xm 0 19)
    +   ((-(2146715569158547 : ℝ)) / 12509640) * (1 / xm 0 20)
    +   ((79274444407173 : ℝ) / 80080) * (1 / xm 0 21)
    +   ((-(10163865131132851 : ℝ)) / 8339760) * (1 / xm 0 22)
    +   ((5119894340141599 : ℝ) / 9729720) * (1 / xm 0 23)
    +   ((-(21686282773047 : ℝ)) / 16016) * (1 / xm 0 24)
    +   ((2830627203036401 : ℝ) / 1389960) * (1 / xm 0 25)
    +   ((63604182470978257 : ℝ) / 58378320) * (1 / xm 0 26)
    +   ((-(252206467147683 : ℝ)) / 80080) * (1 / xm 0 27)
    +   ((6216573019597883 : ℝ) / 4169880) * (1 / xm 0 28)
    +   ((-(220552428259402807 : ℝ)) / 58378320) * (1 / xm 0 29)
    +   ((630853623072549 : ℝ) / 80080) * (1 / xm 0 30)
    +   ((-(3979252899375913 : ℝ)) / 833976) * (1 / xm 0 31)
    +   ((23180425052601203 : ℝ) / 19459440) * (1 / xm 0 32)
    +   ((-(11199785861493 : ℝ)) / 3640) * (1 / xm 0 33)
    +   ((4368554334908443 : ℝ) / 2779920) * (1 / xm 0 34)
    +   ((198777969169267921 : ℝ) / 58378320) * (1 / xm 0 35)
    +   ((-(12327399501057 : ℝ)) / 3640) * (1 / xm 0 36)
    +   ((35433594005659667 : ℝ) / 25019280) * (1 / xm 0 37)
    +   ((-(393850279549053757 : ℝ)) / 175134960) * (1 / xm 0 38)
    +   ((128389236867 : ℝ) / 56) * (1 / xm 0 39)
    +   ((-(4063357025722343 : ℝ)) / 8339760) * (1 / xm 0 40)
    +   ((-(445064479001173 : ℝ)) / 1769040) * (1 / xm 0 41)
    +   ((569173311 : ℝ) / 20) * (1 / xm 0 42)
    +   ((-(34041827709551 : ℝ)) / 252720) * (1 / xm 0 43)
    +   ((105776709633757 : ℝ) / 408240) * (1 / xm 0 44)
    +   ((-(243931419 : ℝ)) / 2) * (1 / xm 0 45)
    +   ((163397000158727 : ℝ) / 25019280) * (1 / xm 0 46)
    +   ((88723790914147 : ℝ) / 15921360) * (1 / xm 0 47)

/-- The value of the whole sum. -/
noncomputable def Vval8 : ℝ := V1val8 + V2val8

/-! ## `HasSum` of the two pieces of the decomposition -/

lemma hasSum_W18 : HasSum W18 V1val8 := by
  have h10 : HasSum (fun m : ℕ => ((51274958 : ℝ) / 729) * (1 / (xm m 10)^2))
      (((51274958 : ℝ) / 729) * (A - Asum 3)) := by
    simpa using (CdtTwoCore.hasSum_sq1 3).mul_left ((51274958 : ℝ) / 729)
  have h11 : HasSum (fun m : ℕ => ((-(251927080 : ℝ)) / 729) * (1 / (xm m 11)^2))
      (((-(251927080 : ℝ)) / 729) * (B - Bsum 3)) := by
    simpa using (CdtTwoCore.hasSum_sq2 3).mul_left ((-(251927080 : ℝ)) / 729)
  have h13 : HasSum (fun m : ℕ => ((1025499160 : ℝ) / 729) * (1 / (xm m 13)^2))
      (((1025499160 : ℝ) / 729) * (A - Asum 4)) := by
    simpa using (CdtTwoCore.hasSum_sq1 4).mul_left ((1025499160 : ℝ) / 729)
  have h14 : HasSum (fun m : ℕ => ((1385598940 : ℝ) / 729) * (1 / (xm m 14)^2))
      (((1385598940 : ℝ) / 729) * (B - Bsum 4)) := by
    simpa using (CdtTwoCore.hasSum_sq2 4).mul_left ((1385598940 : ℝ) / 729)
  have h16 : HasSum (fun m : ℕ => ((-(11747748272 : ℝ)) / 243) * (1 / (xm m 16)^2))
      (((-(11747748272 : ℝ)) / 243) * (A - Asum 5)) := by
    simpa using (CdtTwoCore.hasSum_sq1 5).mul_left ((-(11747748272 : ℝ)) / 243)
  have h17 : HasSum (fun m : ℕ => ((20038315990 : ℝ) / 243) * (1 / (xm m 17)^2))
      (((20038315990 : ℝ) / 243) * (B - Bsum 5)) := by
    simpa using (CdtTwoCore.hasSum_sq2 5).mul_left ((20038315990 : ℝ) / 243)
  have h19 : HasSum (fun m : ℕ => ((86584513288 : ℝ) / 729) * (1 / (xm m 19)^2))
      (((86584513288 : ℝ) / 729) * (A - Asum 6)) := by
    simpa using (CdtTwoCore.hasSum_sq1 6).mul_left ((86584513288 : ℝ) / 729)
  have h20 : HasSum (fun m : ℕ => ((-(358320476360 : ℝ)) / 729) * (1 / (xm m 20)^2))
      (((-(358320476360 : ℝ)) / 729) * (B - Bsum 6)) := by
    simpa using (CdtTwoCore.hasSum_sq2 6).mul_left ((-(358320476360 : ℝ)) / 729)
  have h22 : HasSum (fun m : ℕ => ((639780131120 : ℝ) / 729) * (1 / (xm m 22)^2))
      (((639780131120 : ℝ) / 729) * (A - Asum 7)) := by
    simpa using (CdtTwoCore.hasSum_sq1 7).mul_left ((639780131120 : ℝ) / 729)
  have h23 : HasSum (fun m : ℕ => ((41882053400 : ℝ) / 729) * (1 / (xm m 23)^2))
      (((41882053400 : ℝ) / 729) * (B - Bsum 7)) := by
    simpa using (CdtTwoCore.hasSum_sq2 7).mul_left ((41882053400 : ℝ) / 729)
  have h25 : HasSum (fun m : ℕ => ((-(311306814401 : ℝ)) / 81) * (1 / (xm m 25)^2))
      (((-(311306814401 : ℝ)) / 81) * (A - Asum 8)) := by
    simpa using (CdtTwoCore.hasSum_sq1 8).mul_left ((-(311306814401 : ℝ)) / 81)
  have h26 : HasSum (fun m : ℕ => ((333070218481 : ℝ) / 81) * (1 / (xm m 26)^2))
      (((333070218481 : ℝ) / 81) * (B - Bsum 8)) := by
    simpa using (CdtTwoCore.hasSum_sq2 8).mul_left ((333070218481 : ℝ) / 81)
  have h28 : HasSum (fun m : ℕ => ((850373598800 : ℝ) / 243) * (1 / (xm m 28)^2))
      (((850373598800 : ℝ) / 243) * (A - Asum 9)) := by
    simpa using (CdtTwoCore.hasSum_sq1 9).mul_left ((850373598800 : ℝ) / 243)
  have h29 : HasSum (fun m : ℕ => ((-(1981179805384 : ℝ)) / 243) * (1 / (xm m 29)^2))
      (((-(1981179805384 : ℝ)) / 243) * (B - Bsum 9)) := by
    simpa using (CdtTwoCore.hasSum_sq2 9).mul_left ((-(1981179805384 : ℝ)) / 243)
  have h31 : HasSum (fun m : ℕ => ((1190523038320 : ℝ) / 243) * (1 / (xm m 31)^2))
      (((1190523038320 : ℝ) / 243) * (A - Asum 10)) := by
    simpa using (CdtTwoCore.hasSum_sq1 10).mul_left ((1190523038320 : ℝ) / 243)
  have h32 : HasSum (fun m : ℕ => ((633003394192 : ℝ) / 243) * (1 / (xm m 32)^2))
      (((633003394192 : ℝ) / 243) * (B - Bsum 10)) := by
    simpa using (CdtTwoCore.hasSum_sq2 10).mul_left ((633003394192 : ℝ) / 243)
  have h34 : HasSum (fun m : ℕ => ((-(863856505435 : ℝ)) / 81) * (1 / (xm m 34)^2))
      (((-(863856505435 : ℝ)) / 81) * (A - Asum 11)) := by
    simpa using (CdtTwoCore.hasSum_sq1 11).mul_left ((-(863856505435 : ℝ)) / 81)
  have h35 : HasSum (fun m : ℕ => ((550946044688 : ℝ) / 81) * (1 / (xm m 35)^2))
      (((550946044688 : ℝ) / 81) * (B - Bsum 11)) := by
    simpa using (CdtTwoCore.hasSum_sq2 11).mul_left ((550946044688 : ℝ) / 81)
  have h37 : HasSum (fun m : ℕ => ((3648244560400 : ℝ) / 729) * (1 / (xm m 37)^2))
      (((3648244560400 : ℝ) / 729) * (A - Asum 12)) := by
    simpa using (CdtTwoCore.hasSum_sq1 12).mul_left ((3648244560400 : ℝ) / 729)
  have h38 : HasSum (fun m : ℕ => ((-(4782661388960 : ℝ)) / 729) * (1 / (xm m 38)^2))
      (((-(4782661388960 : ℝ)) / 729) * (B - Bsum 12)) := by
    simpa using (CdtTwoCore.hasSum_sq2 12).mul_left ((-(4782661388960 : ℝ)) / 729)
  have h40 : HasSum (fun m : ℕ => ((1088073058520 : ℝ) / 729) * (1 / (xm m 40)^2))
      (((1088073058520 : ℝ) / 729) * (A - Asum 13)) := by
    simpa using (CdtTwoCore.hasSum_sq1 13).mul_left ((1088073058520 : ℝ) / 729)
  have h41 : HasSum (fun m : ℕ => ((717155691980 : ℝ) / 729) * (1 / (xm m 41)^2))
      (((717155691980 : ℝ) / 729) * (B - Bsum 13)) := by
    simpa using (CdtTwoCore.hasSum_sq2 13).mul_left ((717155691980 : ℝ) / 729)
  have h43 : HasSum (fun m : ℕ => ((-(369073172200 : ℝ)) / 243) * (1 / (xm m 43)^2))
      (((-(369073172200 : ℝ)) / 243) * (A - Asum 14)) := by
    simpa using (CdtTwoCore.hasSum_sq1 14).mul_left ((-(369073172200 : ℝ)) / 243)
  have h44 : HasSum (fun m : ℕ => ((178781559440 : ℝ) / 243) * (1 / (xm m 44)^2))
      (((178781559440 : ℝ) / 243) * (B - Bsum 14)) := by
    simpa using (CdtTwoCore.hasSum_sq2 14).mul_left ((178781559440 : ℝ) / 243)
  have h46 : HasSum (fun m : ℕ => ((102912212180 : ℝ) / 729) * (1 / (xm m 46)^2))
      (((102912212180 : ℝ) / 729) * (A - Asum 15)) := by
    simpa using (CdtTwoCore.hasSum_sq1 15).mul_left ((102912212180 : ℝ) / 729)
  have h47 : HasSum (fun m : ℕ => ((-(119705913712 : ℝ)) / 729) * (1 / (xm m 47)^2))
      (((-(119705913712 : ℝ)) / 729) * (B - Bsum 15)) := by
    simpa using (CdtTwoCore.hasSum_sq2 15).mul_left ((-(119705913712 : ℝ)) / 729)
  have h49 : HasSum (fun m : ℕ => ((31144485265 : ℝ) / 729) * (1 / (xm m 49)^2))
      (((31144485265 : ℝ) / 729) * (A - Asum 16)) := by
    simpa using (CdtTwoCore.hasSum_sq1 16).mul_left ((31144485265 : ℝ) / 729)
  have h50 : HasSum (fun m : ℕ => ((-(9133405754 : ℝ)) / 729) * (1 / (xm m 50)^2))
      (((-(9133405754 : ℝ)) / 729) * (B - Bsum 16)) := by
    simpa using (CdtTwoCore.hasSum_sq2 16).mul_left ((-(9133405754 : ℝ)) / 729)
  exact (((((((((((((((((((((((((((h10.add h11).add h13).add h14).add h16).add h17).add h19).add h20).add h22).add h23).add h25).add h26).add h28).add h29).add h31).add h32).add h34).add h35).add h37).add h38).add h40).add h41).add h43).add h44).add h46).add h47).add h49).add h50)

lemma hasSum_W28 : HasSum W28 V2val8 := by
  have hp9 : HasSum (fun m : ℕ => ((4782969 : ℝ) / 560) * (1 / xm m 9 - 1 / xm m 12))
      (((4782969 : ℝ) / 560) * (1 / xm 0 9)) := by
    simpa using (CdtTwoCore.hasSum_pair 9 (by norm_num)).mul_left ((4782969 : ℝ) / 560)
  have hp10 : HasSum (fun m : ℕ => ((-(3354168039797 : ℝ)) / 25019280) * (1 / xm m 10 - 1 / xm m 13))
      (((-(3354168039797 : ℝ)) / 25019280) * (1 / xm 0 10)) := by
    simpa using (CdtTwoCore.hasSum_pair 10 (by norm_num)).mul_left ((-(3354168039797 : ℝ)) / 25019280)
  have hp11 : HasSum (fun m : ℕ => ((802066797977 : ℝ) / 3127410) * (1 / xm m 11 - 1 / xm m 14))
      (((802066797977 : ℝ) / 3127410) * (1 / xm 0 11)) := by
    simpa using (CdtTwoCore.hasSum_pair 11 (by norm_num)).mul_left ((802066797977 : ℝ) / 3127410)
  have hp12 : HasSum (fun m : ℕ => ((8901105309 : ℝ) / 7280) * (1 / xm m 12 - 1 / xm m 15))
      (((8901105309 : ℝ) / 7280) * (1 / xm 0 12)) := by
    simpa using (CdtTwoCore.hasSum_pair 12 (by norm_num)).mul_left ((8901105309 : ℝ) / 7280)
  have hp13 : HasSum (fun m : ℕ => ((-(32370577837619 : ℝ)) / 8339760) * (1 / xm m 13 - 1 / xm m 16))
      (((-(32370577837619 : ℝ)) / 8339760) * (1 / xm 0 13)) := by
    simpa using (CdtTwoCore.hasSum_pair 13 (by norm_num)).mul_left ((-(32370577837619 : ℝ)) / 8339760)
  have hp14 : HasSum (fun m : ℕ => ((2469444645223 : ℝ) / 694980) * (1 / xm m 14 - 1 / xm m 17))
      (((2469444645223 : ℝ) / 694980) * (1 / xm 0 14)) := by
    simpa using (CdtTwoCore.hasSum_pair 14 (by norm_num)).mul_left ((2469444645223 : ℝ) / 694980)
  have hp15 : HasSum (fun m : ℕ => ((-(136309833531 : ℝ)) / 7280) * (1 / xm m 15 - 1 / xm m 18))
      (((-(136309833531 : ℝ)) / 7280) * (1 / xm 0 15)) := by
    simpa using (CdtTwoCore.hasSum_pair 15 (by norm_num)).mul_left ((-(136309833531 : ℝ)) / 7280)
  have hp16 : HasSum (fun m : ℕ => ((165752655015239 : ℝ) / 2779920) * (1 / xm m 16 - 1 / xm m 19))
      (((165752655015239 : ℝ) / 2779920) * (1 / xm 0 16)) := by
    simpa using (CdtTwoCore.hasSum_pair 16 (by norm_num)).mul_left ((165752655015239 : ℝ) / 2779920)
  have hp17 : HasSum (fun m : ℕ => ((-(93326952415661 : ℝ)) / 4169880) * (1 / xm m 17 - 1 / xm m 20))
      (((-(93326952415661 : ℝ)) / 4169880) * (1 / xm 0 17)) := by
    simpa using (CdtTwoCore.hasSum_pair 17 (by norm_num)).mul_left ((-(93326952415661 : ℝ)) / 4169880)
  have hp18 : HasSum (fun m : ℕ => ((-(7185640864491 : ℝ)) / 80080) * (1 / xm m 18 - 1 / xm m 21))
      (((-(7185640864491 : ℝ)) / 80080) * (1 / xm 0 18)) := by
    simpa using (CdtTwoCore.hasSum_pair 18 (by norm_num)).mul_left ((-(7185640864491 : ℝ)) / 80080)
  have hp19 : HasSum (fun m : ℕ => ((855383417069287 : ℝ) / 25019280) * (1 / xm m 19 - 1 / xm m 22))
      (((855383417069287 : ℝ) / 25019280) * (1 / xm 0 19)) := by
    simpa using (CdtTwoCore.hasSum_pair 19 (by norm_num)).mul_left ((855383417069287 : ℝ) / 25019280)
  have hp20 : HasSum (fun m : ℕ => ((-(2146715569158547 : ℝ)) / 12509640) * (1 / xm m 20 - 1 / xm m 23))
      (((-(2146715569158547 : ℝ)) / 12509640) * (1 / xm 0 20)) := by
    simpa using (CdtTwoCore.hasSum_pair 20 (by norm_num)).mul_left ((-(2146715569158547 : ℝ)) / 12509640)
  have hp21 : HasSum (fun m : ℕ => ((79274444407173 : ℝ) / 80080) * (1 / xm m 21 - 1 / xm m 24))
      (((79274444407173 : ℝ) / 80080) * (1 / xm 0 21)) := by
    simpa using (CdtTwoCore.hasSum_pair 21 (by norm_num)).mul_left ((79274444407173 : ℝ) / 80080)
  have hp22 : HasSum (fun m : ℕ => ((-(10163865131132851 : ℝ)) / 8339760) * (1 / xm m 22 - 1 / xm m 25))
      (((-(10163865131132851 : ℝ)) / 8339760) * (1 / xm 0 22)) := by
    simpa using (CdtTwoCore.hasSum_pair 22 (by norm_num)).mul_left ((-(10163865131132851 : ℝ)) / 8339760)
  have hp23 : HasSum (fun m : ℕ => ((5119894340141599 : ℝ) / 9729720) * (1 / xm m 23 - 1 / xm m 26))
      (((5119894340141599 : ℝ) / 9729720) * (1 / xm 0 23)) := by
    simpa using (CdtTwoCore.hasSum_pair 23 (by norm_num)).mul_left ((5119894340141599 : ℝ) / 9729720)
  have hp24 : HasSum (fun m : ℕ => ((-(21686282773047 : ℝ)) / 16016) * (1 / xm m 24 - 1 / xm m 27))
      (((-(21686282773047 : ℝ)) / 16016) * (1 / xm 0 24)) := by
    simpa using (CdtTwoCore.hasSum_pair 24 (by norm_num)).mul_left ((-(21686282773047 : ℝ)) / 16016)
  have hp25 : HasSum (fun m : ℕ => ((2830627203036401 : ℝ) / 1389960) * (1 / xm m 25 - 1 / xm m 28))
      (((2830627203036401 : ℝ) / 1389960) * (1 / xm 0 25)) := by
    simpa using (CdtTwoCore.hasSum_pair 25 (by norm_num)).mul_left ((2830627203036401 : ℝ) / 1389960)
  have hp26 : HasSum (fun m : ℕ => ((63604182470978257 : ℝ) / 58378320) * (1 / xm m 26 - 1 / xm m 29))
      (((63604182470978257 : ℝ) / 58378320) * (1 / xm 0 26)) := by
    simpa using (CdtTwoCore.hasSum_pair 26 (by norm_num)).mul_left ((63604182470978257 : ℝ) / 58378320)
  have hp27 : HasSum (fun m : ℕ => ((-(252206467147683 : ℝ)) / 80080) * (1 / xm m 27 - 1 / xm m 30))
      (((-(252206467147683 : ℝ)) / 80080) * (1 / xm 0 27)) := by
    simpa using (CdtTwoCore.hasSum_pair 27 (by norm_num)).mul_left ((-(252206467147683 : ℝ)) / 80080)
  have hp28 : HasSum (fun m : ℕ => ((6216573019597883 : ℝ) / 4169880) * (1 / xm m 28 - 1 / xm m 31))
      (((6216573019597883 : ℝ) / 4169880) * (1 / xm 0 28)) := by
    simpa using (CdtTwoCore.hasSum_pair 28 (by norm_num)).mul_left ((6216573019597883 : ℝ) / 4169880)
  have hp29 : HasSum (fun m : ℕ => ((-(220552428259402807 : ℝ)) / 58378320) * (1 / xm m 29 - 1 / xm m 32))
      (((-(220552428259402807 : ℝ)) / 58378320) * (1 / xm 0 29)) := by
    simpa using (CdtTwoCore.hasSum_pair 29 (by norm_num)).mul_left ((-(220552428259402807 : ℝ)) / 58378320)
  have hp30 : HasSum (fun m : ℕ => ((630853623072549 : ℝ) / 80080) * (1 / xm m 30 - 1 / xm m 33))
      (((630853623072549 : ℝ) / 80080) * (1 / xm 0 30)) := by
    simpa using (CdtTwoCore.hasSum_pair 30 (by norm_num)).mul_left ((630853623072549 : ℝ) / 80080)
  have hp31 : HasSum (fun m : ℕ => ((-(3979252899375913 : ℝ)) / 833976) * (1 / xm m 31 - 1 / xm m 34))
      (((-(3979252899375913 : ℝ)) / 833976) * (1 / xm 0 31)) := by
    simpa using (CdtTwoCore.hasSum_pair 31 (by norm_num)).mul_left ((-(3979252899375913 : ℝ)) / 833976)
  have hp32 : HasSum (fun m : ℕ => ((23180425052601203 : ℝ) / 19459440) * (1 / xm m 32 - 1 / xm m 35))
      (((23180425052601203 : ℝ) / 19459440) * (1 / xm 0 32)) := by
    simpa using (CdtTwoCore.hasSum_pair 32 (by norm_num)).mul_left ((23180425052601203 : ℝ) / 19459440)
  have hp33 : HasSum (fun m : ℕ => ((-(11199785861493 : ℝ)) / 3640) * (1 / xm m 33 - 1 / xm m 36))
      (((-(11199785861493 : ℝ)) / 3640) * (1 / xm 0 33)) := by
    simpa using (CdtTwoCore.hasSum_pair 33 (by norm_num)).mul_left ((-(11199785861493 : ℝ)) / 3640)
  have hp34 : HasSum (fun m : ℕ => ((4368554334908443 : ℝ) / 2779920) * (1 / xm m 34 - 1 / xm m 37))
      (((4368554334908443 : ℝ) / 2779920) * (1 / xm 0 34)) := by
    simpa using (CdtTwoCore.hasSum_pair 34 (by norm_num)).mul_left ((4368554334908443 : ℝ) / 2779920)
  have hp35 : HasSum (fun m : ℕ => ((198777969169267921 : ℝ) / 58378320) * (1 / xm m 35 - 1 / xm m 38))
      (((198777969169267921 : ℝ) / 58378320) * (1 / xm 0 35)) := by
    simpa using (CdtTwoCore.hasSum_pair 35 (by norm_num)).mul_left ((198777969169267921 : ℝ) / 58378320)
  have hp36 : HasSum (fun m : ℕ => ((-(12327399501057 : ℝ)) / 3640) * (1 / xm m 36 - 1 / xm m 39))
      (((-(12327399501057 : ℝ)) / 3640) * (1 / xm 0 36)) := by
    simpa using (CdtTwoCore.hasSum_pair 36 (by norm_num)).mul_left ((-(12327399501057 : ℝ)) / 3640)
  have hp37 : HasSum (fun m : ℕ => ((35433594005659667 : ℝ) / 25019280) * (1 / xm m 37 - 1 / xm m 40))
      (((35433594005659667 : ℝ) / 25019280) * (1 / xm 0 37)) := by
    simpa using (CdtTwoCore.hasSum_pair 37 (by norm_num)).mul_left ((35433594005659667 : ℝ) / 25019280)
  have hp38 : HasSum (fun m : ℕ => ((-(393850279549053757 : ℝ)) / 175134960) * (1 / xm m 38 - 1 / xm m 41))
      (((-(393850279549053757 : ℝ)) / 175134960) * (1 / xm 0 38)) := by
    simpa using (CdtTwoCore.hasSum_pair 38 (by norm_num)).mul_left ((-(393850279549053757 : ℝ)) / 175134960)
  have hp39 : HasSum (fun m : ℕ => ((128389236867 : ℝ) / 56) * (1 / xm m 39 - 1 / xm m 42))
      (((128389236867 : ℝ) / 56) * (1 / xm 0 39)) := by
    simpa using (CdtTwoCore.hasSum_pair 39 (by norm_num)).mul_left ((128389236867 : ℝ) / 56)
  have hp40 : HasSum (fun m : ℕ => ((-(4063357025722343 : ℝ)) / 8339760) * (1 / xm m 40 - 1 / xm m 43))
      (((-(4063357025722343 : ℝ)) / 8339760) * (1 / xm 0 40)) := by
    simpa using (CdtTwoCore.hasSum_pair 40 (by norm_num)).mul_left ((-(4063357025722343 : ℝ)) / 8339760)
  have hp41 : HasSum (fun m : ℕ => ((-(445064479001173 : ℝ)) / 1769040) * (1 / xm m 41 - 1 / xm m 44))
      (((-(445064479001173 : ℝ)) / 1769040) * (1 / xm 0 41)) := by
    simpa using (CdtTwoCore.hasSum_pair 41 (by norm_num)).mul_left ((-(445064479001173 : ℝ)) / 1769040)
  have hp42 : HasSum (fun m : ℕ => ((569173311 : ℝ) / 20) * (1 / xm m 42 - 1 / xm m 45))
      (((569173311 : ℝ) / 20) * (1 / xm 0 42)) := by
    simpa using (CdtTwoCore.hasSum_pair 42 (by norm_num)).mul_left ((569173311 : ℝ) / 20)
  have hp43 : HasSum (fun m : ℕ => ((-(34041827709551 : ℝ)) / 252720) * (1 / xm m 43 - 1 / xm m 46))
      (((-(34041827709551 : ℝ)) / 252720) * (1 / xm 0 43)) := by
    simpa using (CdtTwoCore.hasSum_pair 43 (by norm_num)).mul_left ((-(34041827709551 : ℝ)) / 252720)
  have hp44 : HasSum (fun m : ℕ => ((105776709633757 : ℝ) / 408240) * (1 / xm m 44 - 1 / xm m 47))
      (((105776709633757 : ℝ) / 408240) * (1 / xm 0 44)) := by
    simpa using (CdtTwoCore.hasSum_pair 44 (by norm_num)).mul_left ((105776709633757 : ℝ) / 408240)
  have hp45 : HasSum (fun m : ℕ => ((-(243931419 : ℝ)) / 2) * (1 / xm m 45 - 1 / xm m 48))
      (((-(243931419 : ℝ)) / 2) * (1 / xm 0 45)) := by
    simpa using (CdtTwoCore.hasSum_pair 45 (by norm_num)).mul_left ((-(243931419 : ℝ)) / 2)
  have hp46 : HasSum (fun m : ℕ => ((163397000158727 : ℝ) / 25019280) * (1 / xm m 46 - 1 / xm m 49))
      (((163397000158727 : ℝ) / 25019280) * (1 / xm 0 46)) := by
    simpa using (CdtTwoCore.hasSum_pair 46 (by norm_num)).mul_left ((163397000158727 : ℝ) / 25019280)
  have hp47 : HasSum (fun m : ℕ => ((88723790914147 : ℝ) / 15921360) * (1 / xm m 47 - 1 / xm m 50))
      (((88723790914147 : ℝ) / 15921360) * (1 / xm 0 47)) := by
    simpa using (CdtTwoCore.hasSum_pair 47 (by norm_num)).mul_left ((88723790914147 : ℝ) / 15921360)
  exact ((((((((((((((((((((((((((((((((((((((hp9.add hp10).add hp11).add hp12).add hp13).add hp14).add hp15).add hp16).add hp17).add hp18).add hp19).add hp20).add hp21).add hp22).add hp23).add hp24).add hp25).add hp26).add hp27).add hp28).add hp29).add hp30).add hp31).add hp32).add hp33).add hp34).add hp35).add hp36).add hp37).add hp38).add hp39).add hp40).add hp41).add hp42).add hp43).add hp44).add hp45).add hp46).add hp47)

/-- `HasSum` for the whole summand. -/
lemma hasSum_Vm8 : HasSum Vm8 Vval8 := by
  have hsum : HasSum (fun m : ℕ => W18 m + W28 m) Vval8 := by
    simpa [Vval8] using hasSum_W18.add hasSum_W28
  apply HasSum.congr_fun hsum
  intro m
  exact vm8_decomp m

set_option maxHeartbeats 0 in
/-- The infinite sum of `Vm8` in closed form. -/
lemma tsum_Vm8 : (∑' m : ℕ, Vm8 m) = 2157759 * A - 2157759 * B - 66085799967 / 39200 := by
  have hval : Vval8 = 2157759 * A - 2157759 * B - 66085799967 / 39200 := by
    unfold Vval8 V1val8 V2val8
    norm_num [xm]
    ring
  rw [hasSum_Vm8.tsum_eq]
  exact hval

end CdtEightCore
open CdtEightCore

/-! ## Final assembly -/

/-- Creative-telescoping evaluation of the degree-8 `(Cintegral)` inner sum:
`Σₘ 43046721·C(m+16,16)·Σᵢ₌₀¹⁷(−1)ⁱC(17,i)·(264539520/∏_{k=0}^{8}(3m+9+3k+i))²
 = 2157759·Σₖ(1/(3k+1)²−1/(3k+2)²) − 66085799967/39200`. -/
theorem sum_cintegralEight_core :
    (∑' m : ℕ,
        (43046721 : ℝ) * (Nat.choose (m + 16) 16 : ℝ) *
          (∑ i ∈ Finset.range 18,
            ((-1 : ℝ) ^ i * (Nat.choose 17 i : ℝ)) *
              (264539520 / ((((3 * m + 9 + i : ℕ) : ℝ) * ((3 * m + 12 + i : ℕ) : ℝ) * ((3 * m + 15 + i : ℕ) : ℝ) * ((3 * m + 18 + i : ℕ) : ℝ) * ((3 * m + 21 + i : ℕ) : ℝ) * ((3 * m + 24 + i : ℕ) : ℝ) * ((3 * m + 27 + i : ℕ) : ℝ) * ((3 * m + 30 + i : ℕ) : ℝ) * ((3 * m + 33 + i : ℕ) : ℝ)))) ^ 2)) =
      2157759 * (∑' k : ℕ,
          ((1 : ℝ) / (((3 * k + 1 : ℕ) : ℝ) ^ 2) - (1 : ℝ) / (((3 * k + 2 : ℕ) : ℝ) ^ 2))) - 66085799967 / 39200 := by
  have hMain := tsum_Vm8
  have hL : (∑' m : ℕ, Vm8 m) =
      (∑' m : ℕ,
        (43046721 : ℝ) * (Nat.choose (m + 16) 16 : ℝ) *
          (∑ i ∈ Finset.range 18,
            ((-1 : ℝ) ^ i * (Nat.choose 17 i : ℝ)) *
              (264539520 / ((((3 * m + 9 + i : ℕ) : ℝ) * ((3 * m + 12 + i : ℕ) : ℝ) *
                ((3 * m + 15 + i : ℕ) : ℝ) * ((3 * m + 18 + i : ℕ) : ℝ) *
                  ((3 * m + 21 + i : ℕ) : ℝ) * ((3 * m + 24 + i : ℕ) : ℝ) *
                    ((3 * m + 27 + i : ℕ) : ℝ) * ((3 * m + 30 + i : ℕ) : ℝ) *
                      ((3 * m + 33 + i : ℕ) : ℝ)))) ^ 2)) := by
    apply tsum_congr
    intro m
    exact (vm8_eq_statement m).symm
  rw [← hL]
  rw [hMain]
  have hR : (∑' k : ℕ,
      ((1 : ℝ) / (((3 * k + 1 : ℕ) : ℝ) ^ 2) - (1 : ℝ) / (((3 * k + 2 : ℕ) : ℝ) ^ 2))) = A - B := by
    simpa [Rk, f1, f2, xm] using tsum_Rk
  rw [hR]
  ring

end Commons.Analysis.Summation
