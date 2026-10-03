/-
# Area 4 (round 6): absorption of the crude §15 pieces into the round-6 bracket

The round-6 §15 reduction `Work.FIArea4.A6R2.ExpBound6` must pay for the four crude pieces

  `16·Y`,  `256·N·X^{-1/2}`,  `64·Y^{1/3}N^{2/3}(log N+1)^4`,  `64·(log₂(4Y)+1)·N^{23/24+1/4000}`

(with `Y = S15Y Pa X j = ⌈N/(X·2^j)⌉ + 1`) out of the Proposition-14.1 bracket
`(log N+1)^4 · S15Br6 Pa X`, where `S15Br6 = X^{-1/2}N + X^{-1/3}N + N^{23/24+1/1000}`.  This is
what `absorb6` states: the *whole* crude bracket is `≤ C·(log N+1)^4·S15Br6·A` for a constant `C`
depending only on `Cp`.

The mathematics is elementary term by term.

* `16·Y ≤ 16·(N/X + 2) ≤ 48·B`, since `N/X ≤ X^{-1/2}N ≤ B` and `1 ≤ B` (so `2 ≤ 2B`).
* `256·N·X^{-1/2} ≤ 256·B`, the first summand of `B`.
* `Y^{1/3}N^{2/3} ≤ ((N/X)^{1/3} + 2^{1/3})N^{2/3} ≤ X^{-1/3}N + 2N^{2/3} ≤ 3B`: the first piece is
  the *middle* summand `X^{-1/3}N = N^{1/3}X^{-1/3}N^{2/3}` of `B`, the second is below
  `N^{23/24+1/1000} ≤ B` because `N ≥ 1`.
* `log₂(4Y)+1 ≪ log N + 1`, and `N^{23/24+1/4000} ≤ N^{23/24+1/1000} ≤ B` because `1/4000 ≤ 1/1000`:
  here `4Y ≤ 12N` (from `Y ≤ N/X + 2 ≤ N + 2 ≤ 3N`), so `2^{log₂(4Y)} ≤ 4Y ≤ 12N` and
  `log₂(4Y)·log 2 ≤ log 12 + log N ≤ 11 + log N`.

The constant is thus uniform in `Pa`; the existential `x0` is `0`.
-/
import Mathlib
import Submission.Work.FIArea4.A6R2.Defs

namespace Work.FIArea4.A6R2

open Finset
open scoped BigOperators

noncomputable section

set_option maxHeartbeats 1000000

/-! ## 1. The round-6 bracket and its summands -/

/-- The first summand `X^{-1/2}N` of `S15Br6` is dominated by the bracket. -/
lemma S15Br6_ge_first (Pa : Work.FITop.Params) (X : ℕ) :
    (X:ℝ)^(-(1:ℝ)/2) * Pa.N ≤ S15Br6 Pa X := by
  unfold S15Br6
  have hN0 : (0:ℝ) ≤ Pa.N := by linarith [Pa.hN1]
  have hX0 : (0:ℝ) ≤ (X:ℝ) := Nat.cast_nonneg X
  have h2 : (0:ℝ) ≤ Pa.N ^ ((1:ℝ)/3) * (X:ℝ)^(-(1:ℝ)/3) * Pa.N^((2:ℝ)/3) :=
    mul_nonneg (mul_nonneg (Real.rpow_nonneg hN0 _) (Real.rpow_nonneg hX0 _)) (Real.rpow_nonneg hN0 _)
  have h3 : (0:ℝ) ≤ Pa.N ^ ((23:ℝ)/24 + (1:ℝ)/1000) := Real.rpow_nonneg hN0 _
  linarith

/-- The last summand `N^{23/24+1/1000}` of `S15Br6` is dominated by the bracket. -/
lemma S15Br6_ge_last (Pa : Work.FITop.Params) (X : ℕ) :
    Pa.N ^ ((23:ℝ)/24 + (1:ℝ)/1000) ≤ S15Br6 Pa X := by
  unfold S15Br6
  have hN0 : (0:ℝ) ≤ Pa.N := by linarith [Pa.hN1]
  have hX0 : (0:ℝ) ≤ (X:ℝ) := Nat.cast_nonneg X
  have h1 : (0:ℝ) ≤ (X:ℝ)^(-(1:ℝ)/2) * Pa.N := mul_nonneg (Real.rpow_nonneg hX0 _) hN0
  have h2 : (0:ℝ) ≤ Pa.N ^ ((1:ℝ)/3) * (X:ℝ)^(-(1:ℝ)/3) * Pa.N^((2:ℝ)/3) :=
    mul_nonneg (mul_nonneg (Real.rpow_nonneg hN0 _) (Real.rpow_nonneg hX0 _)) (Real.rpow_nonneg hN0 _)
  linarith

/-- `1 ≤ S15Br6 Pa X`: the last summand is `≥ 1` because `N ≥ 1` and the exponent is `≥ 0`. -/
lemma S15Br6_ge_one (Pa : Work.FITop.Params) (X : ℕ) : 1 ≤ S15Br6 Pa X := by
  have hN1 : (1:ℝ) ≤ Pa.N := Pa.hN1
  have h : (1:ℝ) ≤ Pa.N ^ ((23:ℝ)/24 + (1:ℝ)/1000) := Real.one_le_rpow hN1 (by norm_num)
  linarith [S15Br6_ge_last Pa X]

/-- The **middle** summand `X^{-1/3}N = N^{1/3}X^{-1/3}N^{2/3}` of `S15Br6`. -/
lemma S15Br6_ge_mid (Pa : Work.FITop.Params) (X : ℕ) :
    (X:ℝ)^(-(1:ℝ)/3) * Pa.N ≤ S15Br6 Pa X := by
  have hN0 : (0:ℝ) < Pa.N := by linarith [Pa.hN1]
  have hX0 : (0:ℝ) ≤ (X:ℝ) := Nat.cast_nonneg X
  have h1 : (0:ℝ) ≤ (X:ℝ)^(-(1:ℝ)/2) * Pa.N := mul_nonneg (Real.rpow_nonneg hX0 _) hN0.le
  have h3 : (0:ℝ) ≤ Pa.N ^ ((23:ℝ)/24 + (1:ℝ)/1000) := Real.rpow_nonneg hN0.le _
  have heq : Pa.N ^ ((1:ℝ)/3) * (X:ℝ)^(-(1:ℝ)/3) * Pa.N^((2:ℝ)/3)
      = (X:ℝ)^(-(1:ℝ)/3) * Pa.N := by
    rw [show Pa.N ^ ((1:ℝ)/3) * (X:ℝ)^(-(1:ℝ)/3) * Pa.N^((2:ℝ)/3)
        = (X:ℝ)^(-(1:ℝ)/3) * (Pa.N ^ ((1:ℝ)/3) * Pa.N ^ ((2:ℝ)/3)) by ring]
    rw [← Real.rpow_add hN0, show (1:ℝ)/3 + (2:ℝ)/3 = 1 by norm_num, Real.rpow_one]
  rw [← heq]
  unfold S15Br6
  linarith

/-- `N^{2/3} ≤ S15Br6 Pa X`: `2/3 ≤ 23/24 + 1/1000` and `N ≥ 1`. -/
lemma S15Br6_ge_two_thirds (Pa : Work.FITop.Params) (X : ℕ) :
    Pa.N ^ ((2:ℝ)/3) ≤ S15Br6 Pa X := by
  have hN1 : (1:ℝ) ≤ Pa.N := Pa.hN1
  exact le_trans (Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num)) (S15Br6_ge_last Pa X)

/-- `N^{23/24+1/4000} ≤ S15Br6 Pa X`: the exponent is below the bracket's `23/24 + 1/1000`. -/
lemma S15Br6_ge_c4000 (Pa : Work.FITop.Params) (X : ℕ) :
    Pa.N ^ ((23:ℝ)/24 + (1:ℝ)/4000) ≤ S15Br6 Pa X := by
  have hN1 : (1:ℝ) ≤ Pa.N := Pa.hN1
  exact le_trans (Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num)) (S15Br6_ge_last Pa X)

/-- `N/X ≤ S15Br6 Pa X` for `1 ≤ X` (`N/X ≤ X^{-1/2}N`, since `1/X ≤ X^{-1/2}`). -/
lemma S15Br6_ge_divX (Pa : Work.FITop.Params) (X : ℕ) (hX : 1 ≤ X) :
    Pa.N / (X:ℝ) ≤ S15Br6 Pa X := by
  have hX1 : (1:ℝ) ≤ (X:ℝ) := by exact_mod_cast hX
  have hX0 : (0:ℝ) < (X:ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hX)
  have hN0 : (0:ℝ) ≤ Pa.N := by linarith [Pa.hN1]
  have hinv : (X:ℝ)⁻¹ ≤ (X:ℝ)^(-(1:ℝ)/2) := by
    have h1 : (X:ℝ)^(-1:ℝ) ≤ (X:ℝ)^(-(1:ℝ)/2) :=
      Real.rpow_le_rpow_of_exponent_le hX1 (by norm_num)
    rwa [Real.rpow_neg_one] at h1
  calc Pa.N / (X:ℝ) = Pa.N * (X:ℝ)⁻¹ := by rw [div_eq_mul_inv]
    _ ≤ Pa.N * (X:ℝ)^(-(1:ℝ)/2) := mul_le_mul_of_nonneg_left hinv hN0
    _ = (X:ℝ)^(-(1:ℝ)/2) * Pa.N := by ring
    _ ≤ S15Br6 Pa X := S15Br6_ge_first Pa X

/-- `(N/X)^{1/3}N^{2/3} ≤ S15Br6 Pa X`: this collapses to the middle summand `X^{-1/3}N`. -/
lemma S15Br6_ge_dividethird (Pa : Work.FITop.Params) (X : ℕ) (hX : 1 ≤ X) :
    (Pa.N / (X:ℝ)) ^ ((1:ℝ)/3) * Pa.N ^ ((2:ℝ)/3) ≤ S15Br6 Pa X := by
  have hX0 : (0:ℝ) < (X:ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hX)
  have hN0 : (0:ℝ) < Pa.N := by linarith [Pa.hN1]
  rw [Real.div_rpow hN0.le hX0.le]
  have heq : Pa.N ^ ((1:ℝ)/3) / (X:ℝ)^((1:ℝ)/3) * Pa.N ^ ((2:ℝ)/3)
      = (X:ℝ)^(-(1:ℝ)/3) * Pa.N := by
    rw [div_eq_mul_inv, ← Real.rpow_neg hX0.le]
    rw [show (X:ℝ) ^ (-((1:ℝ)/3)) = (X:ℝ) ^ (-(1:ℝ)/3) by norm_num]
    rw [show Pa.N ^ ((1:ℝ)/3) * (X:ℝ) ^ (-(1:ℝ)/3) * Pa.N ^ ((2:ℝ)/3)
        = (X:ℝ) ^ (-(1:ℝ)/3) * (Pa.N ^ ((1:ℝ)/3) * Pa.N ^ ((2:ℝ)/3)) by ring]
    rw [← Real.rpow_add hN0, show (1:ℝ)/3 + (2:ℝ)/3 = 1 by norm_num, Real.rpow_one]
  rw [heq]
  exact S15Br6_ge_mid Pa X

/-! ## 2. The size `Y = S15Y Pa X j` and the logarithm -/

/-- `S15Y Pa X j = ⌈N/(X·2^j)⌉ + 1 ≤ N/X + 2`. -/
lemma S15Y_cast_le_add_two (Pa : Work.FITop.Params) (X j : ℕ) (hX : 1 ≤ X) :
    (S15Y Pa X j : ℝ) ≤ Pa.N / (X : ℝ) + 2 := by
  have hX0 : (0 : ℝ) < (X : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hX)
  have h2j : (1 : ℝ) ≤ (2 : ℝ) ^ j := one_le_pow₀ (by norm_num)
  have hden : (0 : ℝ) < (X : ℝ) * (2 : ℝ) ^ j := mul_pos hX0 (pow_pos (by norm_num) j)
  have hceil := Nat.ceil_lt_add_one
    (show (0 : ℝ) ≤ Pa.N / ((X : ℝ) * (2 : ℝ) ^ j) from
      le_of_lt (div_pos (by linarith [Pa.hN1]) hden))
  have hY : (S15Y Pa X j : ℝ) = ((⌈Pa.N / ((X : ℝ) * (2 : ℝ) ^ j)⌉₊ : ℕ) : ℝ) + 1 := by
    unfold S15Y; push_cast; ring
  rw [hY]
  have h1 : ((⌈Pa.N / ((X : ℝ) * (2 : ℝ) ^ j)⌉₊ : ℕ) : ℝ)
      < Pa.N / ((X : ℝ) * (2 : ℝ) ^ j) + 1 := hceil
  have hle : Pa.N / ((X : ℝ) * (2 : ℝ) ^ j) ≤ Pa.N / (X : ℝ) := by
    apply div_le_div_of_nonneg_left (by linarith [Pa.hN1]) hX0
    nlinarith [h2j]
  linarith

/-- `1 ≤ S15Y Pa X j`. -/
lemma S15Y_ge_one (Pa : Work.FITop.Params) (X j : ℕ) : 1 ≤ S15Y Pa X j := by
  unfold S15Y; omega

/-- `log₂ n = Nat.log 2 n ≤ 2 log n` for `n ≥ 1` (`2^{log₂ n} ≤ n` and `log 2 ≥ 1/2`). -/
lemma natLog_two_le_log (n : ℕ) (hn : 1 ≤ n) :
    ((Nat.log 2 n : ℕ) : ℝ) ≤ 2 * Real.log (n : ℝ) := by
  have hn0 : n ≠ 0 := by omega
  have hle : 2 ^ Nat.log 2 n ≤ n := Nat.pow_log_le_self 2 hn0
  have hle' : (2:ℝ) ^ (Nat.log 2 n) ≤ (n:ℝ) := by exact_mod_cast hle
  have hpos : (0:ℝ) < (2:ℝ) ^ Nat.log 2 n := by positivity
  have hlog := Real.log_le_log hpos hle'
  rw [Real.log_pow] at hlog
  have hlog2 : (1/2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hk : (0:ℝ) ≤ (Nat.log 2 n : ℝ) := Nat.cast_nonneg _
  nlinarith [hlog, hlog2, hk]

/-! ## 3. The absorption -/

theorem absorb6 (Cp : ℝ) (hCp : 0 < Cp) :
    ∃ C x0 : ℝ, 0 < C ∧ ∀ (Pa : Work.FITop.Params), x0 ≤ (Pa.x : ℝ) →
    ∀ (X j : ℕ) (A : ℝ), 0 ≤ A → 1 ≤ X →
      (16 * Cp) * (16 * (Work.FIArea4.S15Y Pa X j : ℝ)
         + 256 * Pa.N * (X : ℝ) ^ (-(1 : ℝ) / 2)
         + 64 * (((Work.FIArea4.S15Y Pa X j : ℝ)) ^ ((1 : ℝ) / 3)) * Pa.N ^ ((2 : ℝ) / 3)
             * (Real.log Pa.N + 1) ^ (4 : ℕ)
         + 64 * ((Nat.log 2 (4 * Work.FIArea4.S15Y Pa X j) + 1 : ℕ) : ℝ)
             * Pa.N ^ ((23 : ℝ) / 24 + (1 : ℝ) / 4000)) * A
        ≤ C * (Real.log Pa.N + 1) ^ (4 : ℕ) * Work.FIArea4.S15Br6 Pa X * A := by
  refine ⟨31488 * Cp, 0, by nlinarith [hCp], ?_⟩
  intro Pa hx X j A hA hX
  have hN1 : (1:ℝ) ≤ Pa.N := Pa.hN1
  have hN0 : (0:ℝ) < Pa.N := lt_of_lt_of_le one_pos hN1
  have hX0 : (0:ℝ) ≤ (X:ℝ) := Nat.cast_nonneg X
  have hX1 : (1:ℝ) ≤ (X:ℝ) := by exact_mod_cast hX
  have hXpos : (0:ℝ) < (X:ℝ) := lt_of_lt_of_le one_pos hX1
  have hlogN0 : (0:ℝ) ≤ Real.log Pa.N := Real.log_nonneg hN1
  -- the two abbreviations `L = log N + 1` and `B = S15Br6 Pa X` of the target
  set L : ℝ := Real.log Pa.N + 1 with hL
  have hL1 : (1:ℝ) ≤ L := by rw [hL]; linarith
  have hL0 : (0:ℝ) ≤ L := le_trans zero_le_one hL1
  have hL41 : (1:ℝ) ≤ L^4 := one_le_pow₀ hL1
  have hL4nn : (0:ℝ) ≤ L^4 := pow_nonneg hL0 4
  set B : ℝ := S15Br6 Pa X with hB
  have hB1 : (1:ℝ) ≤ B := by rw [hB]; exact S15Br6_ge_one Pa X
  have hB0 : (0:ℝ) ≤ B := le_trans zero_le_one hB1
  have hYb : (S15Y Pa X j : ℝ) ≤ Pa.N / (X:ℝ) + 2 := S15Y_cast_le_add_two Pa X j hX
  have hdX : Pa.N / (X:ℝ) ≤ B := by rw [hB]; exact S15Br6_ge_divX Pa X hX
  -- ### the four pieces, each `≤` its share of `L^4·B`
  have hT1 : 16 * (S15Y Pa X j : ℝ) ≤ 48 * L^4 * B := by
    have h1 : 16 * (S15Y Pa X j : ℝ) ≤ 48 * B := by linarith [hYb, hdX, hB1]
    have h3 : (48:ℝ) ≤ 48 * L^4 := by nlinarith [hL41]
    have h2 : (48:ℝ) * B ≤ 48 * L^4 * B := mul_le_mul_of_nonneg_right h3 hB0
    linarith
  have hT2 : 256 * Pa.N * (X:ℝ)^(-(1:ℝ)/2) ≤ 256 * L^4 * B := by
    have hf : (X:ℝ)^(-(1:ℝ)/2) * Pa.N ≤ B := by rw [hB]; exact S15Br6_ge_first Pa X
    have h1 : 256 * Pa.N * (X:ℝ)^(-(1:ℝ)/2) ≤ 256 * B := by
      calc 256 * Pa.N * (X:ℝ)^(-(1:ℝ)/2) = 256 * ((X:ℝ)^(-(1:ℝ)/2) * Pa.N) := by ring
        _ ≤ 256 * B := mul_le_mul_of_nonneg_left hf (by norm_num)
    have h3 : (256:ℝ) ≤ 256 * L^4 := by nlinarith [hL41]
    have h2 : (256:ℝ) * B ≤ 256 * L^4 * B := mul_le_mul_of_nonneg_right h3 hB0
    linarith
  have hT3 : 64 * ((S15Y Pa X j : ℝ)^((1:ℝ)/3)) * Pa.N^((2:ℝ)/3) * L^4 ≤ 192 * L^4 * B := by
    have hsub : (Pa.N/(X:ℝ) + 2)^((1:ℝ)/3) ≤ (Pa.N/(X:ℝ))^((1:ℝ)/3) + 2^((1:ℝ)/3) :=
      Real.rpow_add_le_add_rpow (div_nonneg hN0.le hX0) (by norm_num) (by norm_num) (by norm_num)
    have h1 : (S15Y Pa X j : ℝ)^((1:ℝ)/3) ≤ (Pa.N/(X:ℝ) + 2)^((1:ℝ)/3) :=
      Real.rpow_le_rpow (by positivity) hYb (by norm_num)
    have h2 : (2:ℝ)^((1:ℝ)/3) ≤ 2 := by
      have := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2)
        (by norm_num : (1:ℝ)/3 ≤ 1)
      simpa using this
    have hYpow : (S15Y Pa X j : ℝ)^((1:ℝ)/3) ≤ (Pa.N/(X:ℝ))^((1:ℝ)/3) + 2 := by linarith
    have hN23 : (0:ℝ) ≤ Pa.N^((2:ℝ)/3) := Real.rpow_nonneg hN0.le _
    have hsplit : ((Pa.N/(X:ℝ))^((1:ℝ)/3) + 2) * Pa.N^((2:ℝ)/3)
        = (Pa.N/(X:ℝ))^((1:ℝ)/3) * Pa.N^((2:ℝ)/3) + 2 * Pa.N^((2:ℝ)/3) := by ring
    have hstep : (S15Y Pa X j : ℝ)^((1:ℝ)/3) * Pa.N^((2:ℝ)/3)
        ≤ (Pa.N/(X:ℝ))^((1:ℝ)/3) * Pa.N^((2:ℝ)/3) + 2 * Pa.N^((2:ℝ)/3) := by
      have h := mul_le_mul_of_nonneg_right hYpow hN23
      rwa [hsplit] at h
    have hA : (Pa.N/(X:ℝ))^((1:ℝ)/3) * Pa.N^((2:ℝ)/3) ≤ B := by
      rw [hB]; exact S15Br6_ge_dividethird Pa X hX
    have hB2 : (2:ℝ) * Pa.N^((2:ℝ)/3) ≤ 2 * B := by
      have h := S15Br6_ge_two_thirds Pa X
      rw [hB]; linarith
    have h3B : (S15Y Pa X j : ℝ)^((1:ℝ)/3) * Pa.N^((2:ℝ)/3) ≤ 3 * B := by linarith
    have hfin : 64 * ((S15Y Pa X j : ℝ)^((1:ℝ)/3)) * Pa.N^((2:ℝ)/3) ≤ 192 * B := by
      calc 64 * ((S15Y Pa X j : ℝ)^((1:ℝ)/3)) * Pa.N^((2:ℝ)/3)
          = 64 * ((S15Y Pa X j : ℝ)^((1:ℝ)/3) * Pa.N^((2:ℝ)/3)) := by ring
        _ ≤ 64 * (3 * B) := mul_le_mul_of_nonneg_left h3B (by norm_num)
        _ = 192 * B := by ring
    calc 64 * ((S15Y Pa X j : ℝ)^((1:ℝ)/3)) * Pa.N^((2:ℝ)/3) * L^4
        = (64 * ((S15Y Pa X j : ℝ)^((1:ℝ)/3)) * Pa.N^((2:ℝ)/3)) * L^4 := by ring
      _ ≤ (192 * B) * L^4 := mul_le_mul_of_nonneg_right hfin hL4nn
      _ = 192 * L^4 * B := by ring
  -- the logarithm comparison `log₂(4Y) + 1 ≤ 23(log N+1)`
  have hk : ((Nat.log 2 (4 * S15Y Pa X j) + 1 : ℕ) : ℝ) ≤ 23 * L := by
    have hY1 : (S15Y Pa X j : ℝ) ≤ Pa.N + 2 := by
      have hdivN : Pa.N/(X:ℝ) ≤ Pa.N := by rw [div_le_iff₀ hXpos]; nlinarith [hN1]
      linarith
    have h4Y : ((4 * S15Y Pa X j : ℕ) : ℝ) ≤ 12 * Pa.N := by
      push_cast
      nlinarith [hY1, hN1]
    have hpow : 2 ^ Nat.log 2 (4 * S15Y Pa X j) ≤ 4 * S15Y Pa X j :=
      Nat.pow_log_le_self 2 (by have := S15Y_ge_one Pa X j; omega)
    have hpow' : (2:ℝ) ^ Nat.log 2 (4 * S15Y Pa X j) ≤ 12 * Pa.N := by
      have hcast : (2:ℝ) ^ Nat.log 2 (4 * S15Y Pa X j) ≤ ((4 * S15Y Pa X j : ℕ) : ℝ) := by
        exact_mod_cast hpow
      linarith
    have hlog := Real.log_le_log
      (by positivity : (0:ℝ) < (2:ℝ)^Nat.log 2 (4 * S15Y Pa X j)) hpow'
    rw [Real.log_pow, Real.log_mul (by norm_num) (ne_of_gt hN0)] at hlog
    have hlog12 : Real.log 12 ≤ 11 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 12); linarith
    have hlog2' : (1/2:ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
    have hknn : (0:ℝ) ≤ ((Nat.log 2 (4 * S15Y Pa X j) : ℕ) : ℝ) := Nat.cast_nonneg _
    push_cast
    rw [hL]
    nlinarith [hlog, hlog12, hlog2', hknn, hlogN0]
  have hT4 : 64 * ((Nat.log 2 (4 * S15Y Pa X j) + 1 : ℕ) : ℝ)
      * Pa.N ^ ((23:ℝ)/24 + (1:ℝ)/4000) ≤ 1472 * L^4 * B := by
    have hNc : Pa.N ^ ((23:ℝ)/24 + (1:ℝ)/4000) ≤ B := by rw [hB]; exact S15Br6_ge_c4000 Pa X
    have h1 : 64 * ((Nat.log 2 (4 * S15Y Pa X j) + 1 : ℕ) : ℝ)
        * Pa.N^((23:ℝ)/24+(1:ℝ)/4000) ≤ 64 * (23*L) * B := by
      have h64 : 64 * ((Nat.log 2 (4 * S15Y Pa X j) + 1 : ℕ) : ℝ) ≤ 64 * (23*L) :=
        mul_le_mul_of_nonneg_left hk (by norm_num)
      calc 64 * ((Nat.log 2 (4 * S15Y Pa X j) + 1 : ℕ) : ℝ)
            * Pa.N^((23:ℝ)/24+(1:ℝ)/4000)
          = (64 * ((Nat.log 2 (4 * S15Y Pa X j) + 1 : ℕ) : ℝ))
              * Pa.N^((23:ℝ)/24+(1:ℝ)/4000) := by ring
        _ ≤ (64 * (23*L)) * B :=
            mul_le_mul h64 hNc (Real.rpow_nonneg hN0.le _) (by linarith)
        _ = 64 * (23*L) * B := by ring
    refine le_trans h1 ?_
    have hLle : L ≤ L^4 := by
      have h := pow_le_pow_right₀ hL1 (show (1:ℕ) ≤ 4 by norm_num)
      simpa using h
    calc 64 * (23*L) * B = (1472*L) * B := by ring
      _ ≤ (1472*L^4) * B :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hLle (by norm_num : (0:ℝ) ≤ 1472)) hB0
      _ = 1472 * L^4 * B := by ring
  -- ### summing the four pieces
  have hsum : 16 * (S15Y Pa X j : ℝ)
      + 256 * Pa.N * (X:ℝ)^(-(1:ℝ)/2)
      + 64 * ((S15Y Pa X j : ℝ)^((1:ℝ)/3)) * Pa.N^((2:ℝ)/3) * L^4
      + 64 * ((Nat.log 2 (4 * S15Y Pa X j) + 1 : ℕ) : ℝ) * Pa.N^((23:ℝ)/24 + (1:ℝ)/4000)
      ≤ 1968 * L^4 * B := by linarith [hT1, hT2, hT3, hT4]
  calc (16 * Cp) * (16 * (S15Y Pa X j : ℝ)
         + 256 * Pa.N * (X:ℝ)^(-(1:ℝ)/2)
         + 64 * ((S15Y Pa X j : ℝ)^((1:ℝ)/3)) * Pa.N^((2:ℝ)/3) * L^4
         + 64 * ((Nat.log 2 (4 * S15Y Pa X j) + 1 : ℕ) : ℝ) * Pa.N^((23:ℝ)/24 + (1:ℝ)/4000)) * A
      ≤ (16 * Cp) * (1968 * L^4 * B) * A := by
        apply mul_le_mul_of_nonneg_right _ hA
        exact mul_le_mul_of_nonneg_left hsum (by nlinarith [hCp])
    _ = (31488 * Cp) * L^4 * B * A := by ring

end

end Work.FIArea4.A6R2
