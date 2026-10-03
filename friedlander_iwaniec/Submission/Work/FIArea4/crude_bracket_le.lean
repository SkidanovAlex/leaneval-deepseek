/-
# Area 4: the crude bracket of the round-6 `ψ`-cut is absorbed by `S15Br6`

The crude (triangle-inequality) estimate of the §15 variance half contributes, after summing over
the `e`-strata, the bracket

  `16·Y + 256·N·X^{-1/2} + 31000·Y^{1/3}N^{2/3}(log N+1)^4 + 64·(log₂(4Y)+1)·N^{23/24+1/4000}`,

`Y = S15Y Pa X j = ⌈N/(X·2^j)⌉ + 1`; this is the left-hand side of the present lemma.  The bound
`≤ 100000·(log N+1)^4·S15Br6 Pa X` matches it against the §15 bracket
`S15Br6 = X^{-1/2}N + X^{-1/3}N + N^{23/24+1/1000}`.

The arithmetic is elementary and term by term, with `L = log N + 1 ≥ 1` and `B = S15Br6 Pa X ≥ 1`:

* `16·Y ≤ 16·(N/X + 2) ≤ 48·B`, since `Y ≤ N/X + 2` (`Nat.ceil_lt_add_one`), `N/X ≤ X^{-1/2}N ≤ B`
  and `1 ≤ B`;
* `256·N·X^{-1/2} ≤ 256·B`, the first summand of `B`;
* `Y^{1/3}N^{2/3} ≤ ((N/X)^{1/3} + 2^{1/3})N^{2/3} ≤ X^{-1/3}N + 2N^{2/3} ≤ 3B`: the first piece is
  the *middle* summand `X^{-1/3}N = N^{1/3}X^{-1/3}N^{2/3}` of `B` (`Real.div_rpow` and
  `N^{1/3}N^{2/3} = N`), the second is below `N^{23/24+1/1000} ≤ B` because `N ≥ 1`; hence
  `31000·Y^{1/3}N^{2/3}L^4 ≤ 93000·L^4·B`;
* `log₂(4Y) + 1 ≤ 23·L` (with `4Y ≤ 12N` and `2^{log₂ m} ≤ m`, `log 2 ≥ 1/2`) and
  `N^{23/24+1/4000} ≤ B`, so `64·(log₂(4Y)+1)·N^{23/24+1/4000} ≤ 1472·L^4·B`.

Since `48 + 256 + 93000 + 1472 = 94776 ≤ 100000`, the four pieces sum to at most
`100000·L^4·B`.

The ingredient lemmas about `S15Br6`, `S15Y` and `Nat.log 2` are proved in the
colleague module `Submission.Work.FIArea4.A6R2.absorb6` and are imported here.
-/
import Mathlib
import Submission.Work.FIArea4.A6Defs
import Submission.Work.FIArea4.S15cutDefs
import Submission.Work.FIArea4.A6R2.absorb6

namespace Work.FIArea4

open Finset
open scoped BigOperators

noncomputable section

set_option maxHeartbeats 1000000

theorem crude_bracket_le (Pa : Work.FITop.Params) (X j : ℕ) (hX : 1 ≤ X) :
    16 * (Work.FIArea4.S15Y Pa X j : ℝ)
      + 256 * Pa.N * (X : ℝ) ^ (-(1 : ℝ) / 2)
      + 31000 * ((Work.FIArea4.S15Y Pa X j : ℝ)) ^ ((1 : ℝ) / 3) * Pa.N ^ ((2 : ℝ) / 3)
          * (Real.log Pa.N + 1) ^ (4 : ℕ)
      + 64 * ((Nat.log 2 (4 * Work.FIArea4.S15Y Pa X j) + 1 : ℕ) : ℝ)
          * Pa.N ^ ((23 : ℝ) / 24 + (1 : ℝ) / 4000)
    ≤ 100000 * (Real.log Pa.N + 1) ^ (4 : ℕ) * Work.FIArea4.S15Br6 Pa X := by
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
  have hB1 : (1:ℝ) ≤ B := by rw [hB]; exact Work.FIArea4.A6R2.S15Br6_ge_one Pa X
  have hB0 : (0:ℝ) ≤ B := le_trans zero_le_one hB1
  have hYb : (S15Y Pa X j : ℝ) ≤ Pa.N / (X:ℝ) + 2 :=
    Work.FIArea4.A6R2.S15Y_cast_le_add_two Pa X j hX
  have hdX : Pa.N / (X:ℝ) ≤ B := by
    rw [hB]; exact Work.FIArea4.A6R2.S15Br6_ge_divX Pa X hX
  -- ### the four pieces, each `≤` its share of `L^4·B`
  have hT1 : 16 * (S15Y Pa X j : ℝ) ≤ 48 * L^4 * B := by
    have h1 : 16 * (S15Y Pa X j : ℝ) ≤ 48 * B := by linarith [hYb, hdX, hB1]
    have h3 : (48:ℝ) ≤ 48 * L^4 := by nlinarith [hL41]
    have h2 : (48:ℝ) * B ≤ 48 * L^4 * B := mul_le_mul_of_nonneg_right h3 hB0
    linarith
  have hT2 : 256 * Pa.N * (X:ℝ)^(-(1:ℝ)/2) ≤ 256 * L^4 * B := by
    have hf : (X:ℝ)^(-(1:ℝ)/2) * Pa.N ≤ B := by
      rw [hB]; exact Work.FIArea4.A6R2.S15Br6_ge_first Pa X
    have h1 : 256 * Pa.N * (X:ℝ)^(-(1:ℝ)/2) ≤ 256 * B := by
      calc 256 * Pa.N * (X:ℝ)^(-(1:ℝ)/2)
          = 256 * ((X:ℝ)^(-(1:ℝ)/2) * Pa.N) := by ring
        _ ≤ 256 * B := mul_le_mul_of_nonneg_left hf (by norm_num)
    have h3 : (256:ℝ) ≤ 256 * L^4 := by nlinarith [hL41]
    have h2 : (256:ℝ) * B ≤ 256 * L^4 * B := mul_le_mul_of_nonneg_right h3 hB0
    linarith
  have hT3 : 31000 * ((S15Y Pa X j : ℝ)^((1:ℝ)/3)) * Pa.N^((2:ℝ)/3) * L^4
      ≤ 93000 * L^4 * B := by
    have hsub : (Pa.N/(X:ℝ) + 2)^((1:ℝ)/3) ≤ (Pa.N/(X:ℝ))^((1:ℝ)/3) + 2^((1:ℝ)/3) :=
      Real.rpow_add_le_add_rpow (div_nonneg hN0.le hX0) (by norm_num) (by norm_num) (by norm_num)
    have h1 : (S15Y Pa X j : ℝ)^((1:ℝ)/3) ≤ (Pa.N/(X:ℝ) + 2)^((1:ℝ)/3) :=
      Real.rpow_le_rpow (by positivity) hYb (by norm_num)
    have h2 : (2:ℝ)^((1:ℝ)/3) ≤ 2 := by
      have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2)
        (by norm_num : (1:ℝ)/3 ≤ 1)
      simpa using h
    have hYpow : (S15Y Pa X j : ℝ)^((1:ℝ)/3) ≤ (Pa.N/(X:ℝ))^((1:ℝ)/3) + 2 := by linarith
    have hN23 : (0:ℝ) ≤ Pa.N^((2:ℝ)/3) := Real.rpow_nonneg hN0.le _
    have hsplit : ((Pa.N/(X:ℝ))^((1:ℝ)/3) + 2) * Pa.N^((2:ℝ)/3)
        = (Pa.N/(X:ℝ))^((1:ℝ)/3) * Pa.N^((2:ℝ)/3) + 2 * Pa.N^((2:ℝ)/3) := by ring
    have hstep : (S15Y Pa X j : ℝ)^((1:ℝ)/3) * Pa.N^((2:ℝ)/3)
        ≤ (Pa.N/(X:ℝ))^((1:ℝ)/3) * Pa.N^((2:ℝ)/3) + 2 * Pa.N^((2:ℝ)/3) := by
      have h := mul_le_mul_of_nonneg_right hYpow hN23
      rwa [hsplit] at h
    have h3 : (Pa.N/(X:ℝ))^((1:ℝ)/3) * Pa.N^((2:ℝ)/3) ≤ B := by
      rw [hB]; exact Work.FIArea4.A6R2.S15Br6_ge_dividethird Pa X hX
    have h4 : (2:ℝ) * Pa.N^((2:ℝ)/3) ≤ 2 * B := by
      have h := Work.FIArea4.A6R2.S15Br6_ge_two_thirds Pa X
      rw [hB]; linarith
    have h3B : (S15Y Pa X j : ℝ)^((1:ℝ)/3) * Pa.N^((2:ℝ)/3) ≤ 3 * B := by linarith
    have hfin : 31000 * ((S15Y Pa X j : ℝ)^((1:ℝ)/3)) * Pa.N^((2:ℝ)/3) ≤ 93000 * B := by
      calc 31000 * ((S15Y Pa X j : ℝ)^((1:ℝ)/3)) * Pa.N^((2:ℝ)/3)
          = 31000 * ((S15Y Pa X j : ℝ)^((1:ℝ)/3) * Pa.N^((2:ℝ)/3)) := by ring
        _ ≤ 31000 * (3 * B) := mul_le_mul_of_nonneg_left h3B (by norm_num)
        _ = 93000 * B := by ring
    calc 31000 * ((S15Y Pa X j : ℝ)^((1:ℝ)/3)) * Pa.N^((2:ℝ)/3) * L^4
        = (31000 * ((S15Y Pa X j : ℝ)^((1:ℝ)/3)) * Pa.N^((2:ℝ)/3)) * L^4 := by ring
      _ ≤ (93000 * B) * L^4 := mul_le_mul_of_nonneg_right hfin hL4nn
      _ = 93000 * L^4 * B := by ring
  -- the logarithm comparison `log₂(4Y) + 1 ≤ 23(log N+1)`
  have hk : ((Nat.log 2 (4 * S15Y Pa X j) + 1 : ℕ) : ℝ) ≤ 23 * L := by
    have hY1 : (S15Y Pa X j : ℝ) ≤ Pa.N + 2 := by
      have hdivN : Pa.N/(X:ℝ) ≤ Pa.N := by
        rw [div_le_iff₀ hXpos]; nlinarith [hN1]
      linarith
    have h4Y : ((4 * S15Y Pa X j : ℕ) : ℝ) ≤ 12 * Pa.N := by
      push_cast
      nlinarith [hY1, hN1]
    have hpow : 2 ^ Nat.log 2 (4 * S15Y Pa X j) ≤ 4 * S15Y Pa X j :=
      Nat.pow_log_le_self 2 (by have := Work.FIArea4.A6R2.S15Y_ge_one Pa X j; omega)
    have hpow' : (2:ℝ) ^ Nat.log 2 (4 * S15Y Pa X j) ≤ 12 * Pa.N := by
      have hcast : (2:ℝ) ^ Nat.log 2 (4 * S15Y Pa X j)
          ≤ ((4 * S15Y Pa X j : ℕ) : ℝ) := by exact_mod_cast hpow
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
    have hNc : Pa.N ^ ((23:ℝ)/24 + (1:ℝ)/4000) ≤ B := by
      rw [hB]; exact Work.FIArea4.A6R2.S15Br6_ge_c4000 Pa X
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
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hLle (by norm_num : (0:ℝ) ≤ 1472)) hB0
      _ = 1472 * L^4 * B := by ring
  -- ### summing the four pieces
  have hsum : 16 * (S15Y Pa X j : ℝ)
      + 256 * Pa.N * (X:ℝ)^(-(1:ℝ)/2)
      + 31000 * ((S15Y Pa X j : ℝ)^((1:ℝ)/3)) * Pa.N^((2:ℝ)/3) * L^4
      + 64 * ((Nat.log 2 (4 * S15Y Pa X j) + 1 : ℕ) : ℝ)
          * Pa.N^((23:ℝ)/24 + (1:ℝ)/4000)
      ≤ 94776 * L^4 * B := by linarith [hT1, hT2, hT3, hT4]
  have hc : (94776:ℝ) * L^4 * B ≤ 100000 * L^4 * B := by
    have h1 : (94776:ℝ) * L^4 ≤ 100000 * L^4 := by nlinarith [hL4nn]
    exact mul_le_mul_of_nonneg_right h1 hB0
  linarith [hsum, hc]

end

end Work.FIArea4
