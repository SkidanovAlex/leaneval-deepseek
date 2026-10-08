/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gorenstein–Walter formalisation team (area BSW, `Work.BSW.Char`)

# The "no bad arithmetic" contract of the Gorenstein–Walter proof

The character-theoretic counting of Bender's §2 (used in the Bender–Suzuki–Walter strategy
towards Gorenstein–Walter) rules out a certain numerical configuration of a hypothetical
group: an integer `n ≥ 5` with `n ≡ 1 (mod 4)` and `3 ∣ n`, three degrees `dᵢ ≥ 3` and three
signs `eᵢ = ±1` satisfying
`1 + e1/d1 + e2/d2 + e3/d3 = 8/(3n)` and `1 + d1² + d2² + d3² ≤ 12n`.

The proof is an elementary case analysis on the multiset of signs `eᵢ`:

* if no `eᵢ` is `-1`, the left-hand side exceeds `1 > 8/(3n)`;
* if exactly one `eᵢ` is `-1`, the left-hand side exceeds `2/3 > 8/(3n)`;
* if exactly two `eᵢ` are `-1`, then `1 − 8/(3n) = 1/dᵢ + 1/dⱼ − 1/dₖ ≤ 2/3`, whereas
  `n ≥ 9` forces `1 − 8/(3n) ≥ 19/27 > 2/3`;
* if all three `eᵢ` are `-1`, the resulting pure arithmetic statement is
  `Work.BSW.Char.k3_impossible` (`Submission/Work/BSW/Char/k3_impossible.lean`).

The reduction `9 ≤ n` used above comes from `n ≥ 5`, `n ≡ 1 (mod 4)`, `3 ∣ n`
(so `n ≡ 9 (mod 12)`).
-/
import Mathlib
import Submission.Work.BSW.Char.k3_impossible

namespace Work.BSW.Char

/-- `e ^ 2 = 1` in `ℤ` forces `e = 1` or `e = -1` (an integral domain has no other roots of
`X ^ 2 - 1`). -/
private lemma int_sq_eq_one {e : ℤ} (h : e ^ 2 = 1) : e = 1 ∨ e = -1 := by
  have h2 : (e - 1) * (e + 1) = 0 := by ring_nf; nlinarith [h]
  rcases mul_eq_zero.mp h2 with h3 | h3
  · left; linarith
  · right; linarith

/-- For a natural number `d ≥ 3`, the reciprocal `1/d` is at most `1/3` (over `ℚ`). -/
private lemma one_div_le_third (d : ℕ) (hd : 3 ≤ d) : (1 : ℚ) / (d : ℚ) ≤ 1 / 3 :=
  one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hd)

/-- For a natural number `d ≥ 3`, the reciprocal `1/d` is positive (over `ℚ`). -/
private lemma one_div_pos' (d : ℕ) (hd : 3 ≤ d) : (0 : ℚ) < 1 / (d : ℚ) := by
  rw [one_div_pos]; exact_mod_cast (by omega : 0 < d)

theorem no_bad_arithmetic (n : ℕ) (hn : 5 ≤ n) (hmod4 : n % 4 = 1) :
    ¬ (3 ∣ n ∧ ∃ d1 d2 d3 : ℕ, 3 ≤ d1 ∧ 3 ≤ d2 ∧ 3 ≤ d3 ∧ ∃ e1 e2 e3 : ℤ,
        e1 ^ 2 = 1 ∧ e2 ^ 2 = 1 ∧ e3 ^ 2 = 1 ∧
        (1 : ℚ) + e1 / (d1 : ℚ) + e2 / (d2 : ℚ) + e3 / (d3 : ℚ) = 8 / (3 * (n : ℚ)) ∧
        1 + d1 ^ 2 + d2 ^ 2 + d3 ^ 2 ≤ 12 * n) := by
  rintro ⟨h3dvd, d1, d2, d3, hd1, hd2, hd3, e1, e2, e3, he1, he2, he3, heq, hineq⟩
  -- `n ≥ 5`, `n ≡ 1 (mod 4)`, `3 ∣ n` give `n ≥ 9` (indeed `n ≡ 9 (mod 12)`).
  have hn9 : 9 ≤ n := by omega
  have hinv1 : (0 : ℚ) < 1 / (d1 : ℚ) := one_div_pos' d1 hd1
  have hinv2 : (0 : ℚ) < 1 / (d2 : ℚ) := one_div_pos' d2 hd2
  have hinv3 : (0 : ℚ) < 1 / (d3 : ℚ) := one_div_pos' d3 hd3
  have hle1 : (1 : ℚ) / (d1 : ℚ) ≤ 1 / 3 := one_div_le_third d1 hd1
  have hle2 : (1 : ℚ) / (d2 : ℚ) ≤ 1 / 3 := one_div_le_third d2 hd2
  have hle3 : (1 : ℚ) / (d3 : ℚ) ≤ 1 / 3 := one_div_le_third d3 hd3
  have h827 : 8 / (3 * (n : ℚ)) ≤ 8 / 27 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num : (0 : ℚ) < 27)
      (by exact_mod_cast (by omega : 27 ≤ 3 * n))
  have hr1 : 8 / (3 * (n : ℚ)) < 1 := by
    rw [div_lt_one (by positivity)]
    have : (9 : ℚ) ≤ 3 * (n : ℚ) := by exact_mod_cast (by omega : 9 ≤ 3 * n)
    linarith
  have hr23 : 8 / (3 * (n : ℚ)) < 2 / 3 := by linarith
  have hr19 : (1 : ℚ) - 8 / (3 * (n : ℚ)) ≥ 19 / 27 := by linarith
  -- Every sign `eᵢ` is `1` or `-1`; split into the eight sign patterns.
  rcases int_sq_eq_one he1 with h1 | h1
  · rcases int_sq_eq_one he2 with h2 | h2
    · rcases int_sq_eq_one he3 with h3' | h3'
      · -- `+ + +`: the left-hand side exceeds `1 > 8/(3n)`.
        rw [h1, h2, h3'] at heq; push_cast at heq
        linarith [heq, hinv1, hinv2, hinv3, hr1]
      · -- `+ + -`: the left-hand side exceeds `2/3 > 8/(3n)`.
        rw [h1, h2, h3'] at heq; push_cast at heq; rw [neg_div] at heq
        linarith [heq, hinv1, hinv2, hle3, hr23]
    · rcases int_sq_eq_one he3 with h3' | h3'
      · -- `+ - +`
        rw [h1, h2, h3'] at heq; push_cast at heq; rw [neg_div] at heq
        linarith [heq, hinv1, hinv3, hle2, hr23]
      · -- `+ - -`: `1 − 8/(3n) = 1/d2 + 1/d3 − 1/d1 ≤ 2/3 < 19/27`.
        rw [h1, h2, h3'] at heq; push_cast at heq; rw [neg_div] at heq; rw [neg_div] at heq
        linarith [heq, hinv1, hle2, hle3, hr19]
  · rcases int_sq_eq_one he2 with h2 | h2
    · rcases int_sq_eq_one he3 with h3' | h3'
      · -- `- + +`
        rw [h1, h2, h3'] at heq; push_cast at heq; rw [neg_div] at heq
        linarith [heq, hinv2, hinv3, hle1, hr23]
      · -- `- + -`: `1 − 8/(3n) = 1/d1 + 1/d3 − 1/d2 ≤ 2/3 < 19/27`.
        rw [h1, h2, h3'] at heq; push_cast at heq; rw [neg_div] at heq; rw [neg_div] at heq
        linarith [heq, hinv2, hle1, hle3, hr19]
    · rcases int_sq_eq_one he3 with h3' | h3'
      · -- `- - +`: `1 − 8/(3n) = 1/d1 + 1/d2 − 1/d3 ≤ 2/3 < 19/27`.
        rw [h1, h2, h3'] at heq; push_cast at heq; rw [neg_div] at heq; rw [neg_div] at heq
        linarith [heq, hinv3, hle1, hle2, hr19]
      · -- `- - -`: the pure arithmetic statement `k3_impossible`.
        rw [h1, h2, h3'] at heq; push_cast at heq
        rw [neg_div] at heq; rw [neg_div] at heq; rw [neg_div] at heq
        have heq' : (1 : ℚ) - 1 / (d1 : ℚ) - 1 / (d2 : ℚ) - 1 / (d3 : ℚ) =
            8 / (3 * (n : ℚ)) := by linarith [heq]
        exact k3_impossible n hn hmod4 h3dvd d1 d2 d3 hd1 hd2 hd3 hineq heq'

end Work.BSW.Char
