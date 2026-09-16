import Submission.ZagierHoffmanProof.ThakurDeg4
import Submission.ZagierHoffmanProof.StepL199
import Submission.ZagierHoffmanProof.StepL3
import Submission.ZagierHoffmanProof.StepL1
import Submission.ZagierHoffmanProof.StepD

set_option autoImplicit false
set_option maxHeartbeats 4000000

open Polynomial RatFunc
open scoped BigOperators WithZero
open WithZero

/-!
# Step: non-vanishing of every depth-two MZV

Combining the block decomposition `ζ_A(a,b) = Σ_d S_d(a,b)` with the depth-two recursion
`S_d(a,b) = P_d(a)·S_{<d}(b)` and Thakur's bounds

  `v (P_d(k)) ≤ exp (−d (k + j_min(k)))`   (Thakur 2.2.5, `ThakurDeg4.v_P_le`)
  `v (S_{<d}(b)) ≤ 1`

gives a *strictly* dominant level: `v (S_d(a,b)) ≤ (v (P_1(a)))^d` and the level `d = 1`
attains `v (S_1(a,b)) = v (P_1(a)) = exp (−(a + j_min(a)))`.  Hence each `S_d` is strictly
smaller than `S_1` for `d ≠ 1`, the sum `ζ_A(a,b)` has valuation `exp (−(a + j_min(a)))`,
and in particular `ζ_A(a,b) ≠ 0` — the depth-two case of Thakur's Theorem 4.
-/

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

section Bounds

lemma exp_pos_arg (a : ℕ+) : (0 : ℤ) < (a : ℤ) + jMin F a := by
  have h1 : (0 : ℤ) < (a : ℤ) := by exact_mod_cast a.pos
  have h2 : (0 : ℤ) ≤ (jMin F a : ℤ) := by
    have := jMin_pos F a
    exact_mod_cast (by omega : 0 ≤ jMin F a)
  linarith

/-- `v (P_d(k)) ≤ 1` at every level (`P_0 = 1` and Thakur 2.2.5 otherwise). -/
lemma v_P_le_one (d : ℕ) (k : ℕ+) : Valued.v (P F d k) ≤ 1 := by
  rcases Nat.eq_zero_or_pos d with h | h
  · subst h
    rw [P_zero_eq_one F k]
    simp
  · refine le_trans (v_P_le F d h k) ?_
    rw [← WithZero.exp_zero]
    refine WithZero.exp_le_exp.mpr ?_
    have hd : (0 : ℤ) ≤ (d : ℤ) := by exact_mod_cast Nat.zero_le d
    have hk := exp_pos_arg F k
    nlinarith

/-- `v (S_{<d}(b)) ≤ 1` at depth one. -/
lemma v_S_lt_one_le_one (d : ℕ) (b : ℕ+) :
    Valued.v (S_lt F 1 (by omega : 0 < 1) (single b) d) ≤ 1 := by
  classical
  rw [S_lt_eq_sum_levels F 1 (by omega : 0 < 1) (single b) d]
  refine Valuation.map_sum_le (v := (Valued.v : Valuation (RatFunc.CompletionAtInfty F) ℤᵐ⁰))
    (g := 1) ?_
  intro i _
  rw [S_one_eq_P F i (by omega : 0 < 1) (single b)]
  exact v_P_le_one F i b

/-- The depth-two block recursion. -/
lemma S_pair_recursion (a b : ℕ+) (d : ℕ) :
    S F 2 (by omega : 0 < 2) (pair a b) d
      = P F d a * S_lt F 1 (by omega : 0 < 1) (single b) d := by
  have h := S_d_recursion F 2 (by omega : 1 < 2) (by omega : 0 < 2) (by omega : 0 < 2 - 1)
    (pair a b) d
  rw [h, pair_zero]
  congr 1

/-- The level-`1` block of a depth-two MZV: the exact valuation. -/
lemma v_S_pair_one (a b : ℕ+) :
    Valued.v (S F 2 (by omega : 0 < 2) (pair a b) 1)
      = WithZero.exp (-((a : ℤ) + jMin F a)) := by
  rw [S_pair_recursion F a b 1, S_lt_one_single_one F b, mul_one]
  exact val_P_one F a

/-- The level-`d` block of a depth-two MZV: Thakur's bound. -/
lemma v_S_pair_le (a b : ℕ+) (d : ℕ) (hd : 1 ≤ d) :
    Valued.v (S F 2 (by omega : 0 < 2) (pair a b) d)
      ≤ WithZero.exp (-((d : ℤ) * ((a : ℤ) + jMin F a))) := by
  rw [S_pair_recursion F a b d, Valuation.map_mul]
  calc Valued.v (P F d a) * Valued.v (S_lt F 1 (by omega : 0 < 1) (single b) d)
      ≤ Valued.v (P F d a) * 1 :=
        mul_le_mul_of_nonneg_left (v_S_lt_one_le_one F d b) zero_le
    _ = Valued.v (P F d a) := mul_one _
    _ ≤ WithZero.exp (-((d : ℤ) * ((a : ℤ) + jMin F a))) := v_P_le F d hd a

end Bounds

section Main

/-- ★★ **Non-vanishing of depth-two MZVs**: for all positive exponents `a`, `b`,
`ζ_A(a, b) ≠ 0` (with `ζ_A(a,b) = Σ_{deg α > deg β} α^{-a} β^{-b}`). -/
theorem zeta_pair_ne_zero (a b : ℕ+) : ζ_A F (pair a b) ≠ 0 := by
  classical
  have hζ : ζ_A F (pair a b) = ∑' d : ℕ, S F 2 (by omega : 0 < 2) (pair a b) d :=
    zeta_eq_tsum_block F (by omega : 0 < 2) (pair a b)
  rw [hζ]
  have hdom := val_tsum_eq_of_dominates F
    (fun d : ℕ => S F 2 (by omega : 0 < 2) (pair a b) d) 1
    (WithZero.exp (-((a : ℤ) + jMin F a))) (WithZero.exp_ne_zero)
    (v_S_pair_one F a b) (summable_S F (by omega : 0 < 2) (pair a b)) ?_
  · intro hzero
    have h1 : Valued.v (∑' d : ℕ, S F 2 (by omega : 0 < 2) (pair a b) d) = 0 := by
      rw [hzero, map_zero]
    rw [hdom] at h1
    exact WithZero.exp_ne_zero h1
  · intro n hn
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h
      rw [S_zero_of_depth_ge_two F (by omega : 0 < 2) (by omega : 1 < 2) (pair a b),
        Valuation.map_zero]
      exact lt_of_lt_of_le (zero_lt_iff.mpr WithZero.exp_ne_zero) le_rfl
    · have hle := v_S_pair_le F a b n h
      refine lt_of_le_of_lt hle ?_
      refine WithZero.exp_lt_exp.mpr ?_
      have h3 : (1 : ℤ) < (n : ℤ) := by
        exact_mod_cast (by omega : 1 < n)
      have h4 := exp_pos_arg F a
      nlinarith

end Main

section Corollaries

lemma val_P_one_lt_one (k : ℕ+) : Valued.v (P F 1 k) < 1 := by
  rw [val_P_one F k, show (1 : ℤᵐ⁰) = WithZero.exp 0 from WithZero.exp_zero.symm,
    WithZero.exp_lt_exp, neg_lt_zero]
  exact exp_pos_arg F k

lemma P_one_ne_zero (k : ℕ+) : P F 1 k ≠ 0 := by
  intro h
  have h1 := val_P_one F k
  rw [h, map_zero] at h1
  exact WithZero.exp_ne_zero h1.symm

/-- ★★ **Non-vanishing of depth-one MZVs**: `ζ_A(k) ≠ 0` for every `k ≥ 1`. -/
theorem zeta_single_ne_zero (k : ℕ+) : ζ_A F (single k) ≠ 0 := by
  classical
  have hζ : ζ_A F (single k) = ∑' d : ℕ, S F 1 (by omega : 0 < 1) (single k) d :=
    zeta_eq_tsum_block F (by omega : 0 < 1) (single k)
  rw [hζ]
  have hterm : ∀ d : ℕ, S F 1 (by omega : 0 < 1) (single k) d = P F d k := by
    intro d
    rw [S_one_eq_P F d (by omega : 0 < 1) (single k)]
    rfl
  have hlt : ∀ n : ℕ, n ≠ 0 → Valued.v (S F 1 (by omega : 0 < 1) (single k) n) < 1 := by
    intro n hn
    rw [hterm n]
    have hn' : 1 ≤ n := by omega
    have hle := v_P_le F n hn' k
    refine lt_of_le_of_lt hle ?_
    rw [show (1 : ℤᵐ⁰) = WithZero.exp 0 from WithZero.exp_zero.symm, WithZero.exp_lt_exp]
    have h4 := exp_pos_arg F k
    have hnz : (0 : ℤ) < (n : ℤ) := by exact_mod_cast (by omega : 0 < n)
    nlinarith
  have hdom := val_tsum_eq_of_dominates F
    (fun d : ℕ => S F 1 (by omega : 0 < 1) (single k) d) 0 (1 : ℤᵐ⁰) one_ne_zero
    (by rw [hterm 0, P_zero_eq_one F k, map_one]) (summable_S F (by omega : 0 < 1) (single k)) hlt
  intro hzero
  have h1 : Valued.v (∑' d : ℕ, S F 1 (by omega : 0 < 1) (single k) d) = 0 := by
    rw [hzero, map_zero]
  rw [hdom] at h1
  exact one_ne_zero h1

end Corollaries

end ZagierHoffmanPositiveChar
