import Mathlib.Probability.Distributions.SetBernoulli
import Submission.Prob
import Submission.PVIter

open ProbabilityTheory MeasureTheory unitInterval Set
open scoped ENNReal NNReal BigOperators unitInterval ProbabilityTheory
open FractionalExpectationThresholds
open Submission.PVIter
open Submission.FET

attribute [local instance] Classical.propDecidable

namespace Submission
namespace TailBnd

/-!
# Binomial-tail estimates for the iteration

Let `bOne L t := ∑ j ∈ Icc (2^t) (2^(t+1)-1), ((2^(t+1)-1).choose j) * (1/L)^j` and
`tailCost L d := ∑_{t=0}^{d-1} bOne L t`  (see `Submission.PVIter`).

The goals here, for `L ≥ 8`:
1. `bOne_le`:      `bOne L t ≤ 2·(4/L)^(2^t)`.
2. `tailCost_le`:  `tailCost L d ≤ 8/L` for every `d`.
3. `tailCost_le_thirds`: `tailCost L d ≤ 1/3` for every `d`  (used in the final hitting theorem).

## Proof outline

**`bOne L t ≤ (4/L)^(2^t)` (crude).**  With `m = 2^t`, `n = 2^(t+1)-1`, `x = 1/L ∈ [0,1]`,
every summand satisfies `(n.choose j)·x^j ≤ (n.choose j)·x^m` (as `j ≥ m` and `x ≤ 1`), so

    bOne L t ≤ x^m · ∑_{j∈Icc m n} n.choose j ≤ x^m · 2^n ≤ x^m · 2^(2^(t+1)) = (4x)^(2^t).

**`bOne L 0 = 1/L`,  `bOne L 1 = 3/L² + 1/L³`** by direct computation.

**`tailCost L d ≤ 8/L`.**  Split off `t = 0`; for `t ≥ 1`, `2^t ≥ 2t` and `0 ≤ 4/L ≤ 1`, hence
`bOne L t ≤ (4/L)^(2t) = ((4/L)^2)^t`; summing the geometric tail with ratio `(4/L)^2` gives
`1/L + (4/L)^2/(1-(4/L)^2) ≤ 8/L`.

**`tailCost L d ≤ 1/3`.**  For `L ≥ 8` one has `1/L ≤ 1/8` and
`bOne L 1 = 3/L²+1/L³ ≤ 25/512`.  For `t ≥ 2`, `bOne L t ≤ 2·(4/L)^(2^t) ≤ 2·(1/2)^(2^t)`;
since `2^t ≥ 4(t-1)` the tail `∑_{t≥2} (1/2)^(2^t) ≤ ∑_{t≥2} (1/16)^(t-1) = 1/15`.
Hence `tailCost L d ≤ 1/8 + 25/512 + 2/15 ≤ 1/3`.
-/

/-- `k + 1 ≤ 2^k` for every natural `k`. -/
lemma succ_le_two_pow (k : ℕ) : k + 1 ≤ 2 ^ k := by
  exact Nat.succ_le_of_lt (k.lt_two_pow_self)

/-- `2t ≤ 2^t` for `t ≥ 1`. -/
lemma two_mul_le_two_pow {t : ℕ} (ht : 1 ≤ t) : 2 * t ≤ 2 ^ t := by
  have h := succ_le_two_pow (t - 1)
  have ht1 : t ≤ 2 ^ (t - 1) := by simpa [Nat.sub_add_cancel ht] using h
  calc
    2 * t ≤ 2 * 2 ^ (t - 1) := by exact Nat.mul_le_mul_left 2 ht1
    _ = 2 ^ t := by
      have ht' : t = (t - 1) + 1 := (Nat.sub_add_cancel ht).symm
      conv_rhs => rw [ht']
      rw [pow_succ]
      ring

/-- `4(t-1) ≤ 2^t` for `t ≥ 2`. -/
lemma four_mul_pred_le_two_pow {t : ℕ} (ht : 2 ≤ t) : 4 * (t - 1) ≤ 2 ^ t := by
  have h1 : 1 ≤ t - 1 := by omega
  have h3 : t - 1 ≤ 2 ^ (t - 2) := by
    have h4 := succ_le_two_pow (t - 2)
    have ht2 : t - 2 + 1 = t - 1 := by omega
    simpa [ht2] using h4
  have h5 : 2 * (t - 1) ≤ 2 * 2 ^ (t - 2) := Nat.mul_le_mul_left 2 h3
  calc
    4 * (t - 1) = 2 * (2 * (t - 1)) := by omega
    _ ≤ 2 * (2 * 2 ^ (t - 2)) := by exact Nat.mul_le_mul_left 2 h5
    _ = 2 ^ t := by
      have ht2 : t = (t - 2) + 2 := (Nat.sub_add_cancel ht).symm
      conv_rhs => rw [ht2]
      rw [pow_add]
      ring_nf

/-- `2 ^ (2^(t+1)) = 4 ^ (2^t)` (real powers). -/
lemma two_pow_two_pow_succ (t : ℕ) : (2 : ℝ) ^ ((2 : ℕ) ^ (t + 1)) = (4 : ℝ) ^ ((2 : ℕ) ^ t) := by
  have hnat : (2 : ℕ) ^ (t + 1) = 2 * (2 : ℕ) ^ t := by
    rw [pow_succ]
    exact Nat.mul_comm _ _
  rw [hnat, pow_mul]
  norm_num

/-- tail of the binomial distribution, bounded by `(4x)^(2^t)` when `0 ≤ x ≤ 1`. -/
lemma binom_tail_le (t : ℕ) (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    (∑ j ∈ Finset.Icc ((2 : ℕ) ^ t) ((2 : ℕ) ^ (t + 1) - 1),
         (((2 : ℕ) ^ (t + 1) - 1).choose j : ℝ) * x ^ j)
    ≤ ((4 : ℝ) * x) ^ ((2 : ℕ) ^ t) := by
  let m : ℕ := (2 : ℕ) ^ t
  let n : ℕ := (2 : ℕ) ^ (t + 1) - 1
  have hterm : ∀ j ∈ Finset.Icc m n, (n.choose j : ℝ) * x ^ j ≤ (n.choose j : ℝ) * x ^ m := by
    intro j hj
    have hjm : m ≤ j := (Finset.mem_Icc.mp hj).1
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_of_le_one hx0 hx1 hjm) (by exact_mod_cast Nat.zero_le (n.choose j))
  have h1 :
      (∑ j ∈ Finset.Icc m n, (n.choose j : ℝ) * x ^ j)
        ≤ ∑ j ∈ Finset.Icc m n, (n.choose j : ℝ) * x ^ m := by
    exact Finset.sum_le_sum hterm
  have h2 : (∑ j ∈ Finset.Icc m n, (n.choose j : ℝ) * x ^ m)
      = x ^ m * (∑ j ∈ Finset.Icc m n, (n.choose j : ℝ)) := by
    calc
      (∑ j ∈ Finset.Icc m n, (n.choose j : ℝ) * x ^ m)
          = ∑ j ∈ Finset.Icc m n, x ^ m * (n.choose j : ℝ) := by
            refine Finset.sum_congr rfl ?_
            intro j hj; rw [mul_comm]
      _ = x ^ m * (∑ j ∈ Finset.Icc m n, (n.choose j : ℝ)) := by rw [Finset.mul_sum]
  have hbin_nat : (∑ j ∈ Finset.Icc m n, n.choose j) ≤ 2 ^ n := by
    have hsub : Finset.Icc m n ⊆ Finset.Icc 0 n := by
      intro j hj
      exact Finset.mem_Icc.mpr ⟨Nat.zero_le j, (Finset.mem_Icc.mp hj).2⟩
    have hsum := Finset.sum_le_sum_of_subset_of_nonneg hsub (f := fun j => n.choose j)
      (by intro j hj hjn; exact Nat.zero_le _)
    have hmem : (∑ j ∈ Finset.Icc 0 n, n.choose j) = ∑ j ∈ Finset.range (n + 1), n.choose j := by
      refine Finset.sum_congr ?_ ?_
      · ext j; simp [Finset.mem_Icc]
      · intro j hj; rfl
    calc
      (∑ j ∈ Finset.Icc m n, n.choose j) ≤ ∑ j ∈ Finset.Icc 0 n, n.choose j := hsum
      _ = ∑ j ∈ Finset.range (n + 1), n.choose j := hmem
      _ = 2 ^ n := Nat.sum_range_choose n
  have hbin : (∑ j ∈ Finset.Icc m n, (n.choose j : ℝ)) ≤ (2 : ℝ) ^ n := by
    exact_mod_cast hbin_nat
  have hxm : 0 ≤ x ^ m := pow_nonneg hx0 m
  have h3 : x ^ m * (∑ j ∈ Finset.Icc m n, (n.choose j : ℝ)) ≤ x ^ m * (2 : ℝ) ^ n := by
    exact mul_le_mul_of_nonneg_left hbin hxm
  have hn : n ≤ (2 : ℕ) ^ (t + 1) := by
    dsimp [n]
    exact Nat.sub_le _ _
  have h2n : (2 : ℝ) ^ n ≤ (2 : ℝ) ^ ((2 : ℕ) ^ (t + 1)) := by
    exact pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hn
  have h4 : x ^ m * (2 : ℝ) ^ n ≤ x ^ m * (2 : ℝ) ^ ((2 : ℕ) ^ (t + 1)) := by
    exact mul_le_mul_of_nonneg_left h2n hxm
  have h5 : x ^ m * (2 : ℝ) ^ ((2 : ℕ) ^ (t + 1)) = ((4 : ℝ) * x) ^ ((2 : ℕ) ^ t) := by
    rw [two_pow_two_pow_succ]
    dsimp [m]
    rw [mul_pow]
    ring
  calc
    (∑ j ∈ Finset.Icc ((2 : ℕ) ^ t) ((2 : ℕ) ^ (t + 1) - 1),
         (((2 : ℕ) ^ (t + 1) - 1).choose j : ℝ) * x ^ j)
        = ∑ j ∈ Finset.Icc m n, (n.choose j : ℝ) * x ^ j := by
          simp [m, n]
    _ ≤ x ^ m * (2 : ℝ) ^ n := by
      calc
        (∑ j ∈ Finset.Icc m n, (n.choose j : ℝ) * x ^ j)
            ≤ ∑ j ∈ Finset.Icc m n, (n.choose j : ℝ) * x ^ m := h1
        _ = x ^ m * (∑ j ∈ Finset.Icc m n, (n.choose j : ℝ)) := h2
        _ ≤ x ^ m * (2 : ℝ) ^ n := h3
    _ ≤ x ^ m * (2 : ℝ) ^ ((2 : ℕ) ^ (t + 1)) := h4
    _ = ((4 : ℝ) * x) ^ ((2 : ℕ) ^ t) := h5

/-- `bOne L t ≤ (4/L)^(2^t)` for `1 ≤ L`. -/
lemma bOne_le_crude {L : ℕ} (hL : 1 ≤ L) (t : ℕ) :
    Submission.PVIter.bOne L t ≤ (4 / (L : ℝ)) ^ ((2 : ℕ) ^ t) := by
  have hx0 : 0 ≤ (1 : ℝ) / (L : ℝ) := by positivity
  have hx1 : (1 : ℝ) / (L : ℝ) ≤ 1 := by
    have hLpos : (0 : ℝ) < (L : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le (by decide : (0 : ℕ) < 1) hL)
    rw [div_le_iff₀ hLpos]
    norm_num
    exact_mod_cast hL
  calc
    Submission.PVIter.bOne L t
        = ∑ j ∈ Finset.Icc ((2 : ℕ) ^ t) ((2 : ℕ) ^ (t + 1) - 1),
            (((2 : ℕ) ^ (t + 1) - 1).choose j : ℝ) * ((1 : ℝ) / (L : ℝ)) ^ j := by
          rfl
    _ ≤ ((4 : ℝ) * ((1 : ℝ) / (L : ℝ))) ^ ((2 : ℕ) ^ t) := by
          exact binom_tail_le t ((1 : ℝ) / (L : ℝ)) hx0 hx1
    _ = (4 / (L : ℝ)) ^ ((2 : ℕ) ^ t) := by
          congr 1
          ring

/-- `bOne L t ≤ 2·(4/L)^(2^t)` for `L ≥ 2`. -/
lemma bOne_le_two_mul {L : ℕ} (hL : 2 ≤ L) (t : ℕ) :
    Submission.PVIter.bOne L t ≤ 2 * (4 / (L : ℝ)) ^ ((2 : ℕ) ^ t) := by
  have h1 : 1 ≤ L := le_trans (by decide : (1 : ℕ) ≤ 2) hL
  have hb := bOne_le_crude h1 t
  have hnon : 0 ≤ (4 / (L : ℝ)) ^ ((2 : ℕ) ^ t) := pow_nonneg (by positivity) _
  calc
    Submission.PVIter.bOne L t ≤ (4 / (L : ℝ)) ^ ((2 : ℕ) ^ t) := hb
    _ ≤ 2 * (4 / (L : ℝ)) ^ ((2 : ℕ) ^ t) := by linarith

/-- geometric tail over a finite `Ico`, `∑_{k∈Ico a b} x^k ≤ x^a/(1-x)`. -/
lemma geom_Ico_le (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x < 1) {a b : ℕ} (hab : a ≤ b) :
    (∑ k ∈ Finset.Ico a b, x ^ k) ≤ x ^ a / (1 - x) := by
  have hgeom := geom_sum_Ico_mul_neg x hab
  have hnon : 0 ≤ x ^ b := pow_nonneg hx0 _
  have hle : (∑ k ∈ Finset.Ico a b, x ^ k) * (1 - x) ≤ x ^ a := by
    rw [hgeom]
    linarith
  exact (le_div_iff₀ (by linarith : 0 < 1 - x)).mpr hle

/-- finite geometric series over a `range` is at most the infinite one. -/
lemma sum_range_geom_le (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x < 1) (n : ℕ) :
    (∑ k ∈ Finset.range n, x ^ k) ≤ 1 / (1 - x) := by
  have hEq : Finset.Ico 0 n = Finset.range n := by
    ext j; simp
  rw [← hEq]
  exact geom_Ico_le x hx0 hx1 (Nat.zero_le n)

/-- the tail sum `∑_{t≥2} 2·(1/2)^(2^t)` is at most `2/15`. -/
lemma tail15_le {d : ℕ} :
    (∑ t ∈ Finset.Ico 2 d, 2 * (1 / 2 : ℝ) ^ ((2 : ℕ) ^ t)) ≤ 2 / 15 := by
  calc
    (∑ t ∈ Finset.Ico 2 d, 2 * (1 / 2 : ℝ) ^ ((2 : ℕ) ^ t))
        = 2 * (∑ t ∈ Finset.Ico 2 d, (1 / 2 : ℝ) ^ ((2 : ℕ) ^ t)) := by
          rw [← Finset.mul_sum]
    _ ≤ 2 * (∑ t ∈ Finset.Ico 2 d, (1 / 16 : ℝ) ^ (t - 1)) := by
          refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
          refine Finset.sum_le_sum ?_
          intro t ht
          have ht2 : 2 ≤ t := (Finset.mem_Ico.mp ht).1
          have hpow : (1 / 2 : ℝ) ^ ((2 : ℕ) ^ t) ≤ (1 / 2 : ℝ) ^ (4 * (t - 1)) := by
            exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (four_mul_pred_le_two_pow ht2)
          calc
            (1 / 2 : ℝ) ^ ((2 : ℕ) ^ t) ≤ (1 / 2 : ℝ) ^ (4 * (t - 1)) := hpow
            _ = (1 / 16 : ℝ) ^ (t - 1) := by
              rw [pow_mul]
              congr 1
              norm_num
    _ = 2 * ((1 / 16 : ℝ) * (∑ k ∈ Finset.range (d - 2), (1 / 16 : ℝ) ^ k)) := by
          have hsub := Finset.sum_Ico_eq_sum_range (fun t => (1 / 16 : ℝ) ^ (t - 1)) 2 d
          rw [hsub]
          congr 1
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro k hk
          have hk1 : (2 + k) - 1 = k + 1 := by omega
          rw [hk1, pow_succ]
          ring
    _ ≤ 2 * ((1 / 16 : ℝ) * (1 / (1 - (1 / 16 : ℝ)))) := by
          refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
          refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
          exact sum_range_geom_le (1 / 16 : ℝ) (by norm_num) (by norm_num) (d - 2)
    _ = 2 / 15 := by norm_num

/-- exact `bOne L 0 = 1/L`. -/
lemma bOne_zero (L : ℕ) : Submission.PVIter.bOne L 0 = 1 / (L : ℝ) := by
  unfold Submission.PVIter.bOne
  norm_num

/-- exact `bOne L 1 = 3·(1/L)^2 + (1/L)^3`. -/
lemma bOne_one (L : ℕ) : Submission.PVIter.bOne L 1 = 3 * (1 / (L : ℝ)) ^ 2 + (1 / (L : ℝ)) ^ 3 := by
  unfold Submission.PVIter.bOne
  norm_num
  rw [← Finset.Ico_add_one_right_eq_Icc (2 : ℕ) 3]
  rw [Finset.sum_Ico_eq_sum_range]
  norm_num
  rw [show Finset.range 2 = Finset.range (1 + 1) by rfl]
  rw [Finset.sum_range_succ]
  rw [show Finset.range 1 = Finset.range (0 + 1) by rfl]
  rw [Finset.sum_range_succ]
  norm_num

/-- `tailCost` is a sum over `range d` of the `bOne` terms. -/
lemma tailCost_eq_sum (L : ℕ) (d : ℕ) :
    Submission.PVIter.tailCost L d = ∑ t ∈ Finset.range d, Submission.PVIter.bOne L t := by
  induction d with
  | zero => simp [Submission.PVIter.tailCost]
  | succ d ih =>
      rw [Submission.PVIter.tailCost]
      rw [ih]
      rw [Finset.sum_range_succ]
      ring

/-- `Finset.range d = Finset.Ico 0 d`. -/
lemma range_eq_Ico_zero (d : ℕ) : Finset.range d = Finset.Ico 0 d := by
  ext t; simp

/-- sum over `Ico 0 1` is the first term. -/
lemma sum_Ico_zero_one (f : ℕ → ℝ) : (∑ t ∈ Finset.Ico 0 1, f t) = f 0 := by
  rw [show Finset.Ico 0 1 = Finset.range 1 by ext t; simp]
  rw [show Finset.range 1 = Finset.range (0 + 1) by rfl]
  rw [Finset.sum_range_succ]
  simp

/-- sum over `Ico 0 2` is the first two terms. -/
lemma sum_Ico_zero_two (f : ℕ → ℝ) : (∑ t ∈ Finset.Ico 0 2, f t) = f 0 + f 1 := by
  rw [show Finset.Ico 0 2 = Finset.range 2 by ext t; simp]
  rw [show Finset.range 2 = Finset.range (1 + 1) by rfl]
  rw [Finset.sum_range_succ]
  rw [show Finset.range 1 = Finset.range (0 + 1) by rfl]
  rw [Finset.sum_range_succ]
  ring

/-- disjointness of the two pieces `Ico 0 a` and `Ico a d`. -/
lemma disjoint_Ico_zero (a d : ℕ) : Disjoint (Finset.Ico 0 a : Finset ℕ) (Finset.Ico a d) := by
  rw [Finset.disjoint_left]
  intro t ht1 ht2
  simp [Finset.mem_Ico] at ht1 ht2
  omega

/-- `tailCost L d`, for `d ≥ 1`, splits as `bOne L 0` plus the rest. -/
lemma tailCost_eq_split_one {L : ℕ} {d : ℕ} (hd : 1 ≤ d) :
    Submission.PVIter.tailCost L d
      = Submission.PVIter.bOne L 0 + ∑ t ∈ Finset.Ico 1 d, Submission.PVIter.bOne L t := by
  rw [tailCost_eq_sum, range_eq_Ico_zero]
  have hsplit : Finset.Ico 0 d = Finset.Ico 0 1 ∪ Finset.Ico 1 d := by
    ext t; simp [Finset.mem_Ico]; omega
  rw [hsplit]
  rw [Finset.sum_union (disjoint_Ico_zero 1 d)]
  rw [sum_Ico_zero_one]

/-- `tailCost L d`, for `d ≥ 2`, splits as `bOne L 0 + bOne L 1` plus the rest. -/
lemma tailCost_eq_split_two {L : ℕ} {d : ℕ} (hd : 2 ≤ d) :
    Submission.PVIter.tailCost L d
      = Submission.PVIter.bOne L 0 + Submission.PVIter.bOne L 1
        + ∑ t ∈ Finset.Ico 2 d, Submission.PVIter.bOne L t := by
  rw [tailCost_eq_sum, range_eq_Ico_zero]
  have hsplit : Finset.Ico 0 d = Finset.Ico 0 2 ∪ Finset.Ico 2 d := by
    ext t; simp [Finset.mem_Ico]; omega
  rw [hsplit]
  rw [Finset.sum_union (disjoint_Ico_zero 2 d)]
  rw [sum_Ico_zero_two]

/-- `1/L ≤ 1/8` for `8 ≤ L`. -/
lemma invL_le_eighth {L : ℕ} (hL : 8 ≤ L) : 1 / (L : ℝ) ≤ 1 / 8 := by
  have hLpos : (0 : ℝ) < (L : ℝ) := by exact_mod_cast (by omega : 0 < L)
  have hLc : (8 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
  exact one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 8) hLc

/-- `bOne L 0 ≤ 1/8` for `8 ≤ L`. -/
lemma bOne_zero_le {L : ℕ} (hL : 8 ≤ L) : Submission.PVIter.bOne L 0 ≤ 1 / 8 := by
  rw [bOne_zero]
  exact invL_le_eighth hL

/-- `bOne L 1 ≤ 25/512` for `8 ≤ L`. -/
lemma bOne_one_le {L : ℕ} (hL : 8 ≤ L) : Submission.PVIter.bOne L 1 ≤ 25 / 512 := by
  have hx : 1 / (L : ℝ) ≤ 1 / 8 := invL_le_eighth hL
  have hx0 : 0 ≤ 1 / (L : ℝ) := by positivity
  have hx2 : (1 / (L : ℝ)) ^ 2 ≤ (1 / 8 : ℝ) ^ 2 := pow_le_pow_left₀ hx0 hx 2
  have hx3 : (1 / (L : ℝ)) ^ 3 ≤ (1 / 8 : ℝ) ^ 3 := pow_le_pow_left₀ hx0 hx 3
  calc
    Submission.PVIter.bOne L 1 = 3 * (1 / (L : ℝ)) ^ 2 + (1 / (L : ℝ)) ^ 3 := bOne_one L
    _ ≤ 3 * (1 / 8 : ℝ) ^ 2 + (1 / 8 : ℝ) ^ 3 := by nlinarith
    _ = 25 / 512 := by norm_num

/-- per-round binomial tail: `bOne L t ≤ 2·(4/L)^(2^t)` for `L ≥ 8`. -/
theorem bOne_le (L : ℕ) (hL : 8 ≤ L) (t : ℕ) :
    Submission.PVIter.bOne L t ≤ 2 * (4 / L : ℝ) ^ ((2 : ℕ) ^ t) := by
  exact bOne_le_two_mul (le_trans (by decide : (2 : ℕ) ≤ 8) hL) t

/-- total budget over any number of rounds is at most `8/L`. -/
theorem tailCost_le {L : ℕ} (hL : 8 ≤ L) (d : ℕ) :
    Submission.PVIter.tailCost L d ≤ 8 / L := by
  by_cases hd0 : d = 0
  · subst d
    simp [Submission.PVIter.tailCost]
    positivity
  · have hd1 : 1 ≤ d := by omega
    let u : ℝ := (4 : ℝ) / (L : ℝ)
    have hLpos : (0 : ℝ) < (L : ℝ) := by exact_mod_cast (by omega : 0 < L)
    have hLc : (8 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
    have hu0 : 0 ≤ u := by positivity
    have hu0' : 0 < u := by positivity
    have hule : u ≤ 1 / 2 := by
      dsimp [u]
      rw [div_le_iff₀ hLpos]
      norm_num
      nlinarith
    have hu2le : u ^ 2 ≤ (1 / 2) * u := by
      calc
        u ^ 2 = u * u := by ring
        _ ≤ u * (1 / 2) := mul_le_mul_of_nonneg_left hule hu0
        _ = (1 / 2) * u := by ring
    have hu2lt1 : u ^ 2 < 1 := by nlinarith
    have hb : ∀ t ∈ Finset.Ico 1 d,
        Submission.PVIter.bOne L t ≤ (u ^ 2) ^ t := by
      intro t ht
      have ht1 : 1 ≤ t := (Finset.mem_Ico.mp ht).1
      have hcrude := bOne_le_crude (le_trans (by decide : (1 : ℕ) ≤ 8) hL) t
      have hle1 : u ^ ((2 : ℕ) ^ t) ≤ u ^ (2 * t) := by
        exact pow_le_pow_of_le_one hu0 (by nlinarith : u ≤ 1) (two_mul_le_two_pow ht1)
      calc
        Submission.PVIter.bOne L t ≤ u ^ ((2 : ℕ) ^ t) := by simpa [u] using hcrude
        _ ≤ u ^ (2 * t) := hle1
        _ = (u ^ 2) ^ t := by rw [pow_mul]
    have htail : (∑ t ∈ Finset.Ico 1 d, Submission.PVIter.bOne L t)
        ≤ u ^ 2 / (1 - u ^ 2) := by
      calc
        (∑ t ∈ Finset.Ico 1 d, Submission.PVIter.bOne L t)
            ≤ ∑ t ∈ Finset.Ico 1 d, (u ^ 2) ^ t := Finset.sum_le_sum hb
        _ ≤ (u ^ 2) ^ 1 / (1 - u ^ 2) := geom_Ico_le (u ^ 2) (by nlinarith) hu2lt1 hd1
        _ = u ^ 2 / (1 - u ^ 2) := by ring
    have hfirst : Submission.PVIter.bOne L 0 ≤ 1 / (L : ℝ) := by
      rw [bOne_zero]
    have hu2le14 : u ^ 2 ≤ 1 / 4 := by
      calc
        u ^ 2 ≤ (1 / 2) * u := hu2le
        _ ≤ (1 / 2) * (1 / 2) := mul_le_mul_of_nonneg_left hule (by norm_num)
        _ = 1 / 4 := by norm_num
    have hthree : (3 / 4 : ℝ) ≤ 1 - u ^ 2 := by nlinarith
    have hinv : 1 / (1 - u ^ 2) ≤ 4 / 3 := by
      have hconv : (1 : ℝ) / (3 / 4) = 4 / 3 := by norm_num
      rw [← hconv]
      exact one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 3 / 4) hthree
    have hdenpos : 0 < 1 - u ^ 2 := by nlinarith
    have htail' : u ^ 2 / (1 - u ^ 2) ≤ (2 / 3) * u := by
      calc
        u ^ 2 / (1 - u ^ 2) = u ^ 2 * (1 / (1 - u ^ 2)) := by field_simp [hdenpos.ne']
        _ ≤ u ^ 2 * (4 / 3) := mul_le_mul_of_nonneg_left hinv (pow_nonneg hu0 2)
        _ ≤ (1 / 2) * u * (4 / 3) := by
          exact mul_le_mul_of_nonneg_right hu2le (by norm_num : (0 : ℝ) ≤ 4 / 3)
        _ = (2 / 3) * u := by ring
    calc
      Submission.PVIter.tailCost L d
          = Submission.PVIter.bOne L 0 + ∑ t ∈ Finset.Ico 1 d, Submission.PVIter.bOne L t :=
            tailCost_eq_split_one hd1
      _ ≤ 1 / (L : ℝ) + u ^ 2 / (1 - u ^ 2) := by
            exact add_le_add hfirst htail
      _ = u / 4 + u ^ 2 / (1 - u ^ 2) := by
            have hL_eq : 1 / (L : ℝ) = u / 4 := by
              dsimp [u]
              field_simp [hLpos.ne']
            rw [hL_eq]
      _ ≤ u / 4 + (2 / 3) * u := by linarith
      _ ≤ 8 / (L : ℝ) := by
            have hu8 : (8 : ℝ) / (L : ℝ) = 2 * u := by
              dsimp [u]
              field_simp [hLpos.ne']
              ring
            rw [hu8]
            nlinarith

/-- the total budget is small enough for the `3/4`-hitting theorem: `tailCost L d ≤ 1/3`. -/
theorem tailCost_le_thirds {L : ℕ} (hL : 8 ≤ L) (d : ℕ) :
    Submission.PVIter.tailCost L d ≤ 1 / 3 := by
  by_cases hd0 : d = 0
  · subst d
    simp [Submission.PVIter.tailCost]
  · by_cases hd1 : d = 1
    · subst d
      calc
        Submission.PVIter.tailCost L 1 = Submission.PVIter.bOne L 0 := by simp [Submission.PVIter.tailCost]
        _ ≤ 1 / 8 := bOne_zero_le hL
        _ ≤ 1 / 3 := by norm_num
    · have hd2 : 2 ≤ d := by omega
      have hfirst : Submission.PVIter.bOne L 0 + Submission.PVIter.bOne L 1 ≤ 89 / 512 := by
        have h0 := bOne_zero_le hL
        have h1 := bOne_one_le hL
        linarith
      have hb2 : ∀ t ∈ Finset.Ico 2 d,
          Submission.PVIter.bOne L t ≤ 2 * (1 / 2 : ℝ) ^ ((2 : ℕ) ^ t) := by
        intro t ht
        have h4le12 : (4 : ℝ) / (L : ℝ) ≤ 1 / 2 := by
          have h1 := invL_le_eighth hL
          calc
            (4 : ℝ) / (L : ℝ) = 4 * (1 / (L : ℝ)) := by ring
            _ ≤ 4 * (1 / 8) := mul_le_mul_of_nonneg_left h1 (by norm_num)
            _ = 1 / 2 := by norm_num
        have hpow : (4 / (L : ℝ)) ^ ((2 : ℕ) ^ t) ≤ (1 / 2 : ℝ) ^ ((2 : ℕ) ^ t) := by
          exact pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 4 / (L : ℝ)) h4le12 ((2 : ℕ) ^ t)
        have hleL : (4 / (L : ℝ)) ^ ((2 : ℕ) ^ t) ≤ (1 / 2 : ℝ) ^ ((2 : ℕ) ^ t) := hpow
        calc
          Submission.PVIter.bOne L t ≤ 2 * (4 / (L : ℝ)) ^ ((2 : ℕ) ^ t) := bOne_le_two_mul (le_trans (by decide : (2 : ℕ) ≤ 8) hL) t
          _ ≤ 2 * (1 / 2 : ℝ) ^ ((2 : ℕ) ^ t) := mul_le_mul_of_nonneg_left hleL (by norm_num)
      have htail : (∑ t ∈ Finset.Ico 2 d, Submission.PVIter.bOne L t)
          ≤ 2 / 15 := by
        calc
          (∑ t ∈ Finset.Ico 2 d, Submission.PVIter.bOne L t)
              ≤ ∑ t ∈ Finset.Ico 2 d, 2 * (1 / 2 : ℝ) ^ ((2 : ℕ) ^ t) := Finset.sum_le_sum hb2
          _ ≤ 2 / 15 := tail15_le
      calc
        Submission.PVIter.tailCost L d
            = Submission.PVIter.bOne L 0 + Submission.PVIter.bOne L 1
              + ∑ t ∈ Finset.Ico 2 d, Submission.PVIter.bOne L t := tailCost_eq_split_two hd2
        _ ≤ 89 / 512 + 2 / 15 := by linarith
        _ ≤ 1 / 3 := by norm_num

end TailBnd
end Submission
