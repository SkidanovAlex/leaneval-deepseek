import Mathlib.Probability.Distributions.SetBernoulli
import ChallengeDeps
import Submission.SelCore
import Submission.Deep
import Submission.Binom
import Submission.Binom2
import Submission.BinomMed

/-!
# BinomOne: binomial mass and generalized uniform-comparison for threshold N = 1.

PROVE the declarations below (no unfinished proofs). You may add helper lemmas.
Use `Binom2.binom_ge_uniform` (in `Submission.Binom2`) as a template for
`binomSum_ge_c_sizeAvg` (its proof is the same, replacing the median-mass
hypothesis by the parameter `hmass`).

All sums are over the finite type of subsets; `n := Fintype.card X`.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
open Classical
open MeasureTheory ProbabilityTheory Measure unitInterval Finset
open scoped NNReal ENNReal BigOperators

namespace Submission

open _root_.SupremumOfSelectorProcesses

namespace BinomOne

open Frame
open Sel.Deep
open Sel.Deep.Sys

variable {X : Type*} [Fintype X]

/-- elementary bound: (1-p)^n * (1 + n p) ≤ 1 for p ∈ [0,1]. -/
lemma one_minus_pow_mul_le_one (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    ∀ n : ℕ, (1 - p) ^ n * (1 + (n : ℝ) * p) ≤ 1 := by
  intro n
  induction n with
  | zero => norm_num
  | succ n ih =>
      have hdiff : (1 - p) ^ n * (1 + (n : ℝ) * p) -
          (1 - p) ^ (Nat.succ n) * (1 + ((Nat.succ n : ℕ) : ℝ) * p)
          = (1 - p) ^ n * ((Nat.succ n : ℕ) : ℝ) * p ^ 2 := by
        rw [pow_succ]
        simp
        ring
      have hd0 : 0 ≤ (1 - p) ^ n * ((Nat.succ n : ℕ) : ℝ) * p ^ 2 := by
        positivity
      have hle : (1 - p) ^ (Nat.succ n) * (1 + ((Nat.succ n : ℕ) : ℝ) * p) ≤
          (1 - p) ^ n * (1 + (n : ℝ) * p) := by
        nlinarith
      exact le_trans hle ih

/-- (1-p)^n ≤ 1/(1+np). -/
lemma one_minus_pow_le (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    ∀ n : ℕ, (1 - p) ^ n ≤ 1 / (1 + (n : ℝ) * p) := by
  intro n
  have hden : 0 < 1 + (n : ℝ) * p := by positivity
  rw [le_div_iff₀ hden]
  exact one_minus_pow_mul_le_one p hp0 hp1 n

/-- if n p ≥ 1/2 then P(|Xp| ≥ 1) ≥ 1/4: the binomial tail mass over sizes ≥ 1. -/
lemma mass_ge_quarter (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (hnp : (1 / 2 : ℝ) ≤ (Fintype.card X : ℝ) * p) :
    (1 / 4 : ℝ) ≤ ∑ k ∈ Finset.Icc 1 (Fintype.card X),
      ((Fintype.card X).choose k : ℝ) * p ^ k * (1 - p) ^ (Fintype.card X - k) := by
  classical
  let f : ℕ → ℝ := fun k => ((Fintype.card X).choose k : ℝ) * p ^ k * (1 - p) ^ (Fintype.card X - k)
  have hfull : (∑ k ∈ Finset.Icc 0 (Fintype.card X), f k) = 1 := by
    dsimp [f]
    exact BinomMed.binom_full (Fintype.card X) p
  have hf0 : f 0 = (1 - p) ^ (Fintype.card X) := by
    dsimp [f]
    rw [Nat.choose_zero_right]
    simp
  have hset : (Finset.Icc 0 (Fintype.card X)).erase 0 = Finset.Icc 1 (Fintype.card X) := by
    ext k
    constructor <;> intro h <;> simp at h ⊢ <;> omega
  have hsum_split : (∑ k ∈ Finset.Icc 1 (Fintype.card X), f k) + f 0 =
      ∑ k ∈ Finset.Icc 0 (Fintype.card X), f k := by
    rw [← hset]
    exact Finset.sum_erase_add (s := Finset.Icc 0 (Fintype.card X)) (f := f) (a := 0) (by simp)
  have htail : (∑ k ∈ Finset.Icc 1 (Fintype.card X), f k) = 1 - (1 - p) ^ (Fintype.card X) := by
    calc
      (∑ k ∈ Finset.Icc 1 (Fintype.card X), f k)
          = (∑ k ∈ Finset.Icc 0 (Fintype.card X), f k) - f 0 := by linarith
      _ = 1 - (1 - p) ^ (Fintype.card X) := by rw [hfull, hf0]
  rw [htail]
  have hqle : (1 - p) ^ (Fintype.card X) ≤
      1 / (1 + (Fintype.card X : ℝ) * p) :=
    one_minus_pow_le p (le_of_lt hp0) (le_of_lt hp1) (Fintype.card X)
  have hden : 0 < 1 + (Fintype.card X : ℝ) * p := by positivity
  have h34 : 1 / (1 + (Fintype.card X : ℝ) * p) ≤ (3 : ℝ) / 4 := by
    rw [div_le_div_iff₀ hden (by norm_num : 0 < (4 : ℝ))]
    nlinarith
  have hq34 : (1 - p) ^ (Fintype.card X) ≤ (3 : ℝ) / 4 := le_trans hqle h34
  linarith

/-- generalized uniform comparison: if the binomial mass of sizes ≥ N is ≥ c then
    c * (average of g over N-subsets) ≤ binomial sum of g. -/
theorem binomSum_ge_c_sizeAvg (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (c : ℝ) (N : ℕ)
    (hc0 : 0 ≤ c) (hNn : N ≤ Fintype.card X)
    (hmass : c ≤ ∑ k ∈ Finset.Icc N (Fintype.card X),
       ((Fintype.card X).choose k : ℝ) * p ^ k * (1 - p) ^ (Fintype.card X - k))
    (g : Set X → ℝ) (hg : ∀ T : Set X, 0 ≤ g T) (hmono : Monotone g) :
    c * Binom.sizeAvg g N ≤ Binom.binomSum p g := by
  classical
  have hp0le : 0 ≤ p := le_of_lt hp0
  have hp1le : p ≤ 1 := le_of_lt hp1
  let w : ℕ → ℝ := fun k => ((Fintype.card X).choose k : ℝ) * p ^ k * (1 - p) ^ (Fintype.card X - k)
  have hw_nonneg (k : ℕ) : 0 ≤ w k := by
    dsimp [w]
    positivity
  have havg : 0 ≤ Binom.sizeAvg g N := by
    simpa [Binom2.sizeAvg] using (Binom2.sizeAvg_nonneg (X := X) g hg N hNn)
  calc
    c * Binom.sizeAvg g N ≤ (∑ k ∈ Finset.Icc N (Fintype.card X), w k) * Binom.sizeAvg g N := by
        exact mul_le_mul_of_nonneg_right hmass havg
    _ ≤ Binom.binomSum p g := by
        calc
          (∑ k ∈ Finset.Icc N (Fintype.card X), w k) * Binom.sizeAvg g N
              ≤ ∑ k ∈ Finset.Icc N (Fintype.card X), w k * Binom.sizeAvg g k := by
                  rw [Finset.sum_mul]
                  apply Finset.sum_le_sum
                  intro k hk
                  have hNk : N ≤ k := (Finset.mem_Icc.mp hk).1
                  have hkn : k ≤ Fintype.card X := (Finset.mem_Icc.mp hk).2
                  exact mul_le_mul_of_nonneg_left
                    (by simpa [Binom2.sizeAvg] using
                      (Binom2.sizeAvg_le_of_le (X := X) g hmono N k hNk hkn)) (hw_nonneg k)
          _ = ∑ k ∈ Finset.Icc N (Fintype.card X),
                Binom.sizeSum g k * p ^ k * (1 - p) ^ (Fintype.card X - k) := by
                apply Finset.sum_congr rfl
                intro k hk
                have hkn : k ≤ Fintype.card X := (Finset.mem_Icc.mp hk).2
                rw [mul_comm]
                simpa [w] using
                  ((by simpa [Binom2.sizeSum, Binom2.sizeAvg] using
                      (Binom2.term_eq_avg_w (X := X) p g k hkn)) : Binom.sizeSum g k * p ^ k * (1 - p) ^ (Fintype.card X - k)
                        = Binom.sizeAvg g k * (((Fintype.card X).choose k : ℝ) * p ^ k * (1 - p) ^ (Fintype.card X - k))).symm
          _ ≤ Binom.binomSum p g := by
                simpa [Binom2.sizeSum, Binom2.binomSum] using
                  (Binom2.binomSum_ge_Icc (X := X) p g hg hp0le hp1le N)

/-- case n p < 1 (but ≥ 1/2): binomial expectation ≥ (1/4)·(average over 1-subsets). -/
theorem binom_ge_one (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (hnp : (1 / 2 : ℝ) ≤ (Fintype.card X : ℝ) * p)
    (g : Set X → ℝ) (hg : ∀ T : Set X, 0 ≤ g T) (hmono : Monotone g) :
    (1 / 4 : ℝ) * Binom.sizeAvg g 1 ≤ Binom.binomSum p g := by
  have hNn : 1 ≤ Fintype.card X := by
    by_contra h
    have hn0 : Fintype.card X = 0 := by omega
    have hbad : (1 / 2 : ℝ) ≤ (0 : ℝ) := by simpa [hn0] using hnp
    norm_num at hbad
  have hmass := mass_ge_quarter (X := X) p hp0 hp1 hnp
  exact binomSum_ge_c_sizeAvg (X := X) p hp0 hp1 (1 / 4) 1 (by norm_num) hNn hmass g hg hmono

end BinomOne
end Submission
