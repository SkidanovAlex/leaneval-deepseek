import Mathlib
import Submission.Work.KMTAreas.A5.absorbWeightTools

/-!
# The weight `⟨Log N⟩^{-10}` loses at most a constant when `N` is replaced by its floor

Section 5 of Krause--Mirek--Tao integrates the single-scale `ℓᵖ` estimates of the minor-arc part
over a lacunary set of scales; the *weights* produced there are `⟨Log N⟩^{-10}`, and the scales
are integers.  This module records the elementary fact that replacing a positive real scale `N`
by the integer scale `⌊N⌋` changes the weight by at most a fixed multiplicative constant, so
that an estimate stated at integer scales can be used at real scales (and conversely).

Concretely, `heightWeight c N = (max 1 (logb 2 N))^{-c}`, and the claim is

`heightWeight 10 ⌊N⌋ ≤ 1024 · heightWeight 10 N`  for every `N ≥ 1`.

The proof is the observation that `⌊N⌋` is comparable with `N` *after taking logarithms*: for
`N ≥ 2`, with `n = ⌊N⌋ ≥ 2` one has `log₂ N < log₂ (n+1) ≤ log₂ (2n) = 1 + log₂ n ≤ 2 log₂ n`,
so the logarithm only doubles, and raising to the power `-10` costs the factor `2^10 = 1024`.
For `1 ≤ N ≤ 2` both weights are equal to `1`.  The constant `1024` is the natural one (it is
attained in the limit `N → 3^-`).
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Work.KMTAreas.A5

noncomputable section

open scoped NNReal

/-- The real-variable core of `heightWeight_floor_le`, in the form in which the floor has already
been replaced by an integer `n ≥ 2` with `N < n + 1`: if `logb 2 N ≤ 2 logb 2 n` then the
`-10`-th powers are comparable with constant `1024 = 2^10`. -/
private lemma logb_floor_key (n : ℕ) {N : ℝ} (hN2 : (2 : ℝ) < N) (hn2 : (2 : ℝ) ≤ n)
    (hN : N < (n : ℝ) + 1) :
    (max 1 (Real.logb 2 (n : ℝ))) ^ (-(10 : ℝ))
      ≤ (1024 : ℝ) * (max 1 (Real.logb 2 N)) ^ (-(10 : ℝ)) := by
  have hlogN_ge1 : 1 ≤ Real.logb 2 N := by
    have h := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
      (by norm_num : (0 : ℝ) < 2) hN2.le
    rwa [Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)] at h
  have hlogn_ge1 : 1 ≤ Real.logb 2 (n : ℝ) := by
    have h := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
      (by norm_num : (0 : ℝ) < 2) hn2
    rwa [Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)] at h
  have hbound : Real.logb 2 N ≤ 2 * Real.logb 2 (n : ℝ) := by
    have h1 : Real.logb 2 N ≤ Real.logb 2 ((n : ℝ) + 1) :=
      Real.logb_le_logb_of_le (by norm_num) (by linarith) hN.le
    have h2 : Real.logb 2 ((n : ℝ) + 1) ≤ Real.logb 2 (2 * (n : ℝ)) :=
      Real.logb_le_logb_of_le (by norm_num) (by linarith) (by linarith)
    have h3 : Real.logb 2 (2 * (n : ℝ)) = 1 + Real.logb 2 (n : ℝ) := by
      rw [Real.logb_mul (by norm_num) (by positivity)]
      rw [Real.logb_self_eq_one (by norm_num)]
    have h4 : 1 + Real.logb 2 (n : ℝ) ≤ 2 * Real.logb 2 (n : ℝ) := by linarith
    linarith
  have key := rpow_neg_le_mul_two_pow (m := Real.logb 2 (n : ℝ)) (M := Real.logb 2 N)
    (a := 10) (by linarith) (by linarith) (by norm_num) hbound
  rw [show (2 : ℝ) ^ (10 : ℝ) = 1024 by norm_num] at key
  rw [max_eq_right hlogn_ge1, max_eq_right hlogN_ge1]
  exact key

/-- The real-variable form of the floor comparison: for every `N ≥ 1`,
`(max 1 (logb 2 ⌊N⌋))^{-10} ≤ 1024 · (max 1 (logb 2 N))^{-10}`. -/
private lemma heightWeight_floor_key : ∀ N : ℝ≥0, 1 ≤ N →
    (max 1 (Real.logb 2 ((Nat.floor N : ℕ) : ℝ))) ^ (-(10 : ℝ))
      ≤ (1024 : ℝ) * (max 1 (Real.logb 2 (N : ℝ))) ^ (-(10 : ℝ)) := by
  intro N hN
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    have h1 : ((0 : ℝ)) < (1 : ℝ) := by norm_num
    have h2 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    linarith
  by_cases h2 : (N : ℝ) ≤ 2
  · -- small scales: both weights are `1`
    have hlogN : Real.logb 2 (N : ℝ) ≤ 1 := by
      have h := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) hNpos h2
      rwa [Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)] at h
    have hM : max 1 (Real.logb 2 (N : ℝ)) = 1 := max_eq_left hlogN
    have hL1 : (max 1 (Real.logb 2 ((Nat.floor N : ℕ) : ℝ))) ^ (-(10 : ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (le_max_left _ _) (by norm_num)
    rw [hM, Real.one_rpow]
    linarith
  · -- large scales: `logb 2 N ≤ 2 logb 2 ⌊N⌋`
    have h2lt : (2 : ℝ) < (N : ℝ) := not_le.mp h2
    set n : ℕ := Nat.floor N with hn
    have hn2 : 2 ≤ n := by
      rw [hn]
      apply Nat.le_floor
      rw [← NNReal.coe_le_coe]
      push_cast
      exact h2lt.le
    have hn2R : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
    have hNlt : (N : ℝ) < (n : ℝ) + 1 := by
      have h := Nat.lt_floor_add_one N
      rw [← hn] at h
      exact_mod_cast h
    have hkey := logb_floor_key n h2lt hn2R hNlt
    have hL : max 1 (Real.logb 2 ((Nat.floor N : ℕ) : ℝ)) = max 1 (Real.logb 2 (n : ℝ)) := by
      rw [← hn]
    rw [hL]
    exact hkey

/-- **The `⟨Log N⟩^{-10}` weight of the floor of `N` is comparable with that of `N`.**  There is a
constant `K > 0` (namely `1024`) with `heightWeight 10 ⌊N⌋ ≤ K · heightWeight 10 N` for all
`N ≥ 1`. -/
theorem heightWeight_floor_le :
    ∃ K : NNReal, 0 < K ∧ ∀ N : NNReal, 1 ≤ N →
      Work.Analysis.EndVar.heightWeight 10 (Nat.floor N : NNReal)
        ≤ K * Work.Analysis.EndVar.heightWeight 10 N := by
  refine ⟨1024, by norm_num, fun N hN => ?_⟩
  rw [← NNReal.coe_le_coe]
  push_cast
  rw [Work.Analysis.EndVar.coe_heightWeight, Work.Analysis.EndVar.coe_heightWeight]
  exact heightWeight_floor_key N hN

end

end Work.KMTAreas.A5
