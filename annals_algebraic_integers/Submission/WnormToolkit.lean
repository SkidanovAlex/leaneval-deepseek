import Submission.Contracts
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Toolkit: basic inequalities for the weighted k-norm on Serre's interval

The keystone assembly (`Submission/ConverseAssembly.lean`) needs the elementary
norm arithmetic of `Submission.Contracts.wnorm`:

* pointwise upper bound (the sup is an upper bound);
* `‖P±Q‖_k ≤ ‖P‖_k + ‖Q‖_k`;
* `‖a•P‖_k = |a|·‖P‖_k`;  nonnegativity;
* the exponent-shift inequality `‖P‖_n ≤ M^m · ‖P‖_{n−m}` (`n = n−m + m`)
  where `M` bounds the weight on the interval.

All results are for the fixed data of `Submission.Contracts`: interval
`[aSerre,bSerre]`, measure `muSerre`, weight `weight muSerre x > 0`.
-/

noncomputable section

open MeasureTheory
open scoped Real BigOperators
open Polynomial

namespace Submission.WnormToolkit

open Submission.Contracts
open Submission.Serre
open Submission.SerreExample
open Submission.WeightedNorm

/-- The interval is nonempty: aSerre ≤ bSerre. -/
lemma a_le_b : aSerre ≤ bSerre := by
  norm_num [aSerre, bSerre]

/-- The defining set of `wnorm` is nonempty. -/
lemma wnorm_image_nonempty (k : ℕ) (P : Polynomial ℝ) :
    ((fun x : ℝ => (weight muSerre x) ^ k * |P.eval x|) '' Set.Icc aSerre bSerre).Nonempty := by
  refine ⟨(weight muSerre aSerre) ^ k * |P.eval aSerre|, aSerre, ?_⟩
  exact ⟨⟨le_rfl, a_le_b⟩, rfl⟩

/-- The polynomial evaluation map is continuous on the interval. -/
lemma eval_continuousOn (P : Polynomial ℝ) :
    ContinuousOn (fun x : ℝ => P.eval x) (Set.Icc aSerre bSerre) := by
  have hc : Continuous (fun x : ℝ => Polynomial.aeval x P) := Polynomial.continuous_aeval P
  simpa [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map] using hc.continuousOn

/-- The defining set of `wnorm` is bounded above. -/
lemma wnorm_image_bddAbove (k : ℕ) (P : Polynomial ℝ) :
    BddAbove ((fun x : ℝ => (weight muSerre x) ^ k * |P.eval x|) '' Set.Icc aSerre bSerre) := by
  have hcont : ContinuousOn
      (fun x : ℝ => (weight muSerre x) ^ k * |P.eval x|) (Set.Icc aSerre bSerre) := by
    refine (weight_continuous_on_Icc.pow k).mul ?_
    exact (eval_continuousOn P).abs
  have himg : IsCompact
      ((fun x : ℝ => (weight muSerre x) ^ k * |P.eval x|) '' Set.Icc aSerre bSerre) :=
    CompactIccSpace.isCompact_Icc.image_of_continuousOn hcont
  exact himg.bddAbove

/-- Pointwise bound: values on the interval are bounded by the norm. -/
lemma wnorm_ge_pointwise (k : ℕ) (P : Polynomial ℝ) {x : ℝ} (hx : x ∈ Set.Icc aSerre bSerre) :
    (weight muSerre x) ^ k * |P.eval x| ≤ wnorm k P := by
  unfold wnorm
  exact le_csSup (wnorm_image_bddAbove k P) ⟨x, hx, rfl⟩

/-- `wnorm` is the least upper bound of its defining values. -/
lemma wnorm_sSup_le (k : ℕ) (P : Polynomial ℝ) {a : ℝ}
    (ha : ∀ x : ℝ, x ∈ Set.Icc aSerre bSerre →
      (weight muSerre x) ^ k * |P.eval x| ≤ a) :
    wnorm k P ≤ a := by
  unfold wnorm
  exact csSup_le (wnorm_image_nonempty k P) (by
    intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    exact ha x hx)

/-- Nonnegativity. -/
lemma wnorm_nonneg (k : ℕ) (P : Polynomial ℝ) : 0 ≤ wnorm k P := by
  have hmem : ((weight muSerre aSerre) ^ k * |P.eval aSerre|) ∈
      ((fun x : ℝ => (weight muSerre x) ^ k * |P.eval x|) '' Set.Icc aSerre bSerre) := by
    refine ⟨aSerre, ⟨⟨le_rfl, a_le_b⟩, rfl⟩⟩
  have hval : 0 ≤ (weight muSerre aSerre) ^ k * |P.eval aSerre| :=
    mul_nonneg (pow_nonneg (le_of_lt (weight_pos muSerre aSerre)) k) (abs_nonneg _)
  exact le_trans hval (le_csSup (wnorm_image_bddAbove k P) hmem)

/-- Negation does not change the norm. -/
lemma wnorm_neg (k : ℕ) (P : Polynomial ℝ) : wnorm k (-P) = wnorm k P := by
  apply le_antisymm
  · apply wnorm_sSup_le
    intro x hx
    simpa [abs_neg] using (wnorm_ge_pointwise k P hx)
  · apply wnorm_sSup_le
    intro x hx
    have h := wnorm_ge_pointwise k (-P) hx
    simpa [abs_neg] using h

/-- Sub-additivity. -/
lemma wnorm_add_le (k : ℕ) (P Q : Polynomial ℝ) :
    wnorm k (P + Q) ≤ wnorm k P + wnorm k Q := by
  apply wnorm_sSup_le
  intro x hx
  calc
    (weight muSerre x) ^ k * |(P + Q).eval x|
        = (weight muSerre x) ^ k * |P.eval x + Q.eval x| := by simp
    _ ≤ (weight muSerre x) ^ k * (|P.eval x| + |Q.eval x|) := by
        exact mul_le_mul_of_nonneg_left (abs_add_le _ _) (pow_nonneg (le_of_lt (weight_pos muSerre x)) k)
    _ = (weight muSerre x) ^ k * |P.eval x| + (weight muSerre x) ^ k * |Q.eval x| := by ring
    _ ≤ wnorm k P + wnorm k Q := by
        exact add_le_add (wnorm_ge_pointwise k P hx) (wnorm_ge_pointwise k Q hx)

/-- Sub-additivity of the difference. -/
lemma wnorm_sub_le (k : ℕ) (P Q : Polynomial ℝ) :
    wnorm k (P - Q) ≤ wnorm k P + wnorm k Q := by
  have h1 : wnorm k (P - Q) ≤ wnorm k P + wnorm k (-Q) := by
    simpa [sub_eq_add_neg] using wnorm_add_le k P (-Q)
  rw [wnorm_neg] at h1
  exact h1

/-- Norm of a scalar multiple: `‖a•P‖_k = |a|·‖P‖_k`. -/
lemma wnorm_smul (k : ℕ) (a : ℝ) (P : Polynomial ℝ) :
    wnorm k (a • P) = |a| * wnorm k P := by
  apply le_antisymm
  · apply wnorm_sSup_le
    intro x hx
    calc
      (weight muSerre x) ^ k * |(a • P).eval x|
          = (weight muSerre x) ^ k * (|a| * |P.eval x|) := by simp [smul_eq_mul, abs_mul]
      _ = |a| * ((weight muSerre x) ^ k * |P.eval x|) := by ring
      _ ≤ |a| * wnorm k P := by
          exact mul_le_mul_of_nonneg_left (wnorm_ge_pointwise k P hx) (abs_nonneg a)
  · by_cases ha0 : a = 0
    · subst a
      simpa using (wnorm_nonneg k (0 : Polynomial ℝ))
    · have hpos : 0 < |a| := abs_pos.mpr ha0
      have hdiv : wnorm k P ≤ (1 / |a|) * wnorm k (a • P) := by
        apply wnorm_sSup_le
        intro x hx
        calc
          (weight muSerre x) ^ k * |P.eval x|
              = (1 / |a|) * ((weight muSerre x) ^ k * (|a| * |P.eval x|)) := by
                  field_simp [ne_of_gt hpos]
          _ = (1 / |a|) * ((weight muSerre x) ^ k * |(a • P).eval x|) := by
                  have habs : |a| * |P.eval x| = |(a • P).eval x| := by
                    rw [Polynomial.eval_smul]
                    simp [smul_eq_mul, abs_mul]
                  rw [habs]
          _ ≤ (1 / |a|) * wnorm k (a • P) := by
                  exact mul_le_mul_of_nonneg_left (wnorm_ge_pointwise k (a • P) hx) (by positivity)
      calc
        |a| * wnorm k P ≤ |a| * ((1 / |a|) * wnorm k (a • P)) := by
            exact mul_le_mul_of_nonneg_left hdiv (le_of_lt hpos)
        _ = wnorm k (a • P) := by
            field_simp [ne_of_gt hpos]

/-- Scalar multiple with nonnegative scalar. -/
lemma wnorm_smul_nonneg (k : ℕ) (a : ℝ) (ha : 0 ≤ a) (P : Polynomial ℝ) :
    wnorm k (a • P) = a * wnorm k P := by
  rw [wnorm_smul k a P, abs_of_nonneg ha]

/-- Exponent-shift: `‖P‖_n ≤ M^m · ‖P‖_{n−m}` when `m ≤ n` and `M` bounds the
weight on the interval. -/
lemma wnorm_exp_shift {n m : ℕ} (hm : m ≤ n) {M : ℝ}
    (hM : ∀ x : ℝ, x ∈ Set.Icc aSerre bSerre → weight muSerre x ≤ M) (hM0 : 0 ≤ M)
    (P : Polynomial ℝ) :
    wnorm n P ≤ M ^ m * wnorm (n - m) P := by
  apply wnorm_sSup_le
  intro x hx
  have hle_w : weight muSerre x ≤ M := hM x hx
  have hw0 : 0 ≤ weight muSerre x := le_of_lt (weight_pos muSerre x)
  have hpow : (weight muSerre x) ^ n =
      (weight muSerre x) ^ (n - m) * (weight muSerre x) ^ m := by
    rw [← pow_add]
    congr 1
    omega
  calc
    (weight muSerre x) ^ n * |P.eval x|
        = ((weight muSerre x) ^ (n - m) * |P.eval x|) * (weight muSerre x) ^ m := by
            rw [hpow]
            ring
    _ ≤ ((weight muSerre x) ^ (n - m) * |P.eval x|) * M ^ m := by
            exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hw0 hle_w m)
              (mul_nonneg (pow_nonneg hw0 (n - m)) (abs_nonneg (P.eval x)))
    _ ≤ M ^ m * wnorm (n - m) P := by
            rw [mul_comm]
            exact mul_le_mul_of_nonneg_left (wnorm_ge_pointwise (n - m) P hx) (pow_nonneg hM0 m)

/-- `4 • P` with `4 : ℝ`. -/
lemma wnorm_four_smul (k : ℕ) (P : Polynomial ℝ) :
    wnorm k ((4 : ℝ) • P) = 4 * wnorm k P := by
  rw [wnorm_smul_nonneg k (4 : ℝ) (by norm_num) P]

end Submission.WnormToolkit
