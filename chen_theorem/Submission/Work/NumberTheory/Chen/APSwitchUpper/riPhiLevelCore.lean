/-
# `APSwitchUpper.riPhiLevelCore` — the level constants `Cv`, `Tv` of the delay calculus

Definitions and elementary identities for the partial sums `evenSum`/`oddSum` of the
Rosser–Iwaniec delay family, the level constants `Cv n`, `Tv n`, and the finite
recursions `moment_ineq`, `mass_ineq`, `mass_identity`, `Cv_lower` quoted by the
assembled envelope comparison `riPhi_le_env`.  This module is the *base* of that
development: it imports nothing from it, so lemmas about `Cv`/`Tv` may be proved
in parallel modules that import this one.
-/

import Mathlib
import Submission.Work.NumberTheory.Chen.APSwitchUpper.prof
import Submission.Work.NumberTheory.Chen.APSwitchUpper.riPhiDelay
import Submission.Work.NumberTheory.Chen.APSwitchUpper.profC_summed_delay
import Submission.Work.NumberTheory.Chen.APSwitchUpper.riPhiEnvDefs
import Submission.Work.NumberTheory.Chen.APSwitchUpper.profC_intervalIntegrable
import Submission.Work.NumberTheory.Chen.APSwitchUpper.sum_intervalIntegral_eq_integral_uIoc
import Submission.Work.NumberTheory.Chen.APSwitchUpper.logPad2_L1_lower
import Submission.Work.NumberTheory.Chen.APSwitchUpper.logPad2_L2_lower
import Submission.Work.NumberTheory.Chen.APSwitchUpper.logPad2_L1_upper
import Submission.Work.NumberTheory.Chen.APSwitchUpper.integral_L1lo
import Submission.Work.NumberTheory.Chen.APSwitchUpper.integral_L1up_tail
import Submission.Work.NumberTheory.Chen.APSwitchUpper.integral_L2lo
import Submission.Work.NumberTheory.Chen.APSwitchUpper.integral_L2lo_mul_u4
import Submission.Work.NumberTheory.Chen.APSwitchUpper.integral_L1lo_mul_L2lo

namespace Work.NumberTheory.Chen.APSwitchUpper

open MeasureTheory Finset
open scoped BigOperators

noncomputable section

attribute [local instance] Classical.propDecidable

/-! ## Support facts for the individual profiles -/

lemma profC_two_mul_eq_zero_of_lt_one (i : ℕ) {u : ℝ} (h : u < 1) : profC (2 * i) u = 0 := by
  induction i with
  | zero => rw [profC_zero]; exact if_neg (by rintro ⟨h1, -⟩; linarith)
  | succ i ih =>
      have hsucc : 2 * (i + 1) = (2 * i + 1) + 1 := by ring
      rw [hsucc, profC_succ, if_pos (two_mul_add_one_mod i)]
      exact if_neg (by rintro ⟨h1, -⟩; linarith)

lemma profC_two_mul_add_one_eq_zero_of_lt_two (i : ℕ) {u : ℝ} (h : u < 2) :
    profC (2 * i + 1) u = 0 := by
  rw [profC_succ, if_neg (two_mul_mod_one i)]
  exact if_neg (by rintro ⟨h2, -⟩; linarith)

lemma oddSum_eq_zero_of_lt_two (n : ℕ) {u : ℝ} (h : u < 2) : oddSum n u = 0 := by
  unfold oddSum
  exact Finset.sum_eq_zero (fun i _ => profC_two_mul_add_one_eq_zero_of_lt_two i h)

lemma evenSum_eq_zero_of_lt_one (n : ℕ) {u : ℝ} (h : u < 1) : evenSum n u = 0 := by
  unfold evenSum
  exact Finset.sum_eq_zero (fun i _ => profC_two_mul_eq_zero_of_lt_one i h)

lemma oddSum_eq_zero_of_le (n : ℕ) {u : ℝ} (h : ((2 * n + 4 : ℕ) : ℝ) ≤ u) :
    oddSum n u = 0 := by
  unfold oddSum
  refine Finset.sum_eq_zero (fun i hi => profC_support (2 * i + 1) u ?_)
  rw [Finset.mem_range] at hi
  have h2 : (((2 * i + 1 : ℕ)) : ℝ) + 3 ≤ ((2 * n + 4 : ℕ) : ℝ) := by
    exact_mod_cast (by omega : 2 * i + 1 + 3 ≤ 2 * n + 4)
  linarith

lemma evenSum_eq_zero_of_le (n : ℕ) {u : ℝ} (h : ((2 * n + 3 : ℕ) : ℝ) ≤ u) :
    evenSum n u = 0 := by
  unfold evenSum
  refine Finset.sum_eq_zero (fun i hi => profC_support (2 * i) u ?_)
  rw [Finset.mem_range] at hi
  have h2 : (((2 * i : ℕ)) : ℝ) + 3 ≤ ((2 * n + 3 : ℕ) : ℝ) := by
    exact_mod_cast (by omega : 2 * i + 3 ≤ 2 * n + 3)
  linarith

/-! ## The level constants `Cv n`, `Tv n` -/

/-- The `n`-th level of `C = ∫_2^∞ riPsi`: `Cv n = ∫_2^{2n+4} oddSum n`. -/
def Cv (n : ℕ) : ℝ := ∫ u in (2 : ℝ)..((2 * n + 4 : ℕ) : ℝ), oddSum n u

/-- The `n`-th level of `T = ∫_3^∞ riPhi`: `Tv n = ∫_3^{2n+3} evenSum n`. -/
def Tv (n : ℕ) : ℝ := ∫ u in (3 : ℝ)..((2 * n + 3 : ℕ) : ℝ), evenSum n u

lemma oddSum_intervalIntegrable (n : ℕ) (a b : ℝ) :
    IntervalIntegrable (oddSum n) volume a b := by
  unfold oddSum
  have h := IntervalIntegrable.sum (Finset.range (n + 1))
    (fun i _ => profC_intervalIntegrable (2 * i + 1) a b)
  have h2 : (∑ i ∈ Finset.range (n + 1), profC (2 * i + 1))
      = (fun s => ∑ i ∈ Finset.range (n + 1), profC (2 * i + 1) s) := by
    funext s; rw [Finset.sum_apply]
  rwa [h2] at h

lemma evenSum_intervalIntegrable (n : ℕ) (a b : ℝ) :
    IntervalIntegrable (evenSum n) volume a b := by
  unfold evenSum
  have h := IntervalIntegrable.sum (Finset.range (n + 1))
    (fun i _ => profC_intervalIntegrable (2 * i) a b)
  have h2 : (∑ i ∈ Finset.range (n + 1), profC (2 * i))
      = (fun s => ∑ i ∈ Finset.range (n + 1), profC (2 * i) s) := by
    funext s; rw [Finset.sum_apply]
  rwa [h2] at h

lemma two_le_two_mul_add_four (n : ℕ) : ((2 : ℕ) : ℝ) ≤ ((2 * n + 4 : ℕ) : ℝ) := by
  exact_mod_cast (by omega : 2 ≤ 2 * n + 4)

lemma three_le_two_mul_add_three (n : ℕ) : ((3 : ℕ) : ℝ) ≤ ((2 * n + 3 : ℕ) : ℝ) := by
  exact_mod_cast (by omega : 3 ≤ 2 * n + 3)

lemma Cv_nonneg (n : ℕ) : 0 ≤ Cv n := by
  rw [Cv]
  exact intervalIntegral.integral_nonneg_of_forall (two_le_two_mul_add_four n)
    (fun u => oddSum_nonneg n u)

lemma Tv_nonneg (n : ℕ) : 0 ≤ Tv n := by
  rw [Tv]
  exact intervalIntegral.integral_nonneg_of_forall (three_le_two_mul_add_three n)
    (fun u => evenSum_nonneg n u)

/-- `∫_a^{M}` of a function supported on `(-∞,M]` equals the set integral over `uIoc a M`. -/
lemma intervalIntegral_eq_setIntegral_uIoc {f : ℝ → ℝ} {M a : ℝ}
    (hint : IntervalIntegrable f volume a M) (hzero : ∀ x, M ≤ x → f x = 0) :
    (∫ x in a..M, f x) = ∫ x in Set.uIoc a M, f x := by
  by_cases haM : a ≤ M
  · rw [intervalIntegral.integral_of_le (f := f) haM, Set.uIoc_of_le haM]
  · have hlt : M < a := lt_of_not_ge haM
    have h1 : (∫ x in a..M, f x) = 0 := by
      rw [intervalIntegral.integral_symm (f := f) M a]
      have : (∫ x in M..a, f x) = 0 := by
        rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) ?_,
          intervalIntegral.integral_zero]
        intro x hx
        rw [Set.uIcc_of_le hlt.le, Set.mem_Icc] at hx
        exact hzero x hx.1
      rw [this, neg_zero]
    have h2 : (∫ x in Set.uIoc a M, f x) = 0 := by
      rw [show (0 : ℝ) = ∫ x in Set.uIoc a M, (0 : ℝ) by simp]
      refine MeasureTheory.setIntegral_congr_fun measurableSet_uIoc ?_
      intro x hx
      rw [Set.mem_uIoc] at hx
      rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exfalso; linarith
      · exact hzero x h1.le
    rw [h1, h2]

/-! ## The finite delay identities -/

/-- **Level-`n` even recursion, integrated form.**
`s · evenSum (n+1) s = (3−s)·1_{s≤3} + ∫_{max(s−1,2)}^{2n+4} oddSum n`. -/
lemma evenSum_succ_mul (n : ℕ) {s : ℝ} (h1 : 1 ≤ s) :
    s * evenSum (n + 1) s = (if s ≤ 3 then (3 - s) else 0)
      + ∫ u in (max (s - 1) 2)..((2 * n + 4 : ℕ) : ℝ), oddSum n u := by
  have hsplit : evenSum (n + 1) s
      = profC 0 s + ∑ i ∈ Finset.range (n + 1), profC (2 * (i + 1)) s := by
    unfold evenSum
    rw [Finset.sum_range_succ']
    norm_num
    ring
  rw [hsplit, mul_add, Finset.mul_sum]
  have h0 : s * profC 0 s = (if s ≤ 3 then (3 - s) else 0) := by
    rw [profC_zero]
    by_cases h3 : s ≤ 3
    · rw [if_pos ⟨h1, h3⟩, if_pos h3, mul_div_cancel₀ _ (by linarith : s ≠ 0)]
    · rw [if_neg (fun h => h3 h.2), if_neg h3, mul_zero]
  rw [h0]
  have hsum : (∑ i ∈ Finset.range (n + 1), s * profC (2 * (i + 1)) s)
      = ∑ i ∈ Finset.range (n + 1),
          ∫ u in (max (s - 1) 2)..((((2 * i + 4 : ℕ)) : ℝ)), profC (2 * i + 1) u := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [profC_even_mul i s h1, profTail]
    congr 1
    push_cast
    ring
  rw [hsum]
  have hu : ∀ i ∈ Finset.range (n + 1), (((2 * i + 4 : ℕ)) : ℝ) ≤ (((2 * n + 4 : ℕ)) : ℝ) := by
    intro i hi
    rw [Finset.mem_range] at hi
    push_cast
    have : 2 * i + 4 ≤ 2 * n + 4 := by omega
    exact_mod_cast this
  have hint : ∀ i ∈ Finset.range (n + 1), ∀ p q : ℝ,
      IntervalIntegrable (profC (2 * i + 1)) volume p q :=
    fun i _ p q => profC_intervalIntegrable (2 * i + 1) p q
  have hsupp : ∀ i ∈ Finset.range (n + 1), ∀ x : ℝ,
      (((2 * i + 4 : ℕ)) : ℝ) ≤ x → profC (2 * i + 1) x = 0 := by
    intro i _ x hx
    refine profC_support (2 * i + 1) x ?_
    push_cast at hx ⊢
    linarith
  rw [sum_intervalIntegral_eq_integral_uIoc (Finset.range (n + 1))
      (fun i => profC (2 * i + 1)) (fun i => (((2 * i + 4 : ℕ)) : ℝ))
      (max (s - 1) 2) (((2 * n + 4 : ℕ)) : ℝ) hu hint hsupp]
  have hconv : (∫ u in Set.uIoc (max (s - 1) 2) (((2 * n + 4 : ℕ)) : ℝ),
      ∑ i ∈ Finset.range (n + 1), profC (2 * i + 1) u)
      = ∫ u in Set.uIoc (max (s - 1) 2) (((2 * n + 4 : ℕ)) : ℝ), oddSum n u := by
    simp only [oddSum, Finset.sum_apply]
  rw [hconv, ← intervalIntegral_eq_setIntegral_uIoc (f := oddSum n)
    (M := (((2 * n + 4 : ℕ)) : ℝ)) (a := max (s - 1) 2)
    (oddSum_intervalIntegrable n _ _) (fun x hx => oddSum_eq_zero_of_le n hx)]

/-- On `[1,3]` the even partial sums equal `((3−s)+Cv n)/s`. -/
lemma evenSum_formula (n : ℕ) {s : ℝ} (h1 : 1 ≤ s) (h3 : s ≤ 3) :
    evenSum (n + 1) s = ((3 - s) + Cv n) / s := by
  have h := evenSum_succ_mul n h1
  rw [if_pos h3] at h
  have hmax : max (s - 1) 2 = 2 := max_eq_right (by linarith)
  rw [hmax] at h
  unfold Cv
  field_simp at h ⊢
  linarith [h]

/-- **Level-`n` odd recursion, integrated form.**
`s · oddSum n s = ∫_{s−1}^{2n+3} evenSum n`. -/
lemma oddSum_mul_integral (n : ℕ) {s : ℝ} (h2 : 2 ≤ s) :
    s * oddSum n s = ∫ u in (s - 1)..((2 * n + 3 : ℕ) : ℝ), evenSum n u := by
  have h := (profC_summed_delay).2 n s h2
  rw [h]
  have hterm : ∀ i ∈ Finset.range (n + 1),
      profTail (2 * i) (s - 1) = ∫ u in (s - 1)..(((2 * i + 3 : ℕ)) : ℝ), profC (2 * i) u := by
    intro i _
    rw [profTail]
    congr 1
    push_cast
    ring
  rw [Finset.sum_congr rfl hterm]
  have hu : ∀ i ∈ Finset.range (n + 1), (((2 * i + 3 : ℕ)) : ℝ) ≤ (((2 * n + 3 : ℕ)) : ℝ) := by
    intro i hi
    rw [Finset.mem_range] at hi
    push_cast
    have : 2 * i + 3 ≤ 2 * n + 3 := by omega
    exact_mod_cast this
  have hint : ∀ i ∈ Finset.range (n + 1), ∀ p q : ℝ,
      IntervalIntegrable (profC (2 * i)) volume p q :=
    fun i _ p q => profC_intervalIntegrable (2 * i) p q
  have hsupp : ∀ i ∈ Finset.range (n + 1), ∀ x : ℝ,
      (((2 * i + 3 : ℕ)) : ℝ) ≤ x → profC (2 * i) x = 0 := by
    intro i _ x hx
    refine profC_support (2 * i) x ?_
    push_cast at hx ⊢
    linarith
  rw [sum_intervalIntegral_eq_integral_uIoc (Finset.range (n + 1))
      (fun i => profC (2 * i)) (fun i => (((2 * i + 3 : ℕ)) : ℝ))
      (s - 1) (((2 * n + 3 : ℕ)) : ℝ) hu hint hsupp]
  have hconv : (∫ u in Set.uIoc (s - 1) (((2 * n + 3 : ℕ)) : ℝ),
      ∑ i ∈ Finset.range (n + 1), profC (2 * i) u)
      = ∫ u in Set.uIoc (s - 1) (((2 * n + 3 : ℕ)) : ℝ), evenSum n u := by
    simp only [evenSum, Finset.sum_apply]
  rw [hconv, ← intervalIntegral_eq_setIntegral_uIoc (f := evenSum n)
    (M := (((2 * n + 3 : ℕ)) : ℝ)) (a := s - 1)
    (evenSum_intervalIntegrable n _ _) (fun x hx => evenSum_eq_zero_of_le n hx)]

end

end Work.NumberTheory.Chen.APSwitchUpper
