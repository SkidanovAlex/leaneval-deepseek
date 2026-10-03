/-
# `Submission.Work.FITop4.Red5.BformPiTau_tauReduce`

**The `τ`-reduction of the `Π`-restricted, `τ`-truncated sieve form.**
`BformPiTau x N Pz C τ` is the paper's (4.9) form, whose inner variable carries the support
conditions `(n, Π) = 1` (5.8) and `τ(n) ≤ τ` (5.9); it is the object that the round-5 reduction
`Red5.reduction_save` consumes.  The chain always needs it at the *paper's* choice
`τ = tauOf x Asave = (log x)^{2A + 2^{20}}` (10.11).  This file shows that any other threshold
`τ ≥ (log x)^{A + 124}` (the (4.11) lower bound) gives the *same* value up to an error of the
frozen size `c·Ã(x)(log x)^{-(A - 200000)}`.

The mechanism is the two-sided comparison of the truncated and the untruncated form:

* `BformPi_trunc_le` (already proved) gives the lower direction
  `BformPi ≤ BformPiTau σ + σ⁻¹·Σ_{l≤x} ã_l τ(l)³` for every `σ > 0`;
* the *reverse* direction `BformPiTau τ ≤ BformPi + τ⁻¹·Σ_{l≤x} ã_l τ(l)³` proved here.

The reverse direction is the same triangle-inequality argument as `BformPi_trunc_le`, read the
other way: writing `F_m` (untruncated), `T_m` (truncated) and `R_m` (the removed tail) for the
inner sums of a fixed `m`, one has `F_m = T_m + R_m`, hence
`|T_m| ≤ |F_m| + |R_m|`; the removed tail is bounded by `τ⁻¹ Σ_{n : mn ≤ x} ã_{mn} τ(mn)²`, and the
divisor-pair reindexing `TauMulReindex` totals this to `τ⁻¹ Σ_{l ≤ x} ã_l τ(l)³`.

Since `tauOf x Asave ≥ (log x)^{A+124}` and `τ ≥ (log x)^{A+124}`, both `τ⁻¹` and
`(tauOf x Asave)⁻¹` are at most `(log x)^{-(A+124)}`, and the polylogarithmic bound
`Σ_{l≤x} ã_l τ(l)³ ≤ C·Ã(x)(log x)^{131072}` (`AseqTauCubBound`) turns the total error into
`2C·Ã(x)(log x)^{-(A - 130948)} ≤ 2C·Ã(x)(log x)^{-(A - 200000)}`.
-/
import Mathlib
import Submission.Work.FITop4.Red5.Vocab
import Submission.Work.FITop4.Red5.BformPi_trunc_le
import Submission.Work.FITop4.Red5.BformPi_tau_truncation
import Submission.Work.FITop4.Red5.AseqTauCubBound
import Submission.Work.FITop.TauMulReindex

set_option autoImplicit false

namespace Work.FITop4.Red5

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## Elementary bounds on the four factors -/

private lemma moebius_cast_abs_le_one' (n : ℕ) :
    |(ArithmeticFunction.moebius n : ℝ)| ≤ 1 := by
  rw [← Int.cast_abs]
  exact_mod_cast ArithmeticFunction.abs_moebius_le_one

private lemma divisors_card_mono' {n m : ℕ} (_hn : n ≠ 0) (hm : m ≠ 0) (h : n ∣ m) :
    n.divisors.card ≤ m.divisors.card := by
  apply Finset.card_le_card
  intro b hb
  rw [Nat.mem_divisors] at hb ⊢
  exact ⟨dvd_trans hb.1 h, hm⟩

/-- On the removed tail (`τ < τ(n)`) the summand is bounded by
`τ⁻¹ · ã_{mn} τ(mn)²`.  (Identical to the estimate used in `BformPi_trunc_le`.) -/
private lemma abs_term_le' (C τ : ℝ) (hτ : 0 < τ) {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n)
    (hτn : τ < (n.divisors.card : ℝ)) :
    |(ArithmeticFunction.moebius n : ℝ) * Work.FIPlan.gammaTrunc C n
        * Work.FITop.atilFIa (m * n)|
      ≤ τ⁻¹ * (Work.FITop.atilFIa (m * n) * ((m * n).divisors.card : ℝ) ^ 2) := by
  have hn0 : n ≠ 0 := by omega
  have hmn0 : m * n ≠ 0 := by positivity
  have hdvd : n ∣ m * n := dvd_mul_left n m
  have hcard : (n.divisors.card : ℝ) ≤ ((m * n).divisors.card : ℝ) := by
    exact_mod_cast divisors_card_mono' hn0 hmn0 hdvd
  have hã : 0 ≤ Work.FITop.atilFIa (m * n) := Work.FITop.atilFIa_nonneg _
  have hγ : |Work.FIPlan.gammaTrunc C n| ≤ (n.divisors.card : ℝ) :=
    Work.FITop4.abs_gammaTrunc_le C n
  have hμ : |(ArithmeticFunction.moebius n : ℝ)| ≤ 1 := moebius_cast_abs_le_one' n
  have hf : |(ArithmeticFunction.moebius n : ℝ) * Work.FIPlan.gammaTrunc C n
        * Work.FITop.atilFIa (m * n)|
      = |(ArithmeticFunction.moebius n : ℝ)| * |Work.FIPlan.gammaTrunc C n|
        * Work.FITop.atilFIa (m * n) := by
    rw [abs_mul, abs_mul, abs_of_nonneg hã]
  rw [hf]
  have hcpos : 0 < ((m * n).divisors.card : ℝ) := lt_of_lt_of_le hτ (le_trans hτn.le hcard)
  have hτdmn : τ ≤ ((m * n).divisors.card : ℝ) := le_trans hτn.le hcard
  have hc1 : ((m * n).divisors.card : ℝ) ≤ τ⁻¹ * (((m * n).divisors.card : ℝ) ^ 2) := by
    have hmul : τ * ((m * n).divisors.card : ℝ)
        ≤ ((m * n).divisors.card : ℝ) * ((m * n).divisors.card : ℝ) :=
      mul_le_mul_of_nonneg_right hτdmn (le_of_lt hcpos)
    calc ((m * n).divisors.card : ℝ)
        = τ⁻¹ * (τ * ((m * n).divisors.card : ℝ)) := by
          rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hτ), one_mul]
      _ ≤ τ⁻¹ * (((m * n).divisors.card : ℝ) * ((m * n).divisors.card : ℝ)) :=
          mul_le_mul_of_nonneg_left hmul (inv_nonneg.mpr hτ.le)
      _ = τ⁻¹ * (((m * n).divisors.card : ℝ) ^ 2) := by ring
  calc |(ArithmeticFunction.moebius n : ℝ)| * |Work.FIPlan.gammaTrunc C n|
          * Work.FITop.atilFIa (m * n)
      ≤ (1 * (n.divisors.card : ℝ)) * Work.FITop.atilFIa (m * n) :=
        mul_le_mul_of_nonneg_right (mul_le_mul hμ hγ (abs_nonneg _) (by norm_num)) hã
    _ = (n.divisors.card : ℝ) * Work.FITop.atilFIa (m * n) := by ring
    _ ≤ ((m * n).divisors.card : ℝ) * Work.FITop.atilFIa (m * n) :=
        mul_le_mul_of_nonneg_right hcard hã
    _ ≤ (τ⁻¹ * (((m * n).divisors.card : ℝ) ^ 2)) * Work.FITop.atilFIa (m * n) :=
        mul_le_mul_of_nonneg_right hc1 hã
    _ = τ⁻¹ * (Work.FITop.atilFIa (m * n) * ((m * n).divisors.card : ℝ) ^ 2) := by ring

/-! ## The reverse truncation, one `m` at a time -/

private lemma per_m_reverse (x N Pz : ℕ) (C τ : ℝ) (hτ : 0 < τ) {m : ℕ} (hm : 1 ≤ m) :
    |∑ n ∈ Finset.Icc 1 (2 * N),
        (if N < n ∧ m * n ≤ x ∧ Nat.Coprime n m ∧ (∀ q : ℕ, q.Prime → q ≤ Pz → ¬ q ∣ n)
              ∧ ((n.divisors.card : ℝ) ≤ τ)
          then (ArithmeticFunction.moebius n : ℝ) * Work.FIPlan.gammaTrunc C n
            * Work.FITop.atilFIa (m * n) else 0)|
      ≤ |∑ n ∈ Finset.Icc 1 (2 * N),
        (if N < n ∧ m * n ≤ x ∧ Nat.Coprime n m ∧ (∀ q : ℕ, q.Prime → q ≤ Pz → ¬ q ∣ n)
          then (ArithmeticFunction.moebius n : ℝ) * Work.FIPlan.gammaTrunc C n
            * Work.FITop.atilFIa (m * n) else 0)|
        + τ⁻¹ * ∑ n ∈ (Finset.Icc 1 x).filter (fun n => m * n ≤ x),
            Work.FITop.atilFIa (m * n) * ((m * n).divisors.card : ℝ) ^ 2 := by
  have hτinv : 0 ≤ τ⁻¹ := inv_nonneg.mpr hτ.le
  have hsplit_pt : ∀ n,
      (if N < n ∧ m * n ≤ x ∧ Nat.Coprime n m ∧ (∀ q : ℕ, q.Prime → q ≤ Pz → ¬ q ∣ n)
        then (ArithmeticFunction.moebius n : ℝ) * Work.FIPlan.gammaTrunc C n
          * Work.FITop.atilFIa (m * n) else 0)
      = (if N < n ∧ m * n ≤ x ∧ Nat.Coprime n m ∧ (∀ q : ℕ, q.Prime → q ≤ Pz → ¬ q ∣ n)
            ∧ ((n.divisors.card : ℝ) ≤ τ)
          then (ArithmeticFunction.moebius n : ℝ) * Work.FIPlan.gammaTrunc C n
            * Work.FITop.atilFIa (m * n) else 0)
        + (if (N < n ∧ m * n ≤ x ∧ Nat.Coprime n m ∧ (∀ q : ℕ, q.Prime → q ≤ Pz → ¬ q ∣ n))
              ∧ ¬((n.divisors.card : ℝ) ≤ τ)
          then (ArithmeticFunction.moebius n : ℝ) * Work.FIPlan.gammaTrunc C n
            * Work.FITop.atilFIa (m * n) else 0) := by
    intro n
    by_cases hP : (N < n ∧ m * n ≤ x ∧ Nat.Coprime n m
        ∧ (∀ q : ℕ, q.Prime → q ≤ Pz → ¬ q ∣ n))
    · by_cases hD : ((n.divisors.card : ℝ) ≤ τ)
      · have h5 : N < n ∧ m * n ≤ x ∧ Nat.Coprime n m
            ∧ (∀ q : ℕ, q.Prime → q ≤ Pz → ¬ q ∣ n) ∧ ((n.divisors.card : ℝ) ≤ τ) :=
          ⟨hP.1, hP.2.1, hP.2.2.1, hP.2.2.2, hD⟩
        rw [if_pos hP, if_pos h5, if_neg (fun h => h.2 hD)]
        ring
      · have h5 : ¬ (N < n ∧ m * n ≤ x ∧ Nat.Coprime n m
            ∧ (∀ q : ℕ, q.Prime → q ≤ Pz → ¬ q ∣ n) ∧ ((n.divisors.card : ℝ) ≤ τ)) :=
          fun h => hD h.2.2.2.2
        rw [if_pos hP, if_neg h5, if_pos ⟨hP, hD⟩]
        ring
    · have h5 : ¬ (N < n ∧ m * n ≤ x ∧ Nat.Coprime n m
          ∧ (∀ q : ℕ, q.Prime → q ≤ Pz → ¬ q ∣ n) ∧ ((n.divisors.card : ℝ) ≤ τ)) :=
        fun h => hP ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩
      rw [if_neg hP, if_neg h5, if_neg (fun h => hP h.1)]
      ring
  have hsplit : (∑ n ∈ Finset.Icc 1 (2 * N),
        (if N < n ∧ m * n ≤ x ∧ Nat.Coprime n m ∧ (∀ q : ℕ, q.Prime → q ≤ Pz → ¬ q ∣ n)
          then (ArithmeticFunction.moebius n : ℝ) * Work.FIPlan.gammaTrunc C n
            * Work.FITop.atilFIa (m * n) else 0))
      = (∑ n ∈ Finset.Icc 1 (2 * N),
          (if N < n ∧ m * n ≤ x ∧ Nat.Coprime n m ∧ (∀ q : ℕ, q.Prime → q ≤ Pz → ¬ q ∣ n)
                ∧ ((n.divisors.card : ℝ) ≤ τ)
            then (ArithmeticFunction.moebius n : ℝ) * Work.FIPlan.gammaTrunc C n
              * Work.FITop.atilFIa (m * n) else 0))
        + (∑ n ∈ Finset.Icc 1 (2 * N),
            (if (N < n ∧ m * n ≤ x ∧ Nat.Coprime n m
                  ∧ (∀ q : ℕ, q.Prime → q ≤ Pz → ¬ q ∣ n)) ∧ ¬((n.divisors.card : ℝ) ≤ τ)
              then (ArithmeticFunction.moebius n : ℝ) * Work.FIPlan.gammaTrunc C n
                * Work.FITop.atilFIa (m * n) else 0)) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun n _ => hsplit_pt n)
  have htail : |∑ n ∈ Finset.Icc 1 (2 * N),
        (if (N < n ∧ m * n ≤ x ∧ Nat.Coprime n m
              ∧ (∀ q : ℕ, q.Prime → q ≤ Pz → ¬ q ∣ n)) ∧ ¬((n.divisors.card : ℝ) ≤ τ)
          then (ArithmeticFunction.moebius n : ℝ) * Work.FIPlan.gammaTrunc C n
            * Work.FITop.atilFIa (m * n) else 0)|
      ≤ τ⁻¹ * ∑ n ∈ (Finset.Icc 1 x).filter (fun n => m * n ≤ x),
            Work.FITop.atilFIa (m * n) * ((m * n).divisors.card : ℝ) ^ 2 := by
    calc |∑ n ∈ Finset.Icc 1 (2 * N),
            (if (N < n ∧ m * n ≤ x ∧ Nat.Coprime n m
                  ∧ (∀ q : ℕ, q.Prime → q ≤ Pz → ¬ q ∣ n)) ∧ ¬((n.divisors.card : ℝ) ≤ τ)
              then (ArithmeticFunction.moebius n : ℝ) * Work.FIPlan.gammaTrunc C n
                * Work.FITop.atilFIa (m * n) else 0)|
        ≤ ∑ n ∈ Finset.Icc 1 (2 * N),
            |(if (N < n ∧ m * n ≤ x ∧ Nat.Coprime n m
                  ∧ (∀ q : ℕ, q.Prime → q ≤ Pz → ¬ q ∣ n)) ∧ ¬((n.divisors.card : ℝ) ≤ τ)
              then (ArithmeticFunction.moebius n : ℝ) * Work.FIPlan.gammaTrunc C n
                * Work.FITop.atilFIa (m * n) else 0)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ = ∑ n ∈ Finset.Icc 1 (2 * N),
            (if (N < n ∧ m * n ≤ x ∧ Nat.Coprime n m
                  ∧ (∀ q : ℕ, q.Prime → q ≤ Pz → ¬ q ∣ n)) ∧ ¬((n.divisors.card : ℝ) ≤ τ)
              then |(ArithmeticFunction.moebius n : ℝ) * Work.FIPlan.gammaTrunc C n
                * Work.FITop.atilFIa (m * n)| else 0) := by
          apply Finset.sum_congr rfl
          intro n _
          by_cases h : (N < n ∧ m * n ≤ x ∧ Nat.Coprime n m
                ∧ (∀ q : ℕ, q.Prime → q ≤ Pz → ¬ q ∣ n)) ∧ ¬((n.divisors.card : ℝ) ≤ τ)
          · rw [if_pos h, if_pos h]
          · rw [if_neg h, if_neg h, abs_zero]
      _ ≤ ∑ n ∈ Finset.Icc 1 (2 * N),
            τ⁻¹ * (if N < n ∧ m * n ≤ x ∧ Nat.Coprime n m
                  ∧ (∀ q : ℕ, q.Prime → q ≤ Pz → ¬ q ∣ n)
                then Work.FITop.atilFIa (m * n) * ((m * n).divisors.card : ℝ) ^ 2 else 0) := by
          apply Finset.sum_le_sum
          intro n hn
          have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
          by_cases h : (N < n ∧ m * n ≤ x ∧ Nat.Coprime n m
                ∧ (∀ q : ℕ, q.Prime → q ≤ Pz → ¬ q ∣ n)) ∧ ¬((n.divisors.card : ℝ) ≤ τ)
          · rw [if_pos h, if_pos h.1]
            exact abs_term_le' C τ hτ hm hn1 (not_le.mp h.2)
          · rw [if_neg h]
            apply mul_nonneg hτinv
            by_cases hc : (N < n ∧ m * n ≤ x ∧ Nat.Coprime n m
                  ∧ (∀ q : ℕ, q.Prime → q ≤ Pz → ¬ q ∣ n))
            · rw [if_pos hc]
              exact mul_nonneg (Work.FITop.atilFIa_nonneg _) (sq_nonneg _)
            · rw [if_neg hc]
      _ = τ⁻¹ * ∑ n ∈ Finset.Icc 1 (2 * N),
            (if N < n ∧ m * n ≤ x ∧ Nat.Coprime n m
                  ∧ (∀ q : ℕ, q.Prime → q ≤ Pz → ¬ q ∣ n)
                then Work.FITop.atilFIa (m * n) * ((m * n).divisors.card : ℝ) ^ 2 else 0) := by
          rw [Finset.mul_sum]
      _ ≤ τ⁻¹ * ∑ n ∈ (Finset.Icc 1 x).filter (fun n => m * n ≤ x),
            Work.FITop.atilFIa (m * n) * ((m * n).divisors.card : ℝ) ^ 2 := by
          apply mul_le_mul_of_nonneg_left _ hτinv
          calc ∑ n ∈ Finset.Icc 1 (2 * N),
                (if N < n ∧ m * n ≤ x ∧ Nat.Coprime n m
                      ∧ (∀ q : ℕ, q.Prime → q ≤ Pz → ¬ q ∣ n)
                    then Work.FITop.atilFIa (m * n) * ((m * n).divisors.card : ℝ) ^ 2 else 0)
              ≤ ∑ n ∈ Finset.Icc 1 (2 * N),
                  (if m * n ≤ x
                    then Work.FITop.atilFIa (m * n) * ((m * n).divisors.card : ℝ) ^ 2 else 0) := by
                apply Finset.sum_le_sum
                intro n _
                by_cases hc : (N < n ∧ m * n ≤ x ∧ Nat.Coprime n m
                      ∧ (∀ q : ℕ, q.Prime → q ≤ Pz → ¬ q ∣ n))
                · rw [if_pos hc, if_pos hc.2.1]
                · rw [if_neg hc]
                  by_cases h2 : m * n ≤ x
                  · rw [if_pos h2]
                    exact mul_nonneg (Work.FITop.atilFIa_nonneg _) (sq_nonneg _)
                  · rw [if_neg h2]
            _ = ∑ n ∈ (Finset.Icc 1 (2 * N)).filter (fun n => m * n ≤ x),
                  Work.FITop.atilFIa (m * n) * ((m * n).divisors.card : ℝ) ^ 2 := by
                rw [← Finset.sum_filter]
            _ ≤ ∑ n ∈ (Finset.Icc 1 x).filter (fun n => m * n ≤ x),
                  Work.FITop.atilFIa (m * n) * ((m * n).divisors.card : ℝ) ^ 2 := by
                apply Finset.sum_le_sum_of_subset_of_nonneg
                · intro n hn
                  rw [Finset.mem_filter] at hn ⊢
                  obtain ⟨hnI, hmn⟩ := hn
                  rw [Finset.mem_Icc] at hnI ⊢
                  exact ⟨⟨hnI.1, le_trans (by simpa using Nat.mul_le_mul_right n hm) hmn⟩, hmn⟩
                · intro n _ _
                  exact mul_nonneg (Work.FITop.atilFIa_nonneg _) (sq_nonneg _)
  have hT : |∑ n ∈ Finset.Icc 1 (2 * N),
        (if N < n ∧ m * n ≤ x ∧ Nat.Coprime n m ∧ (∀ q : ℕ, q.Prime → q ≤ Pz → ¬ q ∣ n)
              ∧ ((n.divisors.card : ℝ) ≤ τ)
          then (ArithmeticFunction.moebius n : ℝ) * Work.FIPlan.gammaTrunc C n
            * Work.FITop.atilFIa (m * n) else 0)|
      ≤ |∑ n ∈ Finset.Icc 1 (2 * N),
        (if N < n ∧ m * n ≤ x ∧ Nat.Coprime n m ∧ (∀ q : ℕ, q.Prime → q ≤ Pz → ¬ q ∣ n)
          then (ArithmeticFunction.moebius n : ℝ) * Work.FIPlan.gammaTrunc C n
            * Work.FITop.atilFIa (m * n) else 0)|
        + |∑ n ∈ Finset.Icc 1 (2 * N),
            (if (N < n ∧ m * n ≤ x ∧ Nat.Coprime n m
                  ∧ (∀ q : ℕ, q.Prime → q ≤ Pz → ¬ q ∣ n)) ∧ ¬((n.divisors.card : ℝ) ≤ τ)
              then (ArithmeticFunction.moebius n : ℝ) * Work.FIPlan.gammaTrunc C n
                * Work.FITop.atilFIa (m * n) else 0)| := by
    have heq : (∑ n ∈ Finset.Icc 1 (2 * N),
        (if N < n ∧ m * n ≤ x ∧ Nat.Coprime n m ∧ (∀ q : ℕ, q.Prime → q ≤ Pz → ¬ q ∣ n)
              ∧ ((n.divisors.card : ℝ) ≤ τ)
          then (ArithmeticFunction.moebius n : ℝ) * Work.FIPlan.gammaTrunc C n
            * Work.FITop.atilFIa (m * n) else 0))
        = (∑ n ∈ Finset.Icc 1 (2 * N),
            (if N < n ∧ m * n ≤ x ∧ Nat.Coprime n m ∧ (∀ q : ℕ, q.Prime → q ≤ Pz → ¬ q ∣ n)
              then (ArithmeticFunction.moebius n : ℝ) * Work.FIPlan.gammaTrunc C n
                * Work.FITop.atilFIa (m * n) else 0))
          - (∑ n ∈ Finset.Icc 1 (2 * N),
              (if (N < n ∧ m * n ≤ x ∧ Nat.Coprime n m
                    ∧ (∀ q : ℕ, q.Prime → q ≤ Pz → ¬ q ∣ n)) ∧ ¬((n.divisors.card : ℝ) ≤ τ)
                then (ArithmeticFunction.moebius n : ℝ) * Work.FIPlan.gammaTrunc C n
                  * Work.FITop.atilFIa (m * n) else 0)) := by
      rw [hsplit]; ring
    rw [heq]
    simpa using abs_sub_le (∑ n ∈ Finset.Icc 1 (2 * N),
        (if N < n ∧ m * n ≤ x ∧ Nat.Coprime n m ∧ (∀ q : ℕ, q.Prime → q ≤ Pz → ¬ q ∣ n)
          then (ArithmeticFunction.moebius n : ℝ) * Work.FIPlan.gammaTrunc C n
            * Work.FITop.atilFIa (m * n) else 0)) 0
      (∑ n ∈ Finset.Icc 1 (2 * N),
            (if (N < n ∧ m * n ≤ x ∧ Nat.Coprime n m
                  ∧ (∀ q : ℕ, q.Prime → q ≤ Pz → ¬ q ∣ n)) ∧ ¬((n.divisors.card : ℝ) ≤ τ)
              then (ArithmeticFunction.moebius n : ℝ) * Work.FIPlan.gammaTrunc C n
                * Work.FITop.atilFIa (m * n) else 0))
  calc |∑ n ∈ Finset.Icc 1 (2 * N),
        (if N < n ∧ m * n ≤ x ∧ Nat.Coprime n m ∧ (∀ q : ℕ, q.Prime → q ≤ Pz → ¬ q ∣ n)
              ∧ ((n.divisors.card : ℝ) ≤ τ)
          then (ArithmeticFunction.moebius n : ℝ) * Work.FIPlan.gammaTrunc C n
            * Work.FITop.atilFIa (m * n) else 0)|
      ≤ |∑ n ∈ Finset.Icc 1 (2 * N),
        (if N < n ∧ m * n ≤ x ∧ Nat.Coprime n m ∧ (∀ q : ℕ, q.Prime → q ≤ Pz → ¬ q ∣ n)
          then (ArithmeticFunction.moebius n : ℝ) * Work.FIPlan.gammaTrunc C n
            * Work.FITop.atilFIa (m * n) else 0)|
        + |∑ n ∈ Finset.Icc 1 (2 * N),
            (if (N < n ∧ m * n ≤ x ∧ Nat.Coprime n m
                  ∧ (∀ q : ℕ, q.Prime → q ≤ Pz → ¬ q ∣ n)) ∧ ¬((n.divisors.card : ℝ) ≤ τ)
              then (ArithmeticFunction.moebius n : ℝ) * Work.FIPlan.gammaTrunc C n
                * Work.FITop.atilFIa (m * n) else 0)| := hT
    _ ≤ |∑ n ∈ Finset.Icc 1 (2 * N),
        (if N < n ∧ m * n ≤ x ∧ Nat.Coprime n m ∧ (∀ q : ℕ, q.Prime → q ≤ Pz → ¬ q ∣ n)
          then (ArithmeticFunction.moebius n : ℝ) * Work.FIPlan.gammaTrunc C n
            * Work.FITop.atilFIa (m * n) else 0)|
        + τ⁻¹ * ∑ n ∈ (Finset.Icc 1 x).filter (fun n => m * n ≤ x),
            Work.FITop.atilFIa (m * n) * ((m * n).divisors.card : ℝ) ^ 2 :=
        add_le_add_right htail _

/-! ## The reverse truncation lemma -/

/-- The *reverse* truncation bound: `BformPiTau` at a threshold `τ > 0` exceeds the untruncated
`BformPi` by at most `τ⁻¹ Σ_{l ≤ x} ã_l τ(l)³`.  (This is the mirror of `BformPi_trunc_le`.) -/
theorem BformPiTau_le_BformPi_add (x N Pz : ℕ) (C τ : ℝ) (hτ : 0 < τ) :
    Work.FITop4.BformPiTau x N Pz C τ ≤ Work.FITop.BformPi x N C Pz
      + τ⁻¹ * (∑ l ∈ Finset.Icc 1 x, Work.FITop.atilFIa l * ((l.divisors.card : ℝ) ^ 3)) := by
  have hτinv : 0 ≤ τ⁻¹ := inv_nonneg.mpr hτ.le
  have hS : (∑ l ∈ Finset.Icc 1 x, Work.FITop.atilFIa l * ((l.divisors.card : ℝ) ^ 3))
      = ∑ l ∈ Finset.Icc 1 x,
          ((l.divisors.card : ℝ)) * (Work.FITop.atilFIa l * ((l.divisors.card : ℝ) ^ 2)) := by
    apply Finset.sum_congr rfl
    intro l _
    ring
  have hTMR : (∑ m ∈ Finset.Icc 1 x, ∑ n ∈ (Finset.Icc 1 x).filter (fun n => m * n ≤ x),
        Work.FITop.atilFIa (m * n) * ((m * n).divisors.card : ℝ) ^ 2)
      ≤ ∑ l ∈ Finset.Icc 1 x,
          ((l.divisors.card : ℝ)) * (Work.FITop.atilFIa l * ((l.divisors.card : ℝ) ^ 2)) :=
    Work.FITop.TauMulReindex (g := fun l => Work.FITop.atilFIa l * ((l.divisors.card : ℝ) ^ 2))
      (fun l => mul_nonneg (Work.FITop.atilFIa_nonneg l) (sq_nonneg _)) x
  have hper : ∀ m ∈ Finset.Icc 1 x,
      |∑ n ∈ Finset.Icc 1 (2 * N),
          (if N < n ∧ m * n ≤ x ∧ Nat.Coprime n m ∧ (∀ q : ℕ, q.Prime → q ≤ Pz → ¬ q ∣ n)
                ∧ ((n.divisors.card : ℝ) ≤ τ)
            then (ArithmeticFunction.moebius n : ℝ) * Work.FIPlan.gammaTrunc C n
              * Work.FITop.atilFIa (m * n) else 0)|
        ≤ |∑ n ∈ Finset.Icc 1 (2 * N),
            (if N < n ∧ m * n ≤ x ∧ Nat.Coprime n m ∧ (∀ q : ℕ, q.Prime → q ≤ Pz → ¬ q ∣ n)
              then (ArithmeticFunction.moebius n : ℝ) * Work.FIPlan.gammaTrunc C n
                * Work.FITop.atilFIa (m * n) else 0)|
          + τ⁻¹ * ∑ n ∈ (Finset.Icc 1 x).filter (fun n => m * n ≤ x),
              Work.FITop.atilFIa (m * n) * ((m * n).divisors.card : ℝ) ^ 2 :=
    fun m hm => per_m_reverse x N Pz C τ hτ (Finset.mem_Icc.mp hm).1
  simp only [Work.FITop.BformPi, Work.FITop4.BformPiTau, hS]
  calc (∑ m ∈ Finset.Icc 1 x, |∑ n ∈ Finset.Icc 1 (2 * N),
          (if N < n ∧ m * n ≤ x ∧ Nat.Coprime n m ∧ (∀ q : ℕ, q.Prime → q ≤ Pz → ¬ q ∣ n)
                ∧ ((n.divisors.card : ℝ) ≤ τ)
            then (ArithmeticFunction.moebius n : ℝ) * Work.FIPlan.gammaTrunc C n
              * Work.FITop.atilFIa (m * n) else 0)|)
      ≤ (∑ m ∈ Finset.Icc 1 x, |∑ n ∈ Finset.Icc 1 (2 * N),
            (if N < n ∧ m * n ≤ x ∧ Nat.Coprime n m ∧ (∀ q : ℕ, q.Prime → q ≤ Pz → ¬ q ∣ n)
              then (ArithmeticFunction.moebius n : ℝ) * Work.FIPlan.gammaTrunc C n
                * Work.FITop.atilFIa (m * n) else 0)|)
          + τ⁻¹ * (∑ m ∈ Finset.Icc 1 x, ∑ n ∈ (Finset.Icc 1 x).filter (fun n => m * n ≤ x),
              Work.FITop.atilFIa (m * n) * ((m * n).divisors.card : ℝ) ^ 2) := by
        calc (∑ m ∈ Finset.Icc 1 x, |∑ n ∈ Finset.Icc 1 (2 * N),
              (if N < n ∧ m * n ≤ x ∧ Nat.Coprime n m ∧ (∀ q : ℕ, q.Prime → q ≤ Pz → ¬ q ∣ n)
                    ∧ ((n.divisors.card : ℝ) ≤ τ)
                then (ArithmeticFunction.moebius n : ℝ) * Work.FIPlan.gammaTrunc C n
                  * Work.FITop.atilFIa (m * n) else 0)|)
            ≤ ∑ m ∈ Finset.Icc 1 x,
                (|∑ n ∈ Finset.Icc 1 (2 * N),
                    (if N < n ∧ m * n ≤ x ∧ Nat.Coprime n m
                          ∧ (∀ q : ℕ, q.Prime → q ≤ Pz → ¬ q ∣ n)
                      then (ArithmeticFunction.moebius n : ℝ) * Work.FIPlan.gammaTrunc C n
                        * Work.FITop.atilFIa (m * n) else 0)|
                  + τ⁻¹ * ∑ n ∈ (Finset.Icc 1 x).filter (fun n => m * n ≤ x),
                      Work.FITop.atilFIa (m * n) * ((m * n).divisors.card : ℝ) ^ 2) :=
              Finset.sum_le_sum hper
          _ = (∑ m ∈ Finset.Icc 1 x, |∑ n ∈ Finset.Icc 1 (2 * N),
                (if N < n ∧ m * n ≤ x ∧ Nat.Coprime n m ∧ (∀ q : ℕ, q.Prime → q ≤ Pz → ¬ q ∣ n)
                  then (ArithmeticFunction.moebius n : ℝ) * Work.FIPlan.gammaTrunc C n
                    * Work.FITop.atilFIa (m * n) else 0)|)
              + τ⁻¹ * (∑ m ∈ Finset.Icc 1 x,
                  ∑ n ∈ (Finset.Icc 1 x).filter (fun n => m * n ≤ x),
                    Work.FITop.atilFIa (m * n) * ((m * n).divisors.card : ℝ) ^ 2) := by
              rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ (∑ m ∈ Finset.Icc 1 x, |∑ n ∈ Finset.Icc 1 (2 * N),
            (if N < n ∧ m * n ≤ x ∧ Nat.Coprime n m ∧ (∀ q : ℕ, q.Prime → q ≤ Pz → ¬ q ∣ n)
              then (ArithmeticFunction.moebius n : ℝ) * Work.FIPlan.gammaTrunc C n
                * Work.FITop.atilFIa (m * n) else 0)|)
          + τ⁻¹ * (∑ l ∈ Finset.Icc 1 x,
              ((l.divisors.card : ℝ)) * (Work.FITop.atilFIa l * ((l.divisors.card : ℝ) ^ 2))) :=
        add_le_add_right (mul_le_mul_of_nonneg_left hTMR hτinv) _

/-! ## The `τ`-reduction -/

theorem BformPiTau_tauReduce :
    ∃ c : ℝ, 0 < c ∧ ∃ x₀ : ℕ, ∀ (x N Pz : ℕ) (C τ : ℝ),
      x₀ ≤ x → 1 ≤ N → 1 ≤ C → 2 ≤ Pz →
      (Real.log (x : ℝ)) ^ (Work.FITop4.Asave + 124) ≤ τ →
      BformPiTau x N Pz C τ
        ≤ BformPiTau x N Pz C (Work.FITop4.tauOf x Work.FITop4.Asave)
          + c * Work.FITop.AcountAtil x
              * (Real.log (x : ℝ)) ^ (-(Work.FITop4.Asave - 200000)) := by
  obtain ⟨Cp, Xp, hCp, hp⟩ := Work.FITop4.Red5.AseqTauCubBound
  refine ⟨2 * (Cp : ℝ), by exact mul_pos (by norm_num) (by exact_mod_cast hCp), max Xp 3, ?_⟩
  intro x N Pz C τ hx hN hC hPz hτ
  have hxXp : Xp ≤ x := le_trans (le_max_left _ _) hx
  have hx3 : 3 ≤ x := le_trans (le_max_right _ _) hx
  -- `log x ≥ 1`
  have hL1 : (1 : ℝ) ≤ Real.log (x : ℝ) := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1)
      (le_trans (le_of_lt Real.exp_one_lt_three) (by exact_mod_cast hx3))
  have hLpos : 0 < Real.log (x : ℝ) := lt_of_lt_of_le zero_lt_one hL1
  have hL0 : 0 ≤ Real.log (x : ℝ) := le_of_lt hLpos
  -- positivity of the two thresholds
  have hbase_pos : 0 < (Real.log (x : ℝ)) ^ (Work.FITop4.Asave + 124) :=
    Real.rpow_pos_of_pos hLpos _
  have hτpos : 0 < τ := lt_of_lt_of_le hbase_pos hτ
  have hτ'pos : 0 < Work.FITop4.tauOf x Work.FITop4.Asave := by
    unfold Work.FITop4.tauOf
    exact Real.rpow_pos_of_pos hLpos _
  -- `Ã(x) ≥ 0`
  have hÃ0 : 0 ≤ Work.FITop.AcountAtil x := by
    rw [Work.FITop.AcountAtil, Submission.ASP.Acount, Nat.floor_natCast]
    exact Finset.sum_nonneg (fun n _ => Work.FITop.atilFIa_nonneg n)
  -- the two inverse bounds
  have hτinv_le : τ⁻¹ ≤ (Real.log (x : ℝ)) ^ (-(Work.FITop4.Asave + 124)) := by
    have h := inv_anti₀ hbase_pos hτ
    rwa [← Real.rpow_neg hL0 (Work.FITop4.Asave + 124)] at h
  have hτ'ge : (Real.log (x : ℝ)) ^ (Work.FITop4.Asave + 124)
      ≤ Work.FITop4.tauOf x Work.FITop4.Asave := by
    unfold Work.FITop4.tauOf
    apply Real.rpow_le_rpow_of_exponent_le hL1
    unfold Work.FITop4.Asave
    norm_num
  have hτ'inv_le : (Work.FITop4.tauOf x Work.FITop4.Asave)⁻¹
      ≤ (Real.log (x : ℝ)) ^ (-(Work.FITop4.Asave + 124)) := by
    have h := inv_anti₀ hbase_pos hτ'ge
    rwa [← Real.rpow_neg hL0 (Work.FITop4.Asave + 124)] at h
  have hsum_inv : τ⁻¹ + (Work.FITop4.tauOf x Work.FITop4.Asave)⁻¹
      ≤ 2 * (Real.log (x : ℝ)) ^ (-(Work.FITop4.Asave + 124)) := by
    linarith [hτinv_le, hτ'inv_le]
  -- the two truncation bounds
  have hrev := BformPiTau_le_BformPi_add x N Pz C τ hτpos
  have htrunc := BformPi_trunc_le x N Pz C (Work.FITop4.tauOf x Work.FITop4.Asave) hτ'pos
  set S : ℝ := ∑ l ∈ Finset.Icc 1 x, Work.FITop.atilFIa l * ((l.divisors.card : ℝ) ^ 3) with hSdef
  have h1 : Work.FITop4.BformPiTau x N Pz C τ
      ≤ Work.FITop4.BformPiTau x N Pz C (Work.FITop4.tauOf x Work.FITop4.Asave)
        + (τ⁻¹ + (Work.FITop4.tauOf x Work.FITop4.Asave)⁻¹) * S := by
    have hrev' : Work.FITop4.BformPiTau x N Pz C τ
        ≤ Work.FITop.BformPi x N C Pz + τ⁻¹ * S := hrev
    have htrunc' : Work.FITop.BformPi x N C Pz
        ≤ Work.FITop4.BformPiTau x N Pz C (Work.FITop4.tauOf x Work.FITop4.Asave)
          + (Work.FITop4.tauOf x Work.FITop4.Asave)⁻¹ * S := htrunc
    calc Work.FITop4.BformPiTau x N Pz C τ
        ≤ Work.FITop.BformPi x N C Pz + τ⁻¹ * S := hrev'
      _ ≤ (Work.FITop4.BformPiTau x N Pz C (Work.FITop4.tauOf x Work.FITop4.Asave)
            + (Work.FITop4.tauOf x Work.FITop4.Asave)⁻¹ * S) + τ⁻¹ * S :=
          add_le_add_left htrunc' _
      _ = Work.FITop4.BformPiTau x N Pz C (Work.FITop4.tauOf x Work.FITop4.Asave)
            + (τ⁻¹ + (Work.FITop4.tauOf x Work.FITop4.Asave)⁻¹) * S := by ring
  -- the polylogarithmic bound on `S`, in `rpow` form
  have hsumr : S ≤ (Cp : ℝ) * Work.FITop.AcountAtil x * (Real.log (x : ℝ)) ^ (131072 : ℝ) := by
    rw [hSdef]
    rw [Real.rpow_ofNat]
    exact hp x hxXp
  -- the final numerical bound
  have hS0 : 0 ≤ S := by
    rw [hSdef]
    exact Finset.sum_nonneg (fun l _ =>
      mul_nonneg (Work.FITop.atilFIa_nonneg l) (pow_nonneg (Nat.cast_nonneg _) _))
  have hprod0 : 0 ≤ (Cp : ℝ) * Work.FITop.AcountAtil x * (Real.log (x : ℝ)) ^ (131072 : ℝ) := by
    refine mul_nonneg (mul_nonneg (by exact_mod_cast hCp.le) hÃ0) ?_
    exact Real.rpow_nonneg hL0 _
  have hinv0 : 0 ≤ τ⁻¹ + (Work.FITop4.tauOf x Work.FITop4.Asave)⁻¹ :=
    add_nonneg (inv_nonneg.mpr hτpos.le) (inv_nonneg.mpr hτ'pos.le)
  have h2 : (τ⁻¹ + (Work.FITop4.tauOf x Work.FITop4.Asave)⁻¹) * S
      ≤ (2 * (Cp : ℝ)) * Work.FITop.AcountAtil x
          * (Real.log (x : ℝ)) ^ (-(Work.FITop4.Asave - 200000)) := by
    calc (τ⁻¹ + (Work.FITop4.tauOf x Work.FITop4.Asave)⁻¹) * S
        ≤ (τ⁻¹ + (Work.FITop4.tauOf x Work.FITop4.Asave)⁻¹)
            * ((Cp : ℝ) * Work.FITop.AcountAtil x * (Real.log (x : ℝ)) ^ (131072 : ℝ)) :=
          mul_le_mul_of_nonneg_left hsumr hinv0
      _ ≤ (2 * (Real.log (x : ℝ)) ^ (-(Work.FITop4.Asave + 124)))
            * ((Cp : ℝ) * Work.FITop.AcountAtil x * (Real.log (x : ℝ)) ^ (131072 : ℝ)) :=
          mul_le_mul_of_nonneg_right hsum_inv hprod0
      _ = (2 * (Cp : ℝ)) * Work.FITop.AcountAtil x
            * ((Real.log (x : ℝ)) ^ (-(Work.FITop4.Asave + 124))
                * (Real.log (x : ℝ)) ^ (131072 : ℝ)) := by ring
      _ ≤ (2 * (Cp : ℝ)) * Work.FITop.AcountAtil x
            * (Real.log (x : ℝ)) ^ (-(Work.FITop4.Asave - 200000)) := by
          apply mul_le_mul_of_nonneg_left _ (mul_nonneg (by norm_num) hÃ0)
          rw [← Real.rpow_add hLpos]
          apply Real.rpow_le_rpow_of_exponent_le hL1
          unfold Work.FITop4.Asave
          norm_num
  calc Work.FITop4.BformPiTau x N Pz C τ
      ≤ Work.FITop4.BformPiTau x N Pz C (Work.FITop4.tauOf x Work.FITop4.Asave)
        + (τ⁻¹ + (Work.FITop4.tauOf x Work.FITop4.Asave)⁻¹) * S := h1
    _ ≤ Work.FITop4.BformPiTau x N Pz C (Work.FITop4.tauOf x Work.FITop4.Asave)
        + (2 * (Cp : ℝ)) * Work.FITop.AcountAtil x
            * (Real.log (x : ℝ)) ^ (-(Work.FITop4.Asave - 200000)) :=
        add_le_add_right h2 _

end

end Work.FITop4.Red5
