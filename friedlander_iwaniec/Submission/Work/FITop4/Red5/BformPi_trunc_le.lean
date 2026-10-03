/-
# `Submission.Work.FITop4.Red5.BformPi_trunc_le`

The `τ`-truncation (4.10) of the `Π`-restricted bilinear form:
`BformPi ≤ BformPiTau + τ⁻¹ Σ_{l≤x} ã_l τ(l)³`, i.e. dropping the inner terms with
`τ(n) > τ` (`n.divisors.card > τ`) loses at most `τ⁻¹ Σ_{l ≤ x} ã_l τ(l)³`.

The proof is elementary:

* `|Σ_n (if φ then f else 0)| ≤ |Σ_n (if φ ∧ τ(n) ≤ τ then f else 0)| + |tail|` (triangle
  inequality, after splitting the inner sum on the condition `τ(n) ≤ τ`);
* `|μ(n) γ(n;C) ã(mn)| ≤ τ(n) · ã(mn) ≤ τ(mn) · ã(mn)` for the tail, since `|μ| ≤ 1` and
  `|γ(n;C)| ≤ τ(n)`, and `τ(n) ≤ τ(mn)` whenever `n ∣ mn`;
* on the tail `τ < τ(n) ≤ τ(mn)`, so `τ(mn) · ã(mn) ≤ τ⁻¹ τ(mn)² ã(mn)`;
* the divisor-pair reindexing `Work.FITop.TauMulReindex` turns `Σ_m Σ_{n : mn ≤ x} g(mn)` into
  `Σ_{l ≤ x} τ(l) g(l)` with `g(l) = ã_l τ(l)²`.
-/
import Mathlib
import Submission.Work.FITop4.Defs4
import Submission.Work.FITop4.Red5.Vocab
import Submission.Work.FITop.TauMulReindex

set_option autoImplicit false

namespace Work.FITop4.Red5

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## The four basic factors -/

private lemma atilFIa_nonneg (n : ℕ) : 0 ≤ Work.FITop.atilFIa n := by
  unfold Work.FITop.atilFIa Submission.ASP.atil Submission.ASP.FIa
  positivity

private lemma moebius_cast_abs_le_one (n : ℕ) : |(ArithmeticFunction.moebius n : ℝ)| ≤ 1 := by
  rw [← Int.cast_abs]
  exact_mod_cast ArithmeticFunction.abs_moebius_le_one

private lemma gammaTrunc_abs_le_card (C : ℝ) (n : ℕ) :
    |Work.FIPlan.gammaTrunc C n| ≤ (n.divisors.card : ℝ) := by
  unfold Work.FIPlan.gammaTrunc
  calc |∑ d ∈ n.divisors.filter (fun d => ((d : ℕ) : ℝ) ≤ C),
          (ArithmeticFunction.moebius d : ℝ)|
      ≤ ∑ d ∈ n.divisors.filter (fun d => ((d : ℕ) : ℝ) ≤ C),
          |(ArithmeticFunction.moebius d : ℝ)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _d ∈ n.divisors.filter (fun d => ((d : ℕ) : ℝ) ≤ C), (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro d _
        exact moebius_cast_abs_le_one d
    _ = ((n.divisors.filter (fun d => ((d : ℕ) : ℝ) ≤ C)).card : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    _ ≤ (n.divisors.card : ℝ) := by
        exact_mod_cast Finset.card_filter_le n.divisors (fun d => ((d : ℕ) : ℝ) ≤ C)

private lemma divisors_card_mono {n m : ℕ} (_hn : n ≠ 0) (hm : m ≠ 0) (h : n ∣ m) :
    n.divisors.card ≤ m.divisors.card := by
  apply Finset.card_le_card
  intro b hb
  rw [Nat.mem_divisors] at hb ⊢
  exact ⟨dvd_trans hb.1 h, hm⟩

/-- On the tail (`τ < τ(n)`) the summand is bounded by `τ⁻¹ · ã_{mn} τ(mn)²`. -/
private lemma abs_term_le (C τ : ℝ) (hτ : 0 < τ) {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n)
    (hτn : τ < (n.divisors.card : ℝ)) :
    |(ArithmeticFunction.moebius n : ℝ) * Work.FIPlan.gammaTrunc C n
        * Work.FITop.atilFIa (m * n)|
      ≤ τ⁻¹ * (Work.FITop.atilFIa (m * n) * ((m * n).divisors.card : ℝ) ^ 2) := by
  have hn0 : n ≠ 0 := by omega
  have hmn0 : m * n ≠ 0 := by positivity
  have hdvd : n ∣ m * n := dvd_mul_left n m
  have hcard : (n.divisors.card : ℝ) ≤ ((m * n).divisors.card : ℝ) := by
    exact_mod_cast divisors_card_mono hn0 hmn0 hdvd
  have hã : 0 ≤ Work.FITop.atilFIa (m * n) := atilFIa_nonneg _
  have hγ : |Work.FIPlan.gammaTrunc C n| ≤ (n.divisors.card : ℝ) := gammaTrunc_abs_le_card C n
  have hμ : |(ArithmeticFunction.moebius n : ℝ)| ≤ 1 := moebius_cast_abs_le_one n
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

/-! ## The per-`m` bound -/

private lemma per_m_bound (x N Pz : ℕ) (C τ : ℝ) (hτ : 0 < τ) {m : ℕ} (hm : 1 ≤ m) :
    |∑ n ∈ Finset.Icc 1 (2 * N),
        (if N < n ∧ m * n ≤ x ∧ Nat.Coprime n m ∧ (∀ q : ℕ, q.Prime → q ≤ Pz → ¬ q ∣ n)
          then (ArithmeticFunction.moebius n : ℝ) * Work.FIPlan.gammaTrunc C n
            * Work.FITop.atilFIa (m * n) else 0)|
      ≤ |∑ n ∈ Finset.Icc 1 (2 * N),
        (if N < n ∧ m * n ≤ x ∧ Nat.Coprime n m ∧ (∀ q : ℕ, q.Prime → q ≤ Pz → ¬ q ∣ n)
              ∧ ((n.divisors.card : ℝ) ≤ τ)
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
  have htri : |∑ n ∈ Finset.Icc 1 (2 * N),
        (if N < n ∧ m * n ≤ x ∧ Nat.Coprime n m ∧ (∀ q : ℕ, q.Prime → q ≤ Pz → ¬ q ∣ n)
          then (ArithmeticFunction.moebius n : ℝ) * Work.FIPlan.gammaTrunc C n
            * Work.FITop.atilFIa (m * n) else 0)|
      ≤ |∑ n ∈ Finset.Icc 1 (2 * N),
          (if N < n ∧ m * n ≤ x ∧ Nat.Coprime n m ∧ (∀ q : ℕ, q.Prime → q ≤ Pz → ¬ q ∣ n)
                ∧ ((n.divisors.card : ℝ) ≤ τ)
            then (ArithmeticFunction.moebius n : ℝ) * Work.FIPlan.gammaTrunc C n
              * Work.FITop.atilFIa (m * n) else 0)|
        + |∑ n ∈ Finset.Icc 1 (2 * N),
            (if (N < n ∧ m * n ≤ x ∧ Nat.Coprime n m
                  ∧ (∀ q : ℕ, q.Prime → q ≤ Pz → ¬ q ∣ n)) ∧ ¬((n.divisors.card : ℝ) ≤ τ)
              then (ArithmeticFunction.moebius n : ℝ) * Work.FIPlan.gammaTrunc C n
                * Work.FITop.atilFIa (m * n) else 0)| := by
    rw [hsplit]; exact abs_add_le _ _
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
            exact abs_term_le C τ hτ hm hn1 (not_le.mp h.2)
          · rw [if_neg h]
            apply mul_nonneg hτinv
            by_cases hc : (N < n ∧ m * n ≤ x ∧ Nat.Coprime n m
                  ∧ (∀ q : ℕ, q.Prime → q ≤ Pz → ¬ q ∣ n))
            · rw [if_pos hc]
              exact mul_nonneg (atilFIa_nonneg _) (sq_nonneg _)
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
                    exact mul_nonneg (atilFIa_nonneg _) (sq_nonneg _)
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
                  exact mul_nonneg (atilFIa_nonneg _) (sq_nonneg _)
  calc |∑ n ∈ Finset.Icc 1 (2 * N),
        (if N < n ∧ m * n ≤ x ∧ Nat.Coprime n m ∧ (∀ q : ℕ, q.Prime → q ≤ Pz → ¬ q ∣ n)
          then (ArithmeticFunction.moebius n : ℝ) * Work.FIPlan.gammaTrunc C n
            * Work.FITop.atilFIa (m * n) else 0)|
      ≤ |∑ n ∈ Finset.Icc 1 (2 * N),
          (if N < n ∧ m * n ≤ x ∧ Nat.Coprime n m ∧ (∀ q : ℕ, q.Prime → q ≤ Pz → ¬ q ∣ n)
                ∧ ((n.divisors.card : ℝ) ≤ τ)
            then (ArithmeticFunction.moebius n : ℝ) * Work.FIPlan.gammaTrunc C n
              * Work.FITop.atilFIa (m * n) else 0)|
        + |∑ n ∈ Finset.Icc 1 (2 * N),
            (if (N < n ∧ m * n ≤ x ∧ Nat.Coprime n m
                  ∧ (∀ q : ℕ, q.Prime → q ≤ Pz → ¬ q ∣ n)) ∧ ¬((n.divisors.card : ℝ) ≤ τ)
              then (ArithmeticFunction.moebius n : ℝ) * Work.FIPlan.gammaTrunc C n
                * Work.FITop.atilFIa (m * n) else 0)| := htri
    _ ≤ |∑ n ∈ Finset.Icc 1 (2 * N),
          (if N < n ∧ m * n ≤ x ∧ Nat.Coprime n m ∧ (∀ q : ℕ, q.Prime → q ≤ Pz → ¬ q ∣ n)
                ∧ ((n.divisors.card : ℝ) ≤ τ)
            then (ArithmeticFunction.moebius n : ℝ) * Work.FIPlan.gammaTrunc C n
              * Work.FITop.atilFIa (m * n) else 0)|
        + τ⁻¹ * ∑ n ∈ (Finset.Icc 1 x).filter (fun n => m * n ≤ x),
            Work.FITop.atilFIa (m * n) * ((m * n).divisors.card : ℝ) ^ 2 :=
        add_le_add_right htail _

/-! ## The target -/

theorem BformPi_trunc_le (x N Pz : ℕ) (C τ : ℝ) (hτ : 0 < τ) :
    Work.FITop.BformPi x N C Pz ≤ Work.FITop4.BformPiTau x N Pz C τ
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
      (fun l => mul_nonneg (atilFIa_nonneg l) (sq_nonneg _)) x
  have hper : ∀ m ∈ Finset.Icc 1 x,
      |∑ n ∈ Finset.Icc 1 (2 * N),
          (if N < n ∧ m * n ≤ x ∧ Nat.Coprime n m ∧ (∀ q : ℕ, q.Prime → q ≤ Pz → ¬ q ∣ n)
            then (ArithmeticFunction.moebius n : ℝ) * Work.FIPlan.gammaTrunc C n
              * Work.FITop.atilFIa (m * n) else 0)|
        ≤ |∑ n ∈ Finset.Icc 1 (2 * N),
            (if N < n ∧ m * n ≤ x ∧ Nat.Coprime n m ∧ (∀ q : ℕ, q.Prime → q ≤ Pz → ¬ q ∣ n)
                  ∧ ((n.divisors.card : ℝ) ≤ τ)
              then (ArithmeticFunction.moebius n : ℝ) * Work.FIPlan.gammaTrunc C n
                * Work.FITop.atilFIa (m * n) else 0)|
          + τ⁻¹ * ∑ n ∈ (Finset.Icc 1 x).filter (fun n => m * n ≤ x),
              Work.FITop.atilFIa (m * n) * ((m * n).divisors.card : ℝ) ^ 2 :=
    fun m hm => per_m_bound x N Pz C τ hτ (Finset.mem_Icc.mp hm).1
  simp only [Work.FITop.BformPi, Work.FITop4.BformPiTau, hS]
  calc (∑ m ∈ Finset.Icc 1 x, |∑ n ∈ Finset.Icc 1 (2 * N),
          (if N < n ∧ m * n ≤ x ∧ Nat.Coprime n m ∧ (∀ q : ℕ, q.Prime → q ≤ Pz → ¬ q ∣ n)
            then (ArithmeticFunction.moebius n : ℝ) * Work.FIPlan.gammaTrunc C n
              * Work.FITop.atilFIa (m * n) else 0)|)
      ≤ (∑ m ∈ Finset.Icc 1 x, |∑ n ∈ Finset.Icc 1 (2 * N),
            (if N < n ∧ m * n ≤ x ∧ Nat.Coprime n m ∧ (∀ q : ℕ, q.Prime → q ≤ Pz → ¬ q ∣ n)
                  ∧ ((n.divisors.card : ℝ) ≤ τ)
              then (ArithmeticFunction.moebius n : ℝ) * Work.FIPlan.gammaTrunc C n
                * Work.FITop.atilFIa (m * n) else 0)|)
          + τ⁻¹ * (∑ m ∈ Finset.Icc 1 x, ∑ n ∈ (Finset.Icc 1 x).filter (fun n => m * n ≤ x),
              Work.FITop.atilFIa (m * n) * ((m * n).divisors.card : ℝ) ^ 2) := by
        calc (∑ m ∈ Finset.Icc 1 x, |∑ n ∈ Finset.Icc 1 (2 * N),
              (if N < n ∧ m * n ≤ x ∧ Nat.Coprime n m ∧ (∀ q : ℕ, q.Prime → q ≤ Pz → ¬ q ∣ n)
                then (ArithmeticFunction.moebius n : ℝ) * Work.FIPlan.gammaTrunc C n
                  * Work.FITop.atilFIa (m * n) else 0)|)
            ≤ ∑ m ∈ Finset.Icc 1 x,
                (|∑ n ∈ Finset.Icc 1 (2 * N),
                    (if N < n ∧ m * n ≤ x ∧ Nat.Coprime n m
                          ∧ (∀ q : ℕ, q.Prime → q ≤ Pz → ¬ q ∣ n) ∧ ((n.divisors.card : ℝ) ≤ τ)
                      then (ArithmeticFunction.moebius n : ℝ) * Work.FIPlan.gammaTrunc C n
                        * Work.FITop.atilFIa (m * n) else 0)|
                  + τ⁻¹ * ∑ n ∈ (Finset.Icc 1 x).filter (fun n => m * n ≤ x),
                      Work.FITop.atilFIa (m * n) * ((m * n).divisors.card : ℝ) ^ 2) :=
              Finset.sum_le_sum hper
          _ = (∑ m ∈ Finset.Icc 1 x, |∑ n ∈ Finset.Icc 1 (2 * N),
                (if N < n ∧ m * n ≤ x ∧ Nat.Coprime n m
                      ∧ (∀ q : ℕ, q.Prime → q ≤ Pz → ¬ q ∣ n) ∧ ((n.divisors.card : ℝ) ≤ τ)
                  then (ArithmeticFunction.moebius n : ℝ) * Work.FIPlan.gammaTrunc C n
                    * Work.FITop.atilFIa (m * n) else 0)|)
              + τ⁻¹ * (∑ m ∈ Finset.Icc 1 x,
                  ∑ n ∈ (Finset.Icc 1 x).filter (fun n => m * n ≤ x),
                    Work.FITop.atilFIa (m * n) * ((m * n).divisors.card : ℝ) ^ 2) := by
              rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ (∑ m ∈ Finset.Icc 1 x, |∑ n ∈ Finset.Icc 1 (2 * N),
            (if N < n ∧ m * n ≤ x ∧ Nat.Coprime n m ∧ (∀ q : ℕ, q.Prime → q ≤ Pz → ¬ q ∣ n)
                  ∧ ((n.divisors.card : ℝ) ≤ τ)
              then (ArithmeticFunction.moebius n : ℝ) * Work.FIPlan.gammaTrunc C n
                * Work.FITop.atilFIa (m * n) else 0)|)
          + τ⁻¹ * (∑ l ∈ Finset.Icc 1 x,
              ((l.divisors.card : ℝ)) * (Work.FITop.atilFIa l * ((l.divisors.card : ℝ) ^ 2))) :=
        add_le_add_right (mul_le_mul_of_nonneg_left hTMR hτinv) _

end

end Work.FITop4.Red5
