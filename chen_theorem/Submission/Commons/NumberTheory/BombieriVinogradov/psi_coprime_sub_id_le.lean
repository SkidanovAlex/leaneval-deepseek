import Mathlib
import Submission.Commons.NumberTheory.Goldbach.sum_vonMangoldt_not_coprime

namespace Commons.NumberTheory.BombieriVinogradov

open Finset

theorem psi_coprime_sub_id_le (q : ℕ) [NeZero q] (x : ℕ) :
    |(∑ n ∈ (Finset.range (x + 1)).filter (fun n => Nat.Coprime n q),
        ArithmeticFunction.vonMangoldt n) - (x : ℝ)|
      ≤ |(∑ n ∈ (Finset.range (x + 1)), ArithmeticFunction.vonMangoldt n) - (x : ℝ)|
        + (q.primeFactors.card : ℝ) * Real.log ((x : ℝ) + 2) := by
  classical
  have hz : ArithmeticFunction.vonMangoldt 0 = 0 := by
    rw [ArithmeticFunction.vonMangoldt_eq_zero_iff, isPrimePow_nat_iff]
    rintro ⟨p, k, hp, hk, hpk⟩
    have : 0 < p ^ k := pow_pos hp.pos k
    omega
  have hsplit := Finset.sum_filter_add_sum_filter_not (Finset.range (x + 1))
      (fun n => Nat.Coprime n q) (fun n => ArithmeticFunction.vonMangoldt n)
  have hT_nonneg :
      0 ≤ ∑ n ∈ (Finset.range (x + 1)).filter (fun n => ¬ Nat.Coprime n q),
            ArithmeticFunction.vonMangoldt n :=
    Finset.sum_nonneg (fun n _ => ArithmeticFunction.vonMangoldt_nonneg)
  have hTbound :
      (∑ n ∈ (Finset.range (x + 1)).filter (fun n => ¬ Nat.Coprime n q),
            ArithmeticFunction.vonMangoldt n)
        ≤ (q.primeFactors.card : ℝ) * Real.log ((x : ℝ) + 2) := by
    have hT_eq_Icc :
        (∑ n ∈ (Finset.range (x + 1)).filter (fun n => ¬ Nat.Coprime n q),
            ArithmeticFunction.vonMangoldt n)
          = (∑ n ∈ (Finset.Icc 1 x).filter (fun n => ¬ Nat.Coprime n q),
              ArithmeticFunction.vonMangoldt n) := by
      symm
      refine Finset.sum_subset ?_ ?_
      · intro n hn
        rw [Finset.mem_filter] at hn ⊢
        obtain ⟨hnIcc, hn2⟩ := hn
        exact ⟨Finset.mem_range.mpr (by have := (Finset.mem_Icc.mp hnIcc).2; omega), hn2⟩
      · intro n hn hnnot
        rw [Finset.mem_filter] at hn
        obtain ⟨hnrange, hn2⟩ := hn
        have hn0 : n = 0 := by
          by_contra hne
          apply hnnot
          rw [Finset.mem_filter]
          exact ⟨Finset.mem_Icc.mpr
            ⟨Nat.one_le_iff_ne_zero.mpr hne, Nat.lt_succ_iff.mp (Finset.mem_range.mp hnrange)⟩, hn2⟩
        rw [hn0, hz]
    rw [hT_eq_Icc, Commons.NumberTheory.Goldbach.sum_vonMangoldt_not_coprime q x]
    have hlog_nonneg : 0 ≤ Real.log ((x : ℝ) + 2) := by
      apply Real.log_nonneg
      have : (0 : ℝ) ≤ x := Nat.cast_nonneg x
      linarith
    have hterm : ∀ p ∈ (Finset.Icc 1 x).filter (fun p => p.Prime ∧ p ∣ q),
        ((Nat.log p x : ℕ) : ℝ) * Real.log (p : ℝ) ≤ Real.log ((x : ℝ) + 2) := by
      intro p hp
      rw [Finset.mem_filter, Finset.mem_Icc] at hp
      obtain ⟨⟨hp1, hpx⟩, hpprime, hpdvd⟩ := hp
      have hp2 : 2 ≤ p := hpprime.two_le
      have hx2 : 2 ≤ x := le_trans hp2 hpx
      have hpk : p ^ Nat.log p x ≤ x := Nat.pow_log_le_self p (by omega)
      calc ((Nat.log p x : ℕ) : ℝ) * Real.log (p : ℝ)
          = Real.log ((p : ℝ) ^ Nat.log p x) := (Real.log_pow (p : ℝ) (Nat.log p x)).symm
        _ = Real.log (((p ^ Nat.log p x : ℕ) : ℝ)) := by rw [Nat.cast_pow]
        _ ≤ Real.log ((x : ℝ)) := by
              apply Real.log_le_log
              · exact_mod_cast pow_pos hpprime.pos (Nat.log p x)
              · exact_mod_cast hpk
        _ ≤ Real.log ((x : ℝ) + 2) := by
              apply Real.log_le_log
              · exact_mod_cast (show 0 < x by omega)
              · linarith
    have hRsub : (Finset.Icc 1 x).filter (fun p => p.Prime ∧ p ∣ q) ⊆ q.primeFactors := by
      intro p hp
      rw [Finset.mem_filter] at hp
      exact Nat.mem_primeFactors.mpr ⟨hp.2.1, hp.2.2, NeZero.ne q⟩
    calc (∑ p ∈ (Finset.Icc 1 x).filter (fun p => p.Prime ∧ p ∣ q),
              ((Nat.log p x : ℕ) : ℝ) * Real.log (p : ℝ))
        ≤ ∑ _p ∈ (Finset.Icc 1 x).filter (fun p => p.Prime ∧ p ∣ q),
              Real.log ((x : ℝ) + 2) := Finset.sum_le_sum hterm
      _ = (((Finset.Icc 1 x).filter (fun p => p.Prime ∧ p ∣ q)).card : ℝ)
              * Real.log ((x : ℝ) + 2) := by
            rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (q.primeFactors.card : ℝ) * Real.log ((x : ℝ) + 2) := by
            apply mul_le_mul_of_nonneg_right _ hlog_nonneg
            exact_mod_cast Finset.card_le_card hRsub
  have hdiff :
      (∑ n ∈ (Finset.range (x + 1)).filter (fun n => Nat.Coprime n q),
            ArithmeticFunction.vonMangoldt n) - (x : ℝ)
        = ((∑ n ∈ Finset.range (x + 1), ArithmeticFunction.vonMangoldt n) - (x : ℝ))
          - (∑ n ∈ (Finset.range (x + 1)).filter (fun n => ¬ Nat.Coprime n q),
              ArithmeticFunction.vonMangoldt n) := by
    linarith [hsplit]
  rw [hdiff]
  calc |((∑ n ∈ Finset.range (x + 1), ArithmeticFunction.vonMangoldt n) - (x : ℝ)) -
          (∑ n ∈ (Finset.range (x + 1)).filter (fun n => ¬ Nat.Coprime n q),
              ArithmeticFunction.vonMangoldt n)|
      = |((∑ n ∈ Finset.range (x + 1), ArithmeticFunction.vonMangoldt n) - (x : ℝ)) +
          (-(∑ n ∈ (Finset.range (x + 1)).filter (fun n => ¬ Nat.Coprime n q),
              ArithmeticFunction.vonMangoldt n))| := by
            rw [sub_eq_add_neg]
    _ ≤ |(∑ n ∈ Finset.range (x + 1), ArithmeticFunction.vonMangoldt n) - (x : ℝ)| +
          |-(∑ n ∈ (Finset.range (x + 1)).filter (fun n => ¬ Nat.Coprime n q),
              ArithmeticFunction.vonMangoldt n)| := abs_add_le _ _
    _ = |(∑ n ∈ Finset.range (x + 1), ArithmeticFunction.vonMangoldt n) - (x : ℝ)| +
          (∑ n ∈ (Finset.range (x + 1)).filter (fun n => ¬ Nat.Coprime n q),
              ArithmeticFunction.vonMangoldt n) := by
            rw [abs_neg, abs_of_nonneg hT_nonneg]
    _ ≤ |(∑ n ∈ Finset.range (x + 1), ArithmeticFunction.vonMangoldt n) - (x : ℝ)| +
          (q.primeFactors.card : ℝ) * Real.log ((x : ℝ) + 2) :=
            (by linarith [hTbound])

end Commons.NumberTheory.BombieriVinogradov
