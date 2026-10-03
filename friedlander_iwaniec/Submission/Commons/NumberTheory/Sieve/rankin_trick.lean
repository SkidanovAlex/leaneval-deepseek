import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.NumberTheory.SmoothNumbers

open scoped BigOperators

namespace Commons.NumberTheory.Sieve

theorem rankin_trick {f : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n)
    (hsq : ∀ n, Squarefree n → f n = ∏ p ∈ n.primeFactors, f p)
    {z y N : ℕ} (hy : 1 ≤ y) {ε : ℝ} (hε : 0 < ε) :
    (∑ n ∈ (Finset.range (N + 1)).filter
        (fun n => n ∈ Nat.smoothNumbers z ∧ Squarefree n ∧ y < n), f n)
      ≤ (y : ℝ) ^ (-ε) * ∏ p ∈ Nat.primesBelow z, (1 + (p : ℝ) ^ ε * f p) := by
  set F : Finset ℕ := (Finset.range (N + 1)).filter
      (fun n => n ∈ Nat.smoothNumbers z ∧ Squarefree n ∧ y < n) with hF
  set P : Finset ℕ := Nat.primesBelow z with hP
  have hypos : (0 : ℝ) < (y : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hy)
  have hFmem : ∀ n ∈ F, n ∈ Nat.smoothNumbers z ∧ Squarefree n ∧ y < n := by
    intro n hn
    rw [hF] at hn
    exact (Finset.mem_filter.mp hn).2
  -- Termwise Rankin inequality f n ≤ y⁻ᵋ (nᵋ f n).
  have hterm : ∀ n ∈ F, f n ≤ (y : ℝ) ^ (-ε) * ((n : ℝ) ^ ε * f n) := by
    intro n hn
    obtain ⟨_hsm, _hsf, hyn⟩ := hFmem n hn
    have hyle : (y : ℝ) ≤ (n : ℝ) := by exact_mod_cast (le_of_lt hyn)
    have hyε : (y : ℝ) ^ ε ≤ (n : ℝ) ^ ε := Real.rpow_le_rpow hypos.le hyle hε.le
    have hprod1 : (y : ℝ) ^ ε * (y : ℝ) ^ (-ε) = 1 := by
      rw [← Real.rpow_add hypos ε (-ε), add_neg_cancel, Real.rpow_zero]
    have hmul := mul_le_mul_of_nonneg_right hyε (Real.rpow_nonneg hypos.le (-ε))
    rw [hprod1] at hmul
    have hone : (1 : ℝ) ≤ (y : ℝ) ^ (-ε) * (n : ℝ) ^ ε := by
      rw [mul_comm]; exact hmul
    calc f n ≤ 1 * f n := by rw [one_mul]
      _ ≤ ((y : ℝ) ^ (-ε) * (n : ℝ) ^ ε) * f n := mul_le_mul_of_nonneg_right hone (hf n)
      _ = (y : ℝ) ^ (-ε) * ((n : ℝ) ^ ε * f n) := by ring
  -- For squarefree n, n^ε f n = ∏_{p | n} p^ε f p.
  have hterm2 : ∀ n ∈ F, (n : ℝ) ^ ε * f n = ∏ p ∈ n.primeFactors, ((p : ℝ) ^ ε * f p) := by
    intro n hn
    obtain ⟨_hsm, hsf, _hyn⟩ := hFmem n hn
    have hnprod : ∏ p ∈ n.primeFactors, p = n := Nat.prod_primeFactors_of_squarefree hsf
    have hnsplit : (n : ℝ) ^ ε = ∏ p ∈ n.primeFactors, (p : ℝ) ^ ε := by
      conv_lhs => rw [← hnprod]
      rw [Nat.cast_prod]
      exact (Real.finsetProd_rpow _ _ (fun p _ => Nat.cast_nonneg p) ε).symm
    calc (n : ℝ) ^ ε * f n
        = (∏ p ∈ n.primeFactors, (p : ℝ) ^ ε) * (∏ p ∈ n.primeFactors, f p) := by
            rw [hnsplit, hsq n hsf]
      _ = ∏ p ∈ n.primeFactors, ((p : ℝ) ^ ε * f p) := by rw [Finset.prod_mul_distrib]
  -- The prime-factor map is injective on the squarefree elements of F.
  have hinj : Set.InjOn (fun n : ℕ => n.primeFactors) F := by
    intro m hm n hn hmn
    have hmf : Squarefree m := (hFmem m hm).2.1
    have hnf : Squarefree n := (hFmem n hn).2.1
    have hmn' : m.primeFactors = n.primeFactors := hmn
    rw [← Nat.prod_primeFactors_of_squarefree hmf, hmn']
    exact Nat.prod_primeFactors_of_squarefree hnf
  have himage : (∑ t ∈ F.image (fun n : ℕ => n.primeFactors), ∏ p ∈ t, ((p : ℝ) ^ ε * f p))
      = ∑ n ∈ F, ∏ p ∈ n.primeFactors, ((p : ℝ) ^ ε * f p) := Finset.sum_image hinj
  have hsub : F.image (fun n : ℕ => n.primeFactors) ⊆ P.powerset := by
    intro t ht
    rw [Finset.mem_image] at ht
    obtain ⟨n, hn, rfl⟩ := ht
    exact Finset.mem_powerset.mpr
      (Nat.primeFactors_subset_of_mem_smoothNumbers (hFmem n hn).1)
  have hle : (∑ t ∈ F.image (fun n : ℕ => n.primeFactors), ∏ p ∈ t, ((p : ℝ) ^ ε * f p))
      ≤ ∑ t ∈ P.powerset, ∏ p ∈ t, ((p : ℝ) ^ ε * f p) := by
    refine Finset.sum_le_sum_of_subset_of_nonneg hsub (fun t _ _ => ?_)
    exact Finset.prod_nonneg
      (fun p _ => mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg p) ε) (hf p))
  have h3 : (∑ n ∈ F, (n : ℝ) ^ ε * f n) ≤ ∏ p ∈ P, (1 + (p : ℝ) ^ ε * f p) := by
    rw [Finset.sum_congr rfl (fun n hn => hterm2 n hn)]
    rw [← himage, Finset.prod_one_add]
    exact hle
  calc ∑ n ∈ F, f n
      ≤ ∑ n ∈ F, (y : ℝ) ^ (-ε) * ((n : ℝ) ^ ε * f n) := Finset.sum_le_sum hterm
    _ = (y : ℝ) ^ (-ε) * ∑ n ∈ F, (n : ℝ) ^ ε * f n := by rw [Finset.mul_sum]
    _ ≤ (y : ℝ) ^ (-ε) * ∏ p ∈ P, (1 + (p : ℝ) ^ ε * f p) :=
        mul_le_mul_of_nonneg_left h3 (Real.rpow_nonneg hypos.le (-ε))

end Commons.NumberTheory.Sieve