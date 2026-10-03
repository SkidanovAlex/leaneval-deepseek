import Mathlib
import Submission.Work.FITop.Defs
import Submission.ASP.S30
import Submission.Commons.NumberTheory.FriedlanderIwaniec.Ad_le_tau_sq_div_of_cubefree

set_option maxHeartbeats 1600000

namespace Work.FITop

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- `ã_n ≥ 0` for the Friedlander–Iwaniec sequence. -/
private lemma atilFIa_nonneg (n : ℕ) : 0 ≤ atilFIa n := by
  rw [Work.FITop.atilFIa, Submission.ASP.atil, Submission.ASP.FIa]
  positivity

/-- `Ã(x) ≥ 1` for `x ≥ 1` (the index `1` contributes `a_1 ≥ 1`). -/
private lemma one_le_AcountAtil {x : ℕ} (hx : 1 ≤ x) : 1 ≤ AcountAtil x := by
  rw [Work.FITop.AcountAtil, Submission.ASP.Acount, Nat.floor_natCast]
  have hmem : (1 : ℕ) ∈ Finset.Icc 1 x := Finset.mem_Icc.mpr ⟨le_rfl, hx⟩
  have hle : atilFIa 1 ≤ ∑ n ∈ Finset.Icc 1 x, atilFIa n :=
    Finset.single_le_sum (fun i _ => atilFIa_nonneg i) hmem
  have h1 : 1 ≤ atilFIa 1 := by
    rw [Work.FITop.atilFIa, Submission.ASP.atil, Submission.ASP.FIa]
    have hmu : ((ArithmeticFunction.moebius 1 : ℝ)) ^ 2 = 1 := by
      norm_num [ArithmeticFunction.moebius_apply_one]
    rw [hmu, one_mul]
    have := Submission.ASP.an_one_pos'
    exact_mod_cast this
  linarith

/-- The `ℓ`-sum of `ã(bℓ)` is at most the congruence sum `A_b(x)`. -/
private lemma sum_le_Ad (b x : ℕ) (hb : 1 ≤ b) :
    (∑ ℓ ∈ Finset.Icc 1 x, (if b * ℓ ≤ x then atilFIa (b * ℓ) else 0))
      ≤ (Submission.Ad b x : ℝ) := by
  classical
  set T : Finset ℕ := (Finset.Icc 1 x).filter (fun ℓ => b * ℓ ≤ x) with hT
  have hEq : (∑ ℓ ∈ Finset.Icc 1 x, (if b * ℓ ≤ x then atilFIa (b * ℓ) else 0))
      = ∑ ℓ ∈ T, atilFIa (b * ℓ) := by
    rw [hT, Finset.sum_filter]
  rw [hEq]
  have hb0 : 0 < b := hb
  calc ∑ ℓ ∈ T, atilFIa (b * ℓ)
      ≤ ∑ ℓ ∈ T, (Submission.an (b * ℓ) : ℝ) := by
        apply Finset.sum_le_sum
        intro ℓ _
        rw [Work.FITop.atilFIa, Submission.ASP.atil, Submission.ASP.FIa]
        have h1 : ((ArithmeticFunction.moebius (b * ℓ) : ℝ)) ^ 2 ≤ 1 := by
          rw [Submission.ASP.moebius_sq_cast]; split <;> norm_num
        have h2 : (0 : ℝ) ≤ (Submission.an (b * ℓ) : ℝ) := Nat.cast_nonneg _
        calc ((ArithmeticFunction.moebius (b * ℓ) : ℝ)) ^ 2 * (Submission.an (b * ℓ) : ℝ)
            ≤ 1 * (Submission.an (b * ℓ) : ℝ) := mul_le_mul_of_nonneg_right h1 h2
          _ = (Submission.an (b * ℓ) : ℝ) := one_mul _
    _ = ∑ n ∈ T.image (fun ℓ => b * ℓ), (Submission.an n : ℝ) := by
        refine (Finset.sum_image (f := fun n : ℕ => (Submission.an n : ℝ)) ?_).symm
        intro ℓ _ ℓ' _ heq
        exact Nat.mul_left_cancel hb0 heq
    _ ≤ ∑ n ∈ (Finset.range (x + 1)).filter (fun n => b ∣ n), (Submission.an n : ℝ) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro n hn
          obtain ⟨ℓ, hℓ, rfl⟩ := Finset.mem_image.mp hn
          rw [hT, Finset.mem_filter] at hℓ
          rw [Finset.mem_filter, Finset.mem_range]
          exact ⟨by omega, dvd_mul_right b ℓ⟩
        · intro n _ _
          exact Nat.cast_nonneg _
    _ = (Submission.Ad b x : ℝ) := by
        rw [Submission.Ad, Nat.cast_sum]

theorem AtilCongruenceSum :
    ∃ C X₀ : ℕ, 0 < C ∧ ∀ b x : ℕ, X₀ ≤ x → 1 ≤ b → b * b ≤ x →
      (∑ ℓ ∈ Finset.Icc 1 x, (if b * ℓ ≤ x then Work.FITop.atilFIa (b * ℓ) else 0))
        ≤ C * ((((b.divisors.card : ℝ))^2) / (b:ℝ)) * Work.FITop.AcountAtil x := by
  obtain ⟨C₁, hC₁pos, hAdle⟩ :=
    Commons.NumberTheory.FriedlanderIwaniec.Ad_le_tau_sq_div_of_cubefree
  obtain ⟨XA, hAseq⟩ := Submission.ASP.FI_Aseq_le_const_mul_Atil
  set K : ℝ := 2 / Submission.ASP.Gprod Submission.ASP.FIg with hKdef
  have hKpos : 0 < K := by
    rw [hKdef]
    exact div_pos (by norm_num) Submission.ASP.Gprod_FIg_pos
  set Cn : ℕ := ⌈C₁ * (K + 1)⌉₊ + 1 with hCn_def
  have hCge : C₁ * (K + 1) ≤ (Cn : ℝ) := by
    rw [hCn_def]
    push_cast
    have h := Nat.le_ceil (C₁ * (K + 1))
    linarith
  refine ⟨Cn, max XA 1, ?_, ?_⟩
  · rw [hCn_def]; positivity
  intro b x hx hb hbsq
  have hx1 : 1 ≤ x := le_trans (le_max_right _ _) hx
  have hxXA : XA ≤ x := le_trans (le_max_left _ _) hx
  have hb0 : 0 < b := hb
  have htau_nn : 0 ≤ ((b.divisors.card : ℝ)) ^ 2 / (b : ℝ) :=
    div_nonneg (sq_nonneg _) (Nat.cast_nonneg b)
  have hAtil_nn : 0 ≤ AcountAtil x := le_trans (by norm_num) (one_le_AcountAtil hx1)
  have hAseq_le : (Submission.Aseq x : ℝ) ≤ (K + 1) * AcountAtil x := by
    have h1 : Submission.ASP.Acount Submission.ASP.FIa (x : ℝ) ≤ K * AcountAtil x := by
      have h := hAseq x hxXA
      rw [hKdef]
      rw [show AcountAtil x
            = Submission.ASP.Acount (Submission.ASP.atil Submission.ASP.FIa) (x : ℝ) from rfl]
      exact h
    have h2 : Submission.ASP.Acount Submission.ASP.FIa (x : ℝ) = (Submission.Aseq x : ℝ) - 1 :=
      Submission.ASP.FI_Acount_eq x
    have h3 : (1 : ℝ) ≤ AcountAtil x := one_le_AcountAtil hx1
    linarith [h1, h2, h3, hKpos]
  have hS := sum_le_Ad b x hb
  by_cases hsf : Squarefree b
  · have hcube : ∀ p : ℕ, p.Prime → ¬ p ^ 3 ∣ b := by
      intro p hp hp3
      have h2 : p * p ∣ b := dvd_trans (by exact ⟨p, by ring⟩) hp3
      exact (Nat.squarefree_iff_prime_squarefree.mp hsf) p hp h2
    have hAdb : (Submission.Ad b x : ℝ)
        ≤ C₁ * (((b.divisors.card : ℝ)) ^ 2 / (b : ℝ)) * (Submission.Aseq x : ℝ) :=
      hAdle b x hb hcube (by rw [pow_two]; exact hbsq)
    calc (∑ ℓ ∈ Finset.Icc 1 x, (if b * ℓ ≤ x then atilFIa (b * ℓ) else 0))
        ≤ (Submission.Ad b x : ℝ) := hS
      _ ≤ C₁ * (((b.divisors.card : ℝ)) ^ 2 / (b : ℝ)) * (Submission.Aseq x : ℝ) := hAdb
      _ ≤ C₁ * (((b.divisors.card : ℝ)) ^ 2 / (b : ℝ)) * ((K + 1) * AcountAtil x) :=
          mul_le_mul_of_nonneg_left hAseq_le (mul_nonneg hC₁pos.le htau_nn)
      _ = (C₁ * (K + 1)) * (((b.divisors.card : ℝ)) ^ 2 / (b : ℝ)) * AcountAtil x := by ring
      _ ≤ (Cn : ℝ) * (((b.divisors.card : ℝ)) ^ 2 / (b : ℝ)) * AcountAtil x :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCge htau_nn) hAtil_nn
  · have hzero : ∀ ℓ ∈ Finset.Icc 1 x,
        (if b * ℓ ≤ x then atilFIa (b * ℓ) else 0) = 0 := by
      intro ℓ _
      by_cases h : b * ℓ ≤ x
      · rw [if_pos h]
        rw [Work.FITop.atilFIa, Submission.ASP.atil, Submission.ASP.FIa]
        have hnsf : ¬ Squarefree (b * ℓ) := fun hs =>
          hsf (Squarefree.squarefree_of_dvd (dvd_mul_right b ℓ) hs)
        rw [Submission.ASP.moebius_sq_cast, if_neg hnsf]
        ring
      · rw [if_neg h]
    rw [Finset.sum_eq_zero hzero]
    have hCn : (0 : ℝ) ≤ (Cn : ℝ) := Nat.cast_nonneg _
    have : (0 : ℝ) ≤ (Cn : ℝ) * ((((b.divisors.card : ℝ)) ^ 2) / (b : ℝ)) * AcountAtil x :=
      mul_nonneg (mul_nonneg hCn htau_nn) hAtil_nn
    linarith

end

end Work.FITop
