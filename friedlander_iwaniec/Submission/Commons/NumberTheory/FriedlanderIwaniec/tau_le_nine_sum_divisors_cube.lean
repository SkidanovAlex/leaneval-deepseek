import Mathlib
import Submission.Commons.NumberTheory.FriedlanderIwaniec.tau_cube_sum_eq_sq_sum
import Submission.Commons.NumberTheory.FriedlanderIwaniec.tau3_le_three_mul_sum

namespace Commons.NumberTheory.FriedlanderIwaniec

open Finset

/-- The divisor-count function is submultiplicative. -/
lemma card_divisors_mul_le (m n : ℕ) :
    (m * n).divisors.card ≤ m.divisors.card * n.divisors.card := by
  rw [Nat.divisors_mul]
  exact Finset.card_mul_le

lemma tau_le_nine_sum_divisors_cube {n : ℕ} (hn : 1 ≤ n) :
    (Nat.divisors n).card ≤
      9 * ((Nat.divisors n).filter (fun d => d ^ 3 ≤ n)).sum
        (fun d => (Nat.divisors d).card) := by
  have hn0 : n ≠ 0 := by omega
  set D : Finset ℕ := Nat.divisors n with hD
  set T : Finset ℕ := D.filter (fun d => d ^ 3 ≤ n) with hT
  have hTD : T ⊆ D := by rw [hT]; exact Finset.filter_subset _ _
  have hmemD : ∀ d ∈ D, d ∣ n := by
    intro d hd; rw [hD] at hd; exact (Nat.mem_divisors.mp hd).1
  have hneD : ∀ d ∈ D, d ≠ 0 := by
    intro d hd; rw [hD] at hd; exact (Nat.pos_of_mem_divisors hd).ne'
  have hmemT : ∀ d ∈ T, d ∈ D ∧ d ^ 3 ≤ n := by
    intro d hd; rw [hT] at hd; exact Finset.mem_filter.mp hd
  have h1D : (1 : ℕ) ∈ D := by rw [hD]; exact Nat.one_mem_divisors.mpr hn0
  have h1T : (1 : ℕ) ∈ T := by
    rw [hT]; exact Finset.mem_filter.mpr ⟨h1D, by simpa using hn⟩
  have hB : ∑ d ∈ D, d.divisors.card ≤ 3 * ∑ d ∈ T, (n / d).divisors.card := by
    rw [hT, hD]
    exact tau3_le_three_mul_sum hn
  let t3 : ℚ := ∑ d ∈ D, (d.divisors.card : ℚ)
  let Sq : ℚ := ∑ d ∈ T, (d.divisors.card : ℚ)
  let Wq : ℚ := ∑ d ∈ T, ((n / d).divisors.card : ℚ)
  let A : ℚ := ∑ d ∈ D, (((n / d).divisors.card : ℚ) ^ 2) / (d.divisors.card : ℚ)
  have hdpos : ∀ d ∈ D, (0 : ℚ) < (d.divisors.card : ℚ) := by
    intro d hd
    exact_mod_cast Finset.card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr (hneD d hd)⟩
  -- (P2)
  have hP2 : t3 ≤ 3 * Wq := by
    simp only [t3, Wq]
    exact_mod_cast hB
  -- (P3) Cauchy-Schwarz
  have hSqpos : (0 : ℚ) < Sq := by
    simp only [Sq]
    exact Finset.sum_pos' (fun d _ => Nat.cast_nonneg _) ⟨1, h1T, by simp⟩
  have hTitu := Finset.sq_sum_div_le_sum_sq_div T
      (fun d => ((n / d).divisors.card : ℚ)) (fun d hd => hdpos d (hmemT d hd).1)
  have hA' : ∑ d ∈ T, (((n / d).divisors.card : ℚ) ^ 2) / (d.divisors.card : ℚ) ≤ A := by
    simp only [A]
    exact Finset.sum_le_sum_of_subset_of_nonneg hTD
      (fun d _ _ => div_nonneg (sq_nonneg _) (Nat.cast_nonneg _))
  have hP3 : Wq ^ 2 ≤ A * Sq := by
    have h := hTitu
    simp only [Wq, Sq] at h hSqpos ⊢
    rw [div_le_iff₀ hSqpos] at h
    calc (∑ d ∈ T, ((n / d).divisors.card : ℚ)) ^ 2
        ≤ (∑ d ∈ T, (((n / d).divisors.card : ℚ) ^ 2) / (d.divisors.card : ℚ))
            * (∑ d ∈ T, (d.divisors.card : ℚ)) := h
      _ ≤ A * (∑ d ∈ T, (d.divisors.card : ℚ)) :=
          mul_le_mul_of_nonneg_right hA' (Finset.sum_nonneg (fun d _ => Nat.cast_nonneg _))
  -- (P4)
  have hP4 : ((D.card : ℕ) : ℚ) * A ≤ t3 ^ 2 := by
    have hterm : ∀ d ∈ D,
        ((D.card : ℕ) : ℚ) * ((((n / d).divisors.card : ℚ) ^ 2) / (d.divisors.card : ℚ))
          ≤ ((n / d).divisors.card : ℚ) ^ 3 := by
      intro d hd
      have hdvd : d ∣ n := hmemD d hd
      have hdp : (0 : ℚ) < (d.divisors.card : ℚ) := hdpos d hd
      have hsub : (D.card : ℕ) ≤ d.divisors.card * (n / d).divisors.card := by
        have hn_eq : n = d * (n / d) := (Nat.mul_div_cancel' hdvd).symm
        rw [hD]
        conv_lhs => rw [hn_eq]
        exact card_divisors_mul_le d (n / d)
      have hcast : ((D.card : ℕ) : ℚ)
          ≤ ((d.divisors.card : ℕ) : ℚ) * (((n / d).divisors.card : ℕ) : ℚ) := by
        exact_mod_cast hsub
      calc ((D.card : ℕ) : ℚ) * ((((n / d).divisors.card : ℚ) ^ 2) / (d.divisors.card : ℚ))
          ≤ ((d.divisors.card : ℚ) * ((n / d).divisors.card : ℚ))
              * ((((n / d).divisors.card : ℚ) ^ 2) / (d.divisors.card : ℚ)) :=
            mul_le_mul_of_nonneg_right hcast (div_nonneg (sq_nonneg _) (le_of_lt hdp))
        _ = ((n / d).divisors.card : ℚ) ^ 3 := by
            field_simp
    calc ((D.card : ℕ) : ℚ) * A
        = ∑ d ∈ D, ((D.card : ℕ) : ℚ)
            * ((((n / d).divisors.card : ℚ) ^ 2) / (d.divisors.card : ℚ)) := by
            simp only [A, Finset.mul_sum]
        _ ≤ ∑ d ∈ D, ((n / d).divisors.card : ℚ) ^ 3 := Finset.sum_le_sum hterm
        _ = ∑ d ∈ D, (d.divisors.card : ℚ) ^ 3 := by
            rw [hD]
            exact Nat.sum_div_divisors n (fun x => ((x.divisors.card : ℚ) ^ 3))
        _ = t3 ^ 2 := by
            have hcube := tau_cube_sum_eq_sq_sum n
            simp only [t3]
            rw [hD]
            have h1 : (∑ d ∈ n.divisors, ((d.divisors.card : ℚ)^3))
                = ((∑ d ∈ n.divisors, (d.divisors.card)^3 : ℕ) : ℚ) := by push_cast; rfl
            have h2 : ((∑ d ∈ n.divisors, (d.divisors.card : ℚ)))^2
                = (((∑ d ∈ n.divisors, d.divisors.card : ℕ) : ℚ))^2 := by push_cast; rfl
            rw [h1, h2, hcube]
            push_cast
            ring
  have hApos : (0 : ℚ) < A := by
    simp only [A]
    have hterm1 : (0 : ℚ) < (((n / 1).divisors.card : ℚ) ^ 2) / ((1 : ℕ).divisors.card : ℚ) := by
      have hτ : (0 : ℚ) < ((n).divisors.card : ℚ) := by
        exact_mod_cast Finset.card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr hn0⟩
      rw [Nat.div_one, Nat.divisors_one, Finset.card_singleton, Nat.cast_one, div_one]
      positivity
    exact Finset.sum_pos' (fun d _ => div_nonneg (sq_nonneg _) (Nat.cast_nonneg _))
      ⟨1, h1D, hterm1⟩
  have hWq_nonneg : 0 ≤ Wq := by
    simp only [Wq]
    exact Finset.sum_nonneg (fun d _ => Nat.cast_nonneg _)
  have ht3_nonneg : 0 ≤ t3 := by
    simp only [t3]
    exact Finset.sum_nonneg (fun d _ => Nat.cast_nonneg _)
  have hcombine : ((D.card : ℕ) : ℚ) * A ≤ 9 * A * Sq := by
    have hA_nonneg : 0 ≤ A := le_of_lt hApos
    have hSq_nonneg : 0 ≤ Sq := le_of_lt hSqpos
    calc ((D.card : ℕ) : ℚ) * A ≤ t3 ^ 2 := hP4
      _ ≤ (3 * Wq) ^ 2 := by nlinarith [hP2, hWq_nonneg, ht3_nonneg]
      _ = 9 * Wq ^ 2 := by ring
      _ ≤ 9 * (A * Sq) := mul_le_mul_of_nonneg_left hP3 (by norm_num)
      _ = 9 * A * Sq := by ring
  have hcardQ : ((D.card : ℕ) : ℚ) ≤ 9 * Sq := by
    have h1 : ((D.card : ℕ) : ℚ) * A ≤ (9 * Sq) * A := by
      calc ((D.card : ℕ) : ℚ) * A ≤ 9 * A * Sq := hcombine
        _ = (9 * Sq) * A := by ring
    exact le_of_mul_le_mul_right h1 hApos
  have hfinalQ : ((D.card : ℕ) : ℚ)
      ≤ ((9 * ∑ d ∈ T, d.divisors.card : ℕ) : ℚ) := by
    have hcast : (9 * Sq) = ((9 * ∑ d ∈ T, d.divisors.card : ℕ) : ℚ) := by
      simp only [Sq]; push_cast; ring
    rw [hcast] at hcardQ; exact hcardQ
  have hnat : D.card ≤ 9 * ∑ d ∈ T, d.divisors.card := by exact_mod_cast hfinalQ
  simpa using hnat

end Commons.NumberTheory.FriedlanderIwaniec
