import Mathlib
import Submission.Commons.NumberTheory.Totient.sum_inv_not_dvd_le_sum_mu_sq_div_totient

open Finset
open scoped BigOperators

namespace Commons.NumberTheory.Totient

noncomputable section

/-- The `n`-th term of the squarefree totient sum: `μ(n)²/φ(n)`. -/
private def f (r : ℕ) : ℝ :=
  ((ArithmeticFunction.moebius r : ℤ) : ℝ) ^ 2 / (Nat.totient r : ℝ)

/-- Integers in `[1,Y]` coprime to `6`. -/
private def A6 (Y : ℕ) : Finset ℕ :=
  (Finset.Icc 1 Y).filter (fun n => ¬ 2 ∣ n ∧ ¬ 3 ∣ n)

/-- Numbers `r ∈ [1,z]` with `v₂ r = 1` and `3 ∤ r`. -/
private def B2 (z : ℕ) : Finset ℕ :=
  (Finset.Icc 1 z).filter (fun r => 2 ∣ r ∧ ¬ 4 ∣ r ∧ ¬ 3 ∣ r)

/-- Numbers `r ∈ [1,z]` with `v₃ r = 1` and `2 ∤ r`. -/
private def B3 (z : ℕ) : Finset ℕ :=
  (Finset.Icc 1 z).filter (fun r => 3 ∣ r ∧ ¬ 9 ∣ r ∧ ¬ 2 ∣ r)

/-- Numbers `r ∈ [1,z]` with `v₂ r = 1` and `v₃ r = 1`. -/
private def B6 (z : ℕ) : Finset ℕ :=
  (Finset.Icc 1 z).filter (fun r => 2 ∣ r ∧ ¬ 4 ∣ r ∧ 3 ∣ r ∧ ¬ 9 ∣ r)

/-- The prime set `{2,3}` written as a named `Finset` so that the `∀ p ∈ _` predicates
below elaborate without a `DecidablePred` instance-search failure. -/
private def PR : Finset ℕ := {2, 3}

private lemma f_nonneg (r : ℕ) : 0 ≤ f r := by
  unfold f
  apply div_nonneg
  · positivity
  · positivity

private lemma f_two_mul (n : ℕ) (hn : ¬ 2 ∣ n) : f (2 * n) = f n := by
  have hcop : Nat.Coprime 2 n := (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hn
  have hmul : ArithmeticFunction.moebius (2 * n)
      = ArithmeticFunction.moebius 2 * ArithmeticFunction.moebius n :=
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop
  have h2 : ArithmeticFunction.moebius 2 = -1 :=
    ArithmeticFunction.moebius_apply_prime Nat.prime_two
  have hμsq : ArithmeticFunction.moebius (2 * n) ^ 2 = ArithmeticFunction.moebius n ^ 2 := by
    rw [hmul, h2]; ring
  have htot : (2 * n).totient = n.totient := by
    rw [Nat.totient_mul hcop, Nat.totient_two, one_mul]
  have hnum : ((ArithmeticFunction.moebius (2 * n) : ℤ) : ℝ) ^ 2
      = ((ArithmeticFunction.moebius n : ℤ) : ℝ) ^ 2 := by
    rw [← Int.cast_pow, ← Int.cast_pow, hμsq]
  unfold f
  rw [htot, hnum]

private lemma f_three_mul (n : ℕ) (hn : ¬ 3 ∣ n) : f (3 * n) = f n / 2 := by
  have hcop : Nat.Coprime 3 n := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hn
  have hmul : ArithmeticFunction.moebius (3 * n)
      = ArithmeticFunction.moebius 3 * ArithmeticFunction.moebius n :=
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop
  have h3 : ArithmeticFunction.moebius 3 = -1 :=
    ArithmeticFunction.moebius_apply_prime Nat.prime_three
  have hμsq : ArithmeticFunction.moebius (3 * n) ^ 2 = ArithmeticFunction.moebius n ^ 2 := by
    rw [hmul, h3]; ring
  have htot : (3 * n).totient = (3:ℕ).totient * n.totient := Nat.totient_mul hcop
  have h3t : (3:ℕ).totient = 2 := by decide
  have hnum : ((ArithmeticFunction.moebius (3 * n) : ℤ) : ℝ) ^ 2
      = ((ArithmeticFunction.moebius n : ℤ) : ℝ) ^ 2 := by
    rw [← Int.cast_pow, ← Int.cast_pow, hμsq]
  unfold f
  rw [htot, h3t, hnum]
  push_cast
  rw [div_div]
  ring

private lemma f_six_mul (n : ℕ) (h2 : ¬ 2 ∣ n) (h3 : ¬ 3 ∣ n) : f (6 * n) = f n / 2 := by
  have h23 : ¬ 2 ∣ 3 * n := by
    intro h
    rcases (Nat.prime_two.dvd_mul).mp h with h | h
    · norm_num at h
    · exact h2 h
  have e1 : 6 * n = 2 * (3 * n) := by ring
  rw [e1, f_two_mul (3 * n) h23, f_three_mul n h3]

/-- The base commons lemma, specialised to the primes `2, 3`. -/
private lemma harmonic_le_totient (Y : ℕ) :
    (∑ n ∈ A6 Y, (1 : ℝ) / n) ≤ ∑ r ∈ A6 Y, f r := by
  have hS : ∀ p ∈ (PR : Finset ℕ), p.Prime := by
    intro p hp
    simp only [PR, Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl
    · exact Nat.prime_two
    · exact Nat.prime_three
  have h := sum_inv_not_dvd_le_sum_mu_sq_div_totient Y (PR : Finset ℕ) hS
  have hf1 : (Finset.Icc 1 Y).filter (fun n => ∀ p ∈ (PR : Finset ℕ), ¬ p ∣ n)
      = A6 Y := by
    rw [A6]
    apply Finset.filter_congr
    intro n _
    simp [PR, Finset.mem_insert, Finset.mem_singleton]
  rw [hf1] at h
  simpa [f] using h

private lemma reindex_two (z : ℕ) :
    (∑ n ∈ A6 (z / 2), f n) ≤ ∑ r ∈ B2 z, f r := by
  have hsub : (A6 (z / 2)).image (fun n => 2 * n) ⊆ B2 z := by
    intro r hr
    rw [Finset.mem_image] at hr
    obtain ⟨n, hn, rfl⟩ := hr
    simp only [A6, Finset.mem_filter, Finset.mem_Icc] at hn
    obtain ⟨⟨hn1, hnz⟩, hn2, hn3⟩ := hn
    simp only [B2, Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨by omega, ?_⟩, by omega, ?_, ?_⟩
    · calc 2 * n ≤ 2 * (z / 2) := Nat.mul_le_mul_left 2 hnz
        _ ≤ z := Nat.mul_div_le z 2
    · intro h
      obtain ⟨k, hk⟩ := h
      exact hn2 ⟨k, by omega⟩
    · intro h
      rcases (Nat.prime_three.dvd_mul).mp h with h' | h'
      · norm_num at h'
      · exact hn3 h'
  have himg : (∑ r ∈ (A6 (z / 2)).image (fun n => 2 * n), f r)
      = ∑ n ∈ A6 (z / 2), f (2 * n) :=
    Finset.sum_image (by intro x _ y _ h; exact Nat.mul_left_cancel (by norm_num) h)
  have heq : (∑ n ∈ A6 (z / 2), f (2 * n)) = ∑ n ∈ A6 (z / 2), f n := by
    apply Finset.sum_congr rfl
    intro n hn
    simp only [A6, Finset.mem_filter] at hn
    exact f_two_mul n hn.2.1
  calc (∑ n ∈ A6 (z / 2), f n)
      = ∑ n ∈ A6 (z / 2), f (2 * n) := heq.symm
    _ = ∑ r ∈ (A6 (z / 2)).image (fun n => 2 * n), f r := himg.symm
    _ ≤ ∑ r ∈ B2 z, f r :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun r _ _ => f_nonneg r)

private lemma reindex_three (z : ℕ) :
    (1 / 2) * (∑ n ∈ A6 (z / 3), f n) ≤ ∑ r ∈ B3 z, f r := by
  have hsub : (A6 (z / 3)).image (fun n => 3 * n) ⊆ B3 z := by
    intro r hr
    rw [Finset.mem_image] at hr
    obtain ⟨n, hn, rfl⟩ := hr
    simp only [A6, Finset.mem_filter, Finset.mem_Icc] at hn
    obtain ⟨⟨hn1, hnz⟩, hn2, hn3⟩ := hn
    simp only [B3, Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨by omega, ?_⟩, ⟨by omega, ?_, ?_⟩⟩
    · calc 3 * n ≤ 3 * (z / 3) := Nat.mul_le_mul_left 3 hnz
        _ ≤ z := Nat.mul_div_le z 3
    · intro h
      obtain ⟨k, hk⟩ := h
      exact hn3 ⟨k, by omega⟩
    · intro h
      rcases (Nat.prime_two.dvd_mul).mp h with h' | h'
      · norm_num at h'
      · exact hn2 h'
  have himg : (∑ r ∈ (A6 (z / 3)).image (fun n => 3 * n), f r)
      = ∑ n ∈ A6 (z / 3), f (3 * n) :=
    Finset.sum_image (by intro x _ y _ h; exact Nat.mul_left_cancel (by norm_num) h)
  have heq : (∑ n ∈ A6 (z / 3), (1 / 2) * f n) = ∑ n ∈ A6 (z / 3), f (3 * n) := by
    apply Finset.sum_congr rfl
    intro n hn
    simp only [A6, Finset.mem_filter] at hn
    rw [f_three_mul n hn.2.2]
    ring
  have hfac : (1 / 2) * (∑ n ∈ A6 (z / 3), f n) = ∑ n ∈ A6 (z / 3), (1 / 2) * f n :=
    Finset.mul_sum _ _ _
  calc (1 / 2) * (∑ n ∈ A6 (z / 3), f n)
      = ∑ n ∈ A6 (z / 3), (1 / 2) * f n := hfac
    _ = ∑ n ∈ A6 (z / 3), f (3 * n) := heq
    _ = ∑ r ∈ (A6 (z / 3)).image (fun n => 3 * n), f r := himg.symm
    _ ≤ ∑ r ∈ B3 z, f r :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun r _ _ => f_nonneg r)

private lemma reindex_six (z : ℕ) :
    (1 / 2) * (∑ n ∈ A6 (z / 6), f n) ≤ ∑ r ∈ B6 z, f r := by
  have hsub : (A6 (z / 6)).image (fun n => 6 * n) ⊆ B6 z := by
    intro r hr
    rw [Finset.mem_image] at hr
    obtain ⟨n, hn, rfl⟩ := hr
    simp only [A6, Finset.mem_filter, Finset.mem_Icc] at hn
    obtain ⟨⟨hn1, hnz⟩, hn2, hn3⟩ := hn
    simp only [B6, Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨by omega, ?_⟩, by omega, ?_, by omega, ?_⟩
    · calc 6 * n ≤ 6 * (z / 6) := Nat.mul_le_mul_left 6 hnz
        _ ≤ z := Nat.mul_div_le z 6
    · intro h
      obtain ⟨k, hk⟩ := h
      exact hn2 (by
        have h2 : 2 ∣ 3 * n := ⟨k, by omega⟩
        rcases (Nat.prime_two.dvd_mul).mp h2 with h' | h'
        · norm_num at h'
        · exact h')
    · intro h
      obtain ⟨k, hk⟩ := h
      exact hn3 (by
        have h3 : 3 ∣ 2 * n := ⟨k, by omega⟩
        rcases (Nat.prime_three.dvd_mul).mp h3 with h' | h'
        · norm_num at h'
        · exact h')
  have himg : (∑ r ∈ (A6 (z / 6)).image (fun n => 6 * n), f r)
      = ∑ n ∈ A6 (z / 6), f (6 * n) :=
    Finset.sum_image (by intro x _ y _ h; exact Nat.mul_left_cancel (by norm_num) h)
  have heq : (∑ n ∈ A6 (z / 6), (1 / 2) * f n) = ∑ n ∈ A6 (z / 6), f (6 * n) := by
    apply Finset.sum_congr rfl
    intro n hn
    simp only [A6, Finset.mem_filter] at hn
    rw [f_six_mul n hn.2.1 hn.2.2]
    ring
  have hfac : (1 / 2) * (∑ n ∈ A6 (z / 6), f n) = ∑ n ∈ A6 (z / 6), (1 / 2) * f n :=
    Finset.mul_sum _ _ _
  calc (1 / 2) * (∑ n ∈ A6 (z / 6), f n)
      = ∑ n ∈ A6 (z / 6), (1 / 2) * f n := hfac
    _ = ∑ n ∈ A6 (z / 6), f (6 * n) := heq
    _ = ∑ r ∈ (A6 (z / 6)).image (fun n => 6 * n), f r := himg.symm
    _ ≤ ∑ r ∈ B6 z, f r :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun r _ _ => f_nonneg r)

private lemma four_sum_le (z : ℕ) :
    (∑ r ∈ A6 z, f r) + (∑ r ∈ B2 z, f r) + (∑ r ∈ B3 z, f r) + (∑ r ∈ B6 z, f r)
      ≤ ∑ r ∈ Finset.Icc 1 z, f r := by
  have hd12 : Disjoint (A6 z) (B2 z) := by
    rw [Finset.disjoint_left]; intro r hr1 hr2
    simp only [A6, B2, Finset.mem_filter] at hr1 hr2
    exact hr1.2.1 hr2.2.1
  have hd13 : Disjoint (A6 z) (B3 z) := by
    rw [Finset.disjoint_left]; intro r hr1 hr3
    simp only [A6, B3, Finset.mem_filter] at hr1 hr3
    exact hr1.2.2 hr3.2.1
  have hd14 : Disjoint (A6 z) (B6 z) := by
    rw [Finset.disjoint_left]; intro r hr1 hr4
    simp only [A6, B6, Finset.mem_filter] at hr1 hr4
    exact hr1.2.1 hr4.2.1
  have hd23 : Disjoint (B2 z) (B3 z) := by
    rw [Finset.disjoint_left]; intro r hr2 hr3
    simp only [B2, B3, Finset.mem_filter] at hr2 hr3
    exact hr3.2.2.2 hr2.2.1
  have hd24 : Disjoint (B2 z) (B6 z) := by
    rw [Finset.disjoint_left]; intro r hr2 hr4
    simp only [B2, B6, Finset.mem_filter] at hr2 hr4
    exact hr2.2.2.2 hr4.2.2.2.1
  have hd34 : Disjoint (B3 z) (B6 z) := by
    rw [Finset.disjoint_left]; intro r hr3 hr4
    simp only [B3, B6, Finset.mem_filter] at hr3 hr4
    exact hr3.2.2.2 hr4.2.1
  have hU1 : Disjoint (A6 z ∪ B2 z) (B3 z) := by
    rw [Finset.disjoint_union_left]; exact ⟨hd13, hd23⟩
  have hU2 : Disjoint (A6 z ∪ B2 z ∪ B3 z) (B6 z) := by
    rw [Finset.disjoint_union_left]
    exact ⟨Finset.disjoint_union_left.mpr ⟨hd14, hd24⟩, hd34⟩
  have hsum1 : (∑ r ∈ A6 z ∪ B2 z, f r) = (∑ r ∈ A6 z, f r) + (∑ r ∈ B2 z, f r) :=
    Finset.sum_union hd12
  have hsum2 : (∑ r ∈ A6 z ∪ B2 z ∪ B3 z, f r)
      = (∑ r ∈ A6 z ∪ B2 z, f r) + (∑ r ∈ B3 z, f r) := Finset.sum_union hU1
  have hsum3 : (∑ r ∈ A6 z ∪ B2 z ∪ B3 z ∪ B6 z, f r)
      = (∑ r ∈ A6 z ∪ B2 z ∪ B3 z, f r) + (∑ r ∈ B6 z, f r) := Finset.sum_union hU2
  have htot : (∑ r ∈ A6 z, f r) + (∑ r ∈ B2 z, f r) + (∑ r ∈ B3 z, f r)
      + (∑ r ∈ B6 z, f r) = ∑ r ∈ A6 z ∪ B2 z ∪ B3 z ∪ B6 z, f r := by
    rw [← hsum1, ← hsum2, ← hsum3]
  rw [htot]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · apply Finset.union_subset
    · apply Finset.union_subset
      · apply Finset.union_subset
        · exact Finset.filter_subset _ _
        · exact Finset.filter_subset _ _
      · exact Finset.filter_subset _ _
    · exact Finset.filter_subset _ _
  · intro r _ _
    exact f_nonneg r

theorem totient_sum_ge_A6_combo (z : ℕ) :
    (∑ n ∈ (Finset.Icc 1 z).filter (fun n => ¬ 2 ∣ n ∧ ¬ 3 ∣ n), (1:ℝ)/n)
      + (∑ n ∈ (Finset.Icc 1 (z/2)).filter (fun n => ¬ 2 ∣ n ∧ ¬ 3 ∣ n), (1:ℝ)/n)
      + (1/2) * (∑ n ∈ (Finset.Icc 1 (z/3)).filter (fun n => ¬ 2 ∣ n ∧ ¬ 3 ∣ n), (1:ℝ)/n)
      + (1/2) * (∑ n ∈ (Finset.Icc 1 (z/6)).filter (fun n => ¬ 2 ∣ n ∧ ¬ 3 ∣ n), (1:ℝ)/n)
    ≤ ∑ r ∈ Finset.Icc 1 z, ((ArithmeticFunction.moebius r : ℤ) : ℝ) ^ 2 / (Nat.totient r : ℝ) := by
  show (∑ n ∈ A6 z, (1 : ℝ) / n) + (∑ n ∈ A6 (z / 2), (1 : ℝ) / n)
      + (1 / 2) * (∑ n ∈ A6 (z / 3), (1 : ℝ) / n)
      + (1 / 2) * (∑ n ∈ A6 (z / 6), (1 : ℝ) / n)
      ≤ ∑ r ∈ Finset.Icc 1 z, f r
  have h1 := harmonic_le_totient z
  have h2 := harmonic_le_totient (z / 2)
  have h3 := harmonic_le_totient (z / 3)
  have h4 := harmonic_le_totient (z / 6)
  have e3 : (1 / 2) * (∑ n ∈ A6 (z / 3), (1 : ℝ) / n)
      ≤ (1 / 2) * (∑ n ∈ A6 (z / 3), f n) :=
    mul_le_mul_of_nonneg_left h3 (by norm_num)
  have e4 : (1 / 2) * (∑ n ∈ A6 (z / 6), (1 : ℝ) / n)
      ≤ (1 / 2) * (∑ n ∈ A6 (z / 6), f n) :=
    mul_le_mul_of_nonneg_left h4 (by norm_num)
  have step1 :
      (∑ n ∈ A6 z, (1 : ℝ) / n) + (∑ n ∈ A6 (z / 2), (1 : ℝ) / n)
        + (1 / 2) * (∑ n ∈ A6 (z / 3), (1 : ℝ) / n)
        + (1 / 2) * (∑ n ∈ A6 (z / 6), (1 : ℝ) / n)
      ≤ (∑ n ∈ A6 z, f n) + (∑ n ∈ A6 (z / 2), f n)
        + (1 / 2) * (∑ n ∈ A6 (z / 3), f n)
        + (1 / 2) * (∑ n ∈ A6 (z / 6), f n) :=
    add_le_add (add_le_add (add_le_add h1 h2) e3) e4
  have step2 :
      (∑ n ∈ A6 z, f n) + (∑ n ∈ A6 (z / 2), f n)
        + (1 / 2) * (∑ n ∈ A6 (z / 3), f n)
        + (1 / 2) * (∑ n ∈ A6 (z / 6), f n)
      ≤ (∑ r ∈ A6 z, f r) + (∑ r ∈ B2 z, f r)
        + (∑ r ∈ B3 z, f r) + (∑ r ∈ B6 z, f r) :=
    add_le_add (add_le_add (add_le_add le_rfl (reindex_two z)) (reindex_three z))
      (reindex_six z)
  exact le_trans (le_trans step1 step2) (four_sum_le z)

end

end Commons.NumberTheory.Totient
