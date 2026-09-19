import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum.BigOperators
import Mathlib.Tactic.NormNum.Prime
import Submission.Commons.NumberTheory.SieveWindows.weighted_divisorSumProduct_window_eq_k

namespace Commons.NumberTheory.Totient

open scoped BigOperators

/-- The integrand appearing in the statement: `1 + 2/(p(p-1))`. -/
private noncomputable def phi (p : ℕ) : ℝ := 1 + 2 / ((p : ℝ) * ((p : ℝ) - 1))

private lemma one_le_phi {p : ℕ} (hp : 2 ≤ p) : 1 ≤ phi p := by
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hden : 0 < (p : ℝ) * ((p : ℝ) - 1) := by
    apply mul_pos <;> linarith
  rw [phi]
  have hx : 0 ≤ 2 / ((p : ℝ) * ((p : ℝ) - 1)) := div_nonneg (by norm_num) hden.le
  linarith

/-- Weierstrass product bound: for nonnegative `g` with total sum `< 1`,
`∏ (1 + g a) ≤ (1 - ∑ g a)⁻¹`. -/
private lemma prod_one_add_le_inv_one_sub_sum {α : Type*} (s : Finset α) (g : α → ℝ)
    (hg : ∀ a ∈ s, 0 ≤ g a) (hsum : ∑ a ∈ s, g a < 1) :
    ∏ a ∈ s, (1 + g a) ≤ (1 - ∑ a ∈ s, g a)⁻¹ := by
  classical
  revert hg hsum
  refine Finset.induction_on s ?_ ?_
  · intro hg hsum; simp
  · intro a t ha ih hg hsum
    have hga : 0 ≤ g a := hg a (Finset.mem_insert_self a t)
    have hgt : ∀ b ∈ t, 0 ≤ g b := fun b hb => hg b (Finset.mem_insert_of_mem hb)
    have hSt : 0 ≤ ∑ b ∈ t, g b := Finset.sum_nonneg hgt
    have hxS : g a + ∑ b ∈ t, g b < 1 := by
      have := hsum
      rwa [Finset.sum_insert ha] at this
    have hsumt : ∑ b ∈ t, g b < 1 := by linarith
    have ih' := ih hgt hsumt
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    set S := ∑ b ∈ t, g b
    have h1S : 0 < 1 - S := by linarith
    have h1xS : 0 < 1 - (g a + S) := by linarith
    calc (1 + g a) * ∏ b ∈ t, (1 + g b)
        ≤ (1 + g a) * (1 - S)⁻¹ := mul_le_mul_of_nonneg_left ih' (by linarith)
      _ ≤ (1 - (g a + S))⁻¹ := by
          rw [← div_eq_mul_inv, ← one_div]
          rw [div_le_div_iff₀ h1S h1xS]
          nlinarith [hga, hSt]

/-- Telescoping sum: `∑_{p=17}^{N} 2/(p(p-1)) = 1/8 - 2/N`. -/
private lemma sum_Icc_17_telescope (N : ℕ) (hN : 16 ≤ N) :
    (∑ p ∈ Finset.Icc 17 N, 2 / ((p : ℝ) * ((p : ℝ) - 1))) = 1 / 8 - 2 / (N : ℝ) := by
  induction N, hN using Nat.le_induction with
  | base =>
      have : Finset.Icc 17 16 = (∅ : Finset ℕ) := Finset.Icc_eq_empty_of_lt (by norm_num)
      rw [this]; norm_num
  | succ N hN ih =>
      rw [Finset.sum_Icc_succ_top (by omega : 17 ≤ N + 1)
        (fun p => 2 / ((p : ℝ) * ((p : ℝ) - 1)))]
      rw [ih]
      push_cast
      have hden : ((N : ℝ) + 1 - 1) = (N : ℝ) := by ring
      rw [hden]
      have hN0 : (N : ℝ) ≠ 0 := by positivity
      have key : (2 : ℝ) / ((N : ℝ) * ((N : ℝ) + 1)) = 2 / (N : ℝ) - 2 / ((N : ℝ) + 1) := by
        field_simp
        ring
      rw [mul_comm ((N : ℝ) + 1) (N : ℝ)]
      linarith [key]

/-- Every prime below `17` is one of `2, 3, 5, 7, 11, 13`. -/
private lemma primes_lt_17 (p : ℕ) (hp : Nat.Prime p) (hlt : p < 17) :
    p ∈ ({2, 3, 5, 7, 11, 13} : Finset ℕ) := by
  interval_cases p <;> norm_num at hp
  all_goals simp

theorem prod_one_add_two_div_mul_pred_le_four (P : ℕ) :
    ∏ p ∈ P.primeFactors, (1 + 2 / ((p : ℝ) * ((p : ℝ) - 1))) ≤ 4 := by
  change ∏ p ∈ P.primeFactors, phi p ≤ 4
  classical
  set A := P.primeFactors with hA
  set B := A.filter (fun p => ¬ p < 17) with hB
  have mem_prime : ∀ p ∈ A, Nat.Prime p := by
    intro p hp
    have hp' : p ∈ P.primeFactors := by simpa [hA] using hp
    exact (Nat.mem_primeFactors.mp hp').1
  have hsplit : ∏ p ∈ A, phi p
      = (∏ p ∈ A.filter (fun p => p < 17), phi p) * (∏ p ∈ B, phi p) := by
    rw [hB]
    exact (Finset.prod_filter_mul_prod_filter_not A (fun p => p < 17) phi).symm
  -- small primes
  have hsubset_small : A.filter (fun p => p < 17) ⊆ ({2, 3, 5, 7, 11, 13} : Finset ℕ) := by
    intro p hp
    rw [Finset.mem_filter] at hp
    exact primes_lt_17 p (mem_prime p hp.1) hp.2
  have hone : ∀ i ∈ ({2, 3, 5, 7, 11, 13} : Finset ℕ), 1 ≤ phi i := by
    intro i hi
    apply one_le_phi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num
  have hsmall : ∏ p ∈ A.filter (fun p => p < 17), phi p ≤ 7 / 2 := by
    have hf0 : ∀ i ∈ A.filter (fun p => p < 17), 0 ≤ phi i := by
      intro i hi
      have hiA : i ∈ A := (Finset.mem_filter.mp hi).1
      have := one_le_phi (mem_prime i hiA).two_le
      linarith
    have hstep : ∏ p ∈ A.filter (fun p => p < 17), phi p
        ≤ ∏ p ∈ ({2, 3, 5, 7, 11, 13} : Finset ℕ), phi p :=
      Finset.prod_le_prod_of_subset_of_one_le₀ hsubset_small hf0 (fun i hi _ => hone i hi)
    have hexpl : ∏ p ∈ ({2, 3, 5, 7, 11, 13} : Finset ℕ), phi p ≤ 7 / 2 := by
      norm_num [phi, Finset.prod_insert]
    linarith
  -- tail sum
  have hbig_sum : ∑ p ∈ B, 2 / ((p : ℝ) * ((p : ℝ) - 1)) ≤ 1 / 8 := by
    rcases B.eq_empty_or_nonempty with hemp | hne
    · rw [hemp]; simp
    · set N := B.max' hne with hN
      have hNmem : N ∈ B := Finset.max'_mem B hne
      have hNB : ∀ p ∈ B, p ≤ N := fun p hp => Finset.le_max' B p hp
      have hN17 : 17 ≤ N := by
        have := (Finset.mem_filter.mp hNmem).2
        omega
      have hsubset : B ⊆ Finset.Icc 17 N := by
        intro p hp
        rw [Finset.mem_Icc]
        exact ⟨by have := (Finset.mem_filter.mp hp).2; omega, hNB p hp⟩
      have hnonneg : ∀ p ∈ Finset.Icc 17 N, p ∉ B →
          0 ≤ 2 / ((p : ℝ) * ((p : ℝ) - 1)) := by
        intro p hp _
        have hp2 : (2 : ℝ) ≤ (p : ℝ) := by
          have h2p : 2 ≤ p := le_trans (by norm_num) (Finset.mem_Icc.mp hp).1
          exact_mod_cast h2p
        exact div_nonneg (by norm_num) (mul_nonneg (by linarith) (by linarith))
      have hle := Finset.sum_le_sum_of_subset_of_nonneg hsubset hnonneg
      rw [sum_Icc_17_telescope N (by omega)] at hle
      have : (0 : ℝ) ≤ 2 / (N : ℝ) := by positivity
      linarith
  -- tail product
  have hbig_prod : ∏ p ∈ B, phi p ≤ 8 / 7 := by
    have hnn : ∀ p ∈ B, 0 ≤ 2 / ((p : ℝ) * ((p : ℝ) - 1)) := by
      intro p hp
      have hpA : p ∈ A := (Finset.mem_filter.mp hp).1
      have h2p : 2 ≤ p := (mem_prime p hpA).two_le
      have hcast : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast h2p
      exact div_nonneg (by norm_num) (mul_nonneg (by linarith) (by linarith))
    have hsum_lt : ∑ p ∈ B, 2 / ((p : ℝ) * ((p : ℝ) - 1)) < 1 :=
      lt_of_le_of_lt hbig_sum (by norm_num)
    have hlemma := prod_one_add_le_inv_one_sub_sum B
      (fun p => 2 / ((p : ℝ) * ((p : ℝ) - 1))) hnn hsum_lt
    have hprod_eq : ∏ p ∈ B, phi p = ∏ p ∈ B, (1 + 2 / ((p : ℝ) * ((p : ℝ) - 1))) := by
      apply Finset.prod_congr rfl
      intro p hp
      rw [phi]
    rw [hprod_eq]
    refine le_trans hlemma ?_
    calc (1 - ∑ p ∈ B, 2 / ((p : ℝ) * ((p : ℝ) - 1)))⁻¹
        = 1 / (1 - ∑ p ∈ B, 2 / ((p : ℝ) * ((p : ℝ) - 1))) := by rw [one_div]
      _ ≤ 1 / (7 / 8) := by
            apply one_div_le_one_div_of_le (by norm_num)
            linarith
      _ = 8 / 7 := by norm_num
  rw [hsplit]
  have hbig_nonneg : 0 ≤ ∏ p ∈ B, phi p := by
    apply Finset.prod_nonneg
    intro p hp
    have hpA : p ∈ A := (Finset.mem_filter.mp hp).1
    have := one_le_phi (mem_prime p hpA).two_le
    linarith
  calc (∏ p ∈ A.filter (fun p => p < 17), phi p) * (∏ p ∈ B, phi p)
      ≤ (7 / 2) * (∏ p ∈ B, phi p) := mul_le_mul_of_nonneg_right hsmall hbig_nonneg
    _ ≤ (7 / 2) * (8 / 7) := mul_le_mul_of_nonneg_left hbig_prod (by norm_num)
    _ = 4 := by norm_num

end Commons.NumberTheory.Totient