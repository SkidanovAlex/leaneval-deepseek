import Mathlib.Data.Fintype.BigOperators
import Mathlib.NumberTheory.Divisors
import Submission.Commons.NumberTheory.ArithmeticFunction.card_Omega_eq_le

namespace Commons.NumberTheory.ArithmeticFunction

theorem card_lcm_prod_eq_le_of_ne_zero (k M : ℕ) (hM : M ≠ 0) :
    ((Finset.univ : Finset (Fin k → Fin (M + 1) × Fin (M + 1))).filter
      (fun p => ∏ i : Fin k, ((p i).1 : ℕ).lcm ((p i).2 : ℕ) = M)).card ≤
      (M.divisors.card) ^ (3 * k) := by
  have hcard :
      ((Finset.univ : Finset (Fin k → Fin (M + 1) × Fin (M + 1))).filter
        (fun p => ∏ i : Fin k, ((p i).1 : ℕ).lcm ((p i).2 : ℕ) = M)).card ≤
      (Fintype.piFinset (fun _ : Fin k => M.divisors ×ˢ M.divisors)).card := by
    refine Finset.card_le_card_of_injOn
      (fun p : Fin k → Fin (M + 1) × Fin (M + 1) => fun i => (((p i).1 : ℕ), ((p i).2 : ℕ))) ?_ ?_
    · intro p hp
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hp
      rw [Finset.mem_coe, Fintype.mem_piFinset]
      intro i
      have hdi : ((p i).1 : ℕ).lcm ((p i).2 : ℕ) ∣ M := by
        have h := Finset.dvd_prod_of_mem
          (fun j : Fin k => ((p j).1 : ℕ).lcm ((p j).2 : ℕ)) (Finset.mem_univ i)
        rwa [hp] at h
      rw [Finset.mem_product, Nat.mem_divisors, Nat.mem_divisors]
      exact ⟨⟨dvd_trans (Nat.dvd_lcm_left _ _) hdi, hM⟩,
             ⟨dvd_trans (Nat.dvd_lcm_right _ _) hdi, hM⟩⟩
    · intro p _ q _ heq
      funext i
      have h1 : ((p i).1 : ℕ) = ((q i).1 : ℕ) := congrArg Prod.fst (congrFun heq i)
      have h2 : ((p i).2 : ℕ) = ((q i).2 : ℕ) := congrArg Prod.snd (congrFun heq i)
      exact Prod.ext (Fin.ext h1) (Fin.ext h2)
  have htcard : (Fintype.piFinset (fun _ : Fin k => M.divisors ×ˢ M.divisors)).card
      = (M.divisors.card * M.divisors.card) ^ k := by
    rw [Fintype.card_piFinset]
    simp only [Finset.card_product]
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hτ : 1 ≤ M.divisors.card := by
    have h : (1 : ℕ) ∈ M.divisors := Nat.one_mem_divisors.mpr hM
    exact Finset.one_le_card.mpr ⟨1, h⟩
  calc ((Finset.univ : Finset (Fin k → Fin (M + 1) × Fin (M + 1))).filter
        (fun p => ∏ i : Fin k, ((p i).1 : ℕ).lcm ((p i).2 : ℕ) = M)).card
      ≤ (Fintype.piFinset (fun _ : Fin k => M.divisors ×ˢ M.divisors)).card := hcard
    _ = (M.divisors.card * M.divisors.card) ^ k := htcard
    _ = M.divisors.card ^ (2 * k) := by rw [pow_mul, pow_two]
    _ ≤ M.divisors.card ^ (3 * k) := Nat.pow_le_pow_right (by omega) (by omega)

end Commons.NumberTheory.ArithmeticFunction