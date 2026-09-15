import Submission.Commons.NumberTheory.Sieve.prod_one_add_mul_rpow_half_le_sum_pairs

namespace Commons.NumberTheory.Sieve

open Finset

theorem prod_rpow_le_sum_pairs {n : ℕ} (hn : 2 ≤ n) {C E : ℝ} (hC : 1 ≤ C)
    (hE : C * (n : ℝ) ^ 2 ≤ E) (d : Fin n → Fin n → ℕ) (hd : ∀ i j, 1 ≤ d i j) :
    (∏ q ∈ (∏ i : Fin n, ∏ j ∈ Finset.univ.filter (fun j => i < j), d i j).primeFactors,
        (1 + (q : ℝ) ^ (-(1 / 2 : ℝ)))) ^ C
      ≤ ∑ i : Fin n, ∑ j ∈ Finset.univ.filter (fun j => i < j),
          (∏ q ∈ (d i j).primeFactors, (1 + (q : ℝ) ^ (-(1 / 2 : ℝ)))) ^ E := by
  classical
  set S : Finset (Σ _ : Fin n, Fin n) :=
    Finset.univ.sigma (fun i => Finset.univ.filter (fun j => i < j)) with hS
  have eq_prod : (∏ i : Fin n, ∏ j ∈ Finset.univ.filter (fun j => i < j), d i j)
      = ∏ p ∈ S, d p.1 p.2 := by
    rw [hS]
    exact (Finset.prod_sigma Finset.univ
      (fun i => Finset.univ.filter (fun j => i < j))
      (fun p : (Σ _ : Fin n, Fin n) => d p.1 p.2)).symm
  have eq_sum : (∑ i : Fin n, ∑ j ∈ Finset.univ.filter (fun j => i < j),
        (∏ q ∈ (d i j).primeFactors, (1 + (q : ℝ) ^ (-(1 / 2 : ℝ)))) ^ E)
      = ∑ p ∈ S, (∏ q ∈ (d p.1 p.2).primeFactors, (1 + (q : ℝ) ^ (-(1 / 2 : ℝ)))) ^ E := by
    rw [hS]
    exact (Finset.sum_sigma Finset.univ
      (fun i => Finset.univ.filter (fun j => i < j))
      (fun p : (Σ _ : Fin n, Fin n) =>
        (∏ q ∈ (d p.1 p.2).primeFactors, (1 + (q : ℝ) ^ (-(1 / 2 : ℝ)))) ^ E)).symm
  rw [eq_prod, eq_sum]
  clear eq_prod eq_sum
  -- Basic facts about the per-factor function `q ↦ 1 + q^{-1/2}`.
  have hh1 : ∀ q : ℕ, 1 ≤ (1 + (q : ℝ) ^ (-(1 / 2 : ℝ))) := fun q =>
    le_add_of_nonneg_right (Real.rpow_nonneg (Nat.cast_nonneg q) _)
  have hh0 : ∀ q : ℕ, 0 ≤ (1 + (q : ℝ) ^ (-(1 / 2 : ℝ))) := fun q =>
    le_trans zero_le_one (hh1 q)
  have hC0 : 0 ≤ C := le_trans zero_le_one hC
  -- `S` is nonempty since `n ≥ 2`.
  have hSne : S.Nonempty := by
    refine ⟨⟨⟨0, by omega⟩, ⟨1, by omega⟩⟩, ?_⟩
    rw [hS, Finset.mem_sigma]
    exact ⟨Finset.mem_univ _, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp [Fin.lt_def]⟩⟩
  -- Cardinality bound: `S.card ≤ n^2`.
  have hcard : S.card ≤ n ^ 2 := by
    rw [hS, Finset.card_sigma]
    calc ∑ a ∈ Finset.univ, (Finset.univ.filter (fun j => a < j)).card
        ≤ ∑ _a ∈ Finset.univ, n := by
          apply Finset.sum_le_sum
          intro a _
          calc (Finset.univ.filter (fun j => a < j)).card
              ≤ (Finset.univ : Finset (Fin n)).card :=
                Finset.card_le_card (fun x hx => Finset.mem_univ x)
            _ = n := by simp
      _ = n * n := by simp [Finset.sum_const, Finset.card_univ, smul_eq_mul]
      _ = n ^ 2 := by ring
  have hEcard : C * (S.card : ℝ) ≤ E := by
    have hcast : (S.card : ℝ) ≤ (n : ℝ) ^ 2 := by exact_mod_cast hcard
    calc C * (S.card : ℝ) ≤ C * (n : ℝ) ^ 2 := mul_le_mul_of_nonneg_left hcast hC0
      _ ≤ E := hE
  -- The primes of the total product lie in the union of the primes of the factors.
  have hsub : (∏ p ∈ S, d p.1 p.2).primeFactors ⊆
      S.biUnion (fun p => (d p.1 p.2).primeFactors) := by
    intro q hq
    obtain ⟨hqp, hqdvd, _⟩ := Nat.mem_primeFactors.mp hq
    rw [Finset.mem_biUnion]
    have hdvd := (Prime.dvd_finsetProd_iff hqp.prime
        (fun p : (Σ _ : Fin n, Fin n) => d p.1 p.2)).mp hqdvd
    obtain ⟨p, hpS, hpdvd⟩ := hdvd
    exact ⟨p, hpS, Nat.mem_primeFactors.mpr
      ⟨hqp, hpdvd, ne_of_gt (lt_of_lt_of_le zero_lt_one (hd p.1 p.2))⟩⟩
  -- Step A: product over `primeFactors N` is bounded by the product over all pairs.
  have hstepA : ∏ q ∈ (∏ p ∈ S, d p.1 p.2).primeFactors, (1 + (q : ℝ) ^ (-(1 / 2 : ℝ)))
      ≤ ∏ p ∈ S, ∏ q ∈ (d p.1 p.2).primeFactors, (1 + (q : ℝ) ^ (-(1 / 2 : ℝ))) := by
    refine le_trans (Finset.prod_le_prod_of_subset_of_one_le hsub
      (fun q _ => hh0 q) (fun q _ _ => hh1 q)) ?_
    exact prod_biUnion_le S (fun p => (d p.1 p.2).primeFactors)
      (fun q => 1 + (q : ℝ) ^ (-(1 / 2 : ℝ))) hh1
  -- Assemble the chain of inequalities.
  calc (∏ q ∈ (∏ p ∈ S, d p.1 p.2).primeFactors, (1 + (q : ℝ) ^ (-(1 / 2 : ℝ)))) ^ C
      ≤ (∏ p ∈ S, ∏ q ∈ (d p.1 p.2).primeFactors, (1 + (q : ℝ) ^ (-(1 / 2 : ℝ)))) ^ C :=
        Real.rpow_le_rpow
          (Finset.prod_nonneg (fun q _ => hh0 q)) hstepA hC0
    _ = ∏ p ∈ S,
          (∏ q ∈ (d p.1 p.2).primeFactors, (1 + (q : ℝ) ^ (-(1 / 2 : ℝ)))) ^ C :=
        (Real.finsetProd_rpow S
          (fun p => ∏ q ∈ (d p.1 p.2).primeFactors, (1 + (q : ℝ) ^ (-(1 / 2 : ℝ))))
          (fun p _ => Finset.prod_nonneg (fun q _ => hh0 q)) C).symm
    _ ≤ ∑ p ∈ S,
          (∏ q ∈ (d p.1 p.2).primeFactors, (1 + (q : ℝ) ^ (-(1 / 2 : ℝ)))) ^ E :=
        prod_rpow_le_sum_rpow S hSne
          (fun p => ∏ q ∈ (d p.1 p.2).primeFactors, (1 + (q : ℝ) ^ (-(1 / 2 : ℝ))))
          (fun p _ => Finset.one_le_prod (fun q _ => hh1 q)) hC0 hEcard

end Commons.NumberTheory.Sieve
