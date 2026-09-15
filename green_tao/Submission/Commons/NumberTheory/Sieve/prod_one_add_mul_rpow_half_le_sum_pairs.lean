import Mathlib.Algebra.BigOperators.Associated
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

open Finset

namespace Commons.NumberTheory.Sieve

lemma prod_biUnion_le {α β : Type*} [DecidableEq β] (s : Finset α) (f : α → Finset β)
    (g : β → ℝ) (hg : ∀ b, 1 ≤ g b) :
    ∏ b ∈ s.biUnion f, g b ≤ ∏ a ∈ s, ∏ b ∈ f a, g b := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a t ha ih =>
      rw [Finset.biUnion_insert, Finset.prod_insert ha]
      have hA : 0 ≤ ∏ x ∈ f a ∪ t.biUnion f, g x :=
        Finset.prod_nonneg (fun x _ => le_trans zero_le_one (hg x))
      have hB : 1 ≤ ∏ x ∈ f a ∩ t.biUnion f, g x :=
        Finset.one_le_prod (fun x _ => hg x)
      calc ∏ x ∈ f a ∪ t.biUnion f, g x
          ≤ (∏ x ∈ f a ∪ t.biUnion f, g x) * (∏ x ∈ f a ∩ t.biUnion f, g x) := by
            simpa using mul_le_mul_of_nonneg_left hB hA
        _ = (∏ x ∈ f a, g x) * (∏ x ∈ t.biUnion f, g x) := Finset.prod_union_inter
        _ ≤ (∏ x ∈ f a, g x) * (∏ a' ∈ t, ∏ x ∈ f a', g x) := by
            apply mul_le_mul_of_nonneg_left ih
            exact Finset.prod_nonneg (fun x _ => le_trans zero_le_one (hg x))

lemma prod_rpow_le_sum_rpow {α : Type*} (s : Finset α) (hs : s.Nonempty) (a : α → ℝ)
    (ha : ∀ x ∈ s, 1 ≤ a x) {C E : ℝ} (hC : 0 ≤ C) (hE : C * s.card ≤ E) :
    ∏ x ∈ s, a x ^ C ≤ ∑ x ∈ s, a x ^ E := by
  classical
  obtain ⟨m, hm_mem, hm_eq⟩ := Finset.exists_mem_eq_sup' hs a
  have hm1 : 1 ≤ a m := ha m hm_mem
  have hle : ∀ x ∈ s, a x ≤ a m := fun x hx => by
    rw [← hm_eq]; exact Finset.le_sup' a hx
  have hprod : ∏ x ∈ s, a x ≤ (a m) ^ s.card := by
    calc ∏ x ∈ s, a x ≤ ∏ _x ∈ s, a m :=
          Finset.prod_le_prod (fun x hx => le_trans zero_le_one (ha x hx)) (fun x hx => hle x hx)
      _ = (a m) ^ s.card := Finset.prod_const _
  have hnonneg : 0 ≤ a m := le_trans zero_le_one hm1
  calc ∏ x ∈ s, a x ^ C
      = (∏ x ∈ s, a x) ^ C :=
        Real.finsetProd_rpow s a (fun x hx => le_trans zero_le_one (ha x hx)) C
    _ ≤ ((a m) ^ s.card) ^ C :=
        Real.rpow_le_rpow (Finset.prod_nonneg (fun x hx => le_trans zero_le_one (ha x hx))) hprod hC
    _ = ((a m) ^ ((s.card : ℝ))) ^ C := by rw [Real.rpow_natCast]
    _ = (a m) ^ ((s.card : ℝ) * C) := by rw [Real.rpow_mul hnonneg]
    _ = (a m) ^ (C * (s.card : ℝ)) := by rw [mul_comm]
    _ ≤ (a m) ^ E := Real.rpow_le_rpow_of_exponent_le hm1 hE
    _ ≤ ∑ x ∈ s, a x ^ E :=
        Finset.single_le_sum (f := fun x => a x ^ E)
          (fun x hx => Real.rpow_nonneg (le_trans zero_le_one (ha x hx)) E) hm_mem

theorem prod_one_add_mul_rpow_half_le_sum_pairs {n : ℕ} (hn : 2 ≤ n) {C E : ℝ} (hC : 1 ≤ C)
    (hE : C * (n : ℝ) ^ 2 ≤ E) (d : Fin n → Fin n → ℕ) (hd : ∀ i j, 1 ≤ d i j) :
    ∏ q ∈ (∏ i : Fin n, ∏ j ∈ Finset.univ.filter (fun j => i < j), d i j).primeFactors,
        (1 + C * (q : ℝ) ^ (-(1 / 2 : ℝ)))
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
  set g : ℕ → ℝ := fun q => 1 + C * (q : ℝ) ^ (-(1 / 2 : ℝ)) with hg
  set hh : ℕ → ℝ := fun q => 1 + (q : ℝ) ^ (-(1 / 2 : ℝ)) with hhh
  have hg1 : ∀ q : ℕ, 1 ≤ g q := by
    intro q
    have hC0 : 0 ≤ C := le_trans zero_le_one hC
    have hr : 0 ≤ (q : ℝ) ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg (Nat.cast_nonneg q) _
    rw [hg]
    exact le_add_of_nonneg_right (mul_nonneg hC0 hr)
  -- nonempty
  have hSne : S.Nonempty := by
    refine ⟨⟨⟨0, by omega⟩, ⟨1, by omega⟩⟩, ?_⟩
    rw [hS, Finset.mem_sigma]
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, by simp [Fin.lt_def]⟩
  -- card bound
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
  -- union step
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
  have hstepA : ∏ q ∈ (∏ p ∈ S, d p.1 p.2).primeFactors, g q
      ≤ ∏ p ∈ S, ∏ q ∈ (d p.1 p.2).primeFactors, g q := by
    refine le_trans ?_ (prod_biUnion_le S (fun p => (d p.1 p.2).primeFactors) g hg1)
    exact Finset.prod_le_prod_of_subset_of_one_le hsub
      (fun q _ => le_trans zero_le_one (hg1 q)) (fun q _ _ => hg1 q)
  -- bernoulli step
  have hstepB : ∀ p ∈ S, ∏ q ∈ (d p.1 p.2).primeFactors, g q
      ≤ (∏ q ∈ (d p.1 p.2).primeFactors, hh q) ^ C := by
    intro p hp
    rw [hg, hhh]
    calc ∏ q ∈ (d p.1 p.2).primeFactors, (1 + C * (q : ℝ) ^ (-(1 / 2 : ℝ)))
        ≤ ∏ q ∈ (d p.1 p.2).primeFactors, (1 + (q : ℝ) ^ (-(1 / 2 : ℝ))) ^ C := by
          apply Finset.prod_le_prod
          · intro q hq
            have hC0 : 0 ≤ C := le_trans zero_le_one hC
            have hr : 0 ≤ (q : ℝ) ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg (Nat.cast_nonneg q) _
            exact le_trans zero_le_one (le_add_of_nonneg_right (mul_nonneg hC0 hr))
          · intro q hq
            have hq0 : -1 ≤ (q : ℝ) ^ (-(1 / 2 : ℝ)) := by
              have := Real.rpow_nonneg (Nat.cast_nonneg q) (-(1 / 2 : ℝ)); linarith
            exact one_add_mul_self_le_rpow_one_add hq0 hC
      _ = (∏ q ∈ (d p.1 p.2).primeFactors, (1 + (q : ℝ) ^ (-(1 / 2 : ℝ)))) ^ C :=
          Real.finsetProd_rpow _ _ (fun q hq => by
            have := Real.rpow_nonneg (Nat.cast_nonneg q) (-(1 / 2 : ℝ)); linarith) C
  have hstepB' : ∏ p ∈ S, ∏ q ∈ (d p.1 p.2).primeFactors, g q
      ≤ ∏ p ∈ S, (∏ q ∈ (d p.1 p.2).primeFactors, hh q) ^ C := by
    apply Finset.prod_le_prod
    · intro p hp
      exact Finset.prod_nonneg (fun q hq => le_trans zero_le_one (hg1 q))
    · exact hstepB
  -- final combinatorial step
  have hC0 : 0 ≤ C := le_trans zero_le_one hC
  have hEcard : C * (S.card : ℝ) ≤ E := by
    have hcast : (S.card : ℝ) ≤ (n : ℝ) ^ 2 := by exact_mod_cast hcard
    calc C * (S.card : ℝ) ≤ C * (n : ℝ) ^ 2 := mul_le_mul_of_nonneg_left hcast hC0
      _ ≤ E := hE
  have hstepC : ∏ p ∈ S, (∏ q ∈ (d p.1 p.2).primeFactors, hh q) ^ C
      ≤ ∑ p ∈ S, (∏ q ∈ (d p.1 p.2).primeFactors, hh q) ^ E :=
    prod_rpow_le_sum_rpow S hSne _ (fun p hp => Finset.one_le_prod (fun q hq => by
      rw [hhh]
      exact le_add_of_nonneg_right (Real.rpow_nonneg (Nat.cast_nonneg q) _))) hC0 hEcard
  calc ∏ q ∈ (∏ p ∈ S, d p.1 p.2).primeFactors, g q
      ≤ ∏ p ∈ S, ∏ q ∈ (d p.1 p.2).primeFactors, g q := hstepA
    _ ≤ ∏ p ∈ S, (∏ q ∈ (d p.1 p.2).primeFactors, hh q) ^ C := hstepB'
    _ ≤ ∑ p ∈ S, (∏ q ∈ (d p.1 p.2).primeFactors, hh q) ^ E := hstepC

end Commons.NumberTheory.Sieve