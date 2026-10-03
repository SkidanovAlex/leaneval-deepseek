import Mathlib
import Submission.Work.FIArea4.GaussMoebiusCore

namespace Work.FIArea4.A4c

/-- Purely arithmetic counting lemma.

If `S` is a multiset of natural numbers each `≥ 2` whose product is squarefree, then the number
of terms of `S` is at most the number of distinct prime divisors of its product.

Indeed, squarefreeness of the product forces the terms to be pairwise coprime and each term to be
squarefree, so every term contributes at least one new prime divisor. -/
theorem multiset_card_le_primeFactors_card_prod (S : Multiset ℕ)
    (h2 : ∀ a ∈ S, 2 ≤ a) (hsq : Squarefree S.prod) :
    S.card ≤ S.prod.primeFactors.card := by
  induction S using Multiset.induction with
  | empty => simp
  | cons a S' ih =>
    have ha2 : 2 ≤ a := h2 a (Multiset.mem_cons_self a S')
    have h2' : ∀ b ∈ S', 2 ≤ b := fun b hb => h2 b (Multiset.mem_cons_of_mem hb)
    have hprod : (a ::ₘ S').prod = a * S'.prod := Multiset.prod_cons a S'
    have hsq' : Squarefree S'.prod :=
      hsq.squarefree_of_dvd (by rw [hprod]; exact dvd_mul_left _ _)
    have ih' := ih h2' hsq'
    have ha0 : a ≠ 0 := by omega
    have ha1 : a ≠ 1 := by omega
    have hS'0 : S'.prod ≠ 0 := Multiset.prod_ne_zero (fun h => by have := h2' 0 h; omega)
    have hpf : (a * S'.prod).primeFactors = a.primeFactors ∪ S'.prod.primeFactors :=
      Nat.primeFactors_mul ha0 hS'0
    obtain ⟨p, hpprime, hpdvd⟩ := Nat.exists_prime_and_dvd ha1
    have hpA : p ∈ a.primeFactors := hpprime.mem_primeFactors hpdvd ha0
    have hpB : p ∉ S'.prod.primeFactors := by
      intro hpBmem
      have hpdvdB : p ∣ S'.prod := Nat.dvd_of_mem_primeFactors hpBmem
      have hpp : p * p ∣ a * S'.prod := mul_dvd_mul hpdvd hpdvdB
      have hunit : IsUnit p := hsq p (by rw [hprod]; exact hpp)
      have hp1 : p = 1 := Nat.isUnit_iff.mp hunit
      have hp2 : 2 ≤ p := hpprime.two_le
      omega
    have hsub : insert p S'.prod.primeFactors ⊆ a.primeFactors ∪ S'.prod.primeFactors := by
      intro x hx
      rw [Finset.mem_insert] at hx
      rcases hx with rfl | hx
      · exact Finset.mem_union_left _ hpA
      · exact Finset.mem_union_right _ hx
    have hcard : (insert p S'.prod.primeFactors).card = S'.prod.primeFactors.card + 1 :=
      Finset.card_insert_of_notMem hpB
    have hkey : S'.prod.primeFactors.card + 1 ≤ (a ::ₘ S').prod.primeFactors.card := by
      rw [hprod, hpf]
      calc S'.prod.primeFactors.card + 1
          = (insert p S'.prod.primeFactors).card := hcard.symm
        _ ≤ (a.primeFactors ∪ S'.prod.primeFactors).card := Finset.card_le_card hsub
    rw [Multiset.card_cons]
    exact le_trans (Nat.add_le_add_right ih' 1) hkey

/-- `gnorm` is multiplicative over multiset products. -/
theorem gnorm_multiset_prod (S : Multiset GaussianInt) :
    (S.map Work.FIPlan.gnorm).prod = Work.FIPlan.gnorm S.prod := by
  induction S using Multiset.induction with
  | empty => simp [Work.FIArea4.gnorm_one]
  | cons x S' ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, Multiset.prod_cons, Work.FIArea4.gnorm_mul, ih]

theorem card_normalizedFactors_le_primeFactors_card (z : GaussianInt) (hz : z ≠ 0)
    (hsq : Squarefree (Work.FIPlan.gnorm z)) :
    (UniqueFactorizationMonoid.normalizedFactors z).card ≤ (Work.FIPlan.gnorm z).primeFactors.card := by
  have hmap_prod :
      ((UniqueFactorizationMonoid.normalizedFactors z).map Work.FIPlan.gnorm).prod
        = Work.FIPlan.gnorm z := by
    rw [gnorm_multiset_prod]
    exact Work.FIArea4.gnorm_eq_of_associated
      (UniqueFactorizationMonoid.prod_normalizedFactors hz)
  have h2 : ∀ a ∈ (UniqueFactorizationMonoid.normalizedFactors z).map Work.FIPlan.gnorm, 2 ≤ a := by
    intro a ha
    rw [Multiset.mem_map] at ha
    obtain ⟨π, hπ, hπa⟩ := ha
    rw [← hπa]
    have hprime := UniqueFactorizationMonoid.prime_of_normalized_factor π hπ
    have hπne : π ≠ 0 := UniqueFactorizationMonoid.ne_zero_of_mem_normalizedFactors hπ
    have hpos : 1 ≤ Work.FIPlan.gnorm π := Work.FIArea4.gnorm_pos hπne
    have hne1 : Work.FIPlan.gnorm π ≠ 1 := by
      intro h1
      have h1' : π.norm.natAbs = 1 := by simpa [Work.FIPlan.gnorm] using h1
      exact hprime.not_isUnit (Zsqrtd.norm_eq_one_iff.mp h1')
    omega
  have hsq' :
      Squarefree ((UniqueFactorizationMonoid.normalizedFactors z).map Work.FIPlan.gnorm).prod := by
    rw [hmap_prod]; exact hsq
  have key := multiset_card_le_primeFactors_card_prod
      ((UniqueFactorizationMonoid.normalizedFactors z).map Work.FIPlan.gnorm) h2 hsq'
  rw [Multiset.card_map, hmap_prod] at key
  exact key

end Work.FIArea4.A4c
