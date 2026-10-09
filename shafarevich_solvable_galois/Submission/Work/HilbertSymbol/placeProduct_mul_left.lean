import Mathlib
import Submission.Work.HilbertSymbol.Places
import Submission.Work.HilbertSymbol.Symbol
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.HilbertSymbol

/-! ## Auxiliary facts about `numDenNat`, `padicVal` and the triviality of the Hilbert symbol
outside `contributingPrimes` -/

theorem numDenNat_ne_zero (a : ℚˣ) : numDenNat a ≠ 0 := by
  rw [numDenNat, mul_ne_zero_iff]
  exact ⟨Int.natAbs_ne_zero.mpr (Rat.num_ne_zero.mpr a.ne_zero), Rat.den_nz _⟩

theorem padicVal_eq_zero_of_not_mem_primeFactors {p : ℕ} (hp : p.Prime) {a : ℚˣ}
    (h : p ∉ (numDenNat a).primeFactors) : padicVal p a = 0 := by
  have hfac : Fact p.Prime := ⟨hp⟩
  have hnd : ¬ p ∣ numDenNat a := fun hd =>
    h ((Nat.mem_primeFactors).mpr ⟨hp, hd, numDenNat_ne_zero a⟩)
  rw [numDenNat, Nat.Prime.dvd_mul hp] at hnd
  push Not at hnd
  obtain ⟨h1, h2⟩ := hnd
  rw [padicVal_eq_zero_iff]
  refine ⟨fun hd => h1 ?_, h2⟩
  have := Int.natAbs_dvd_natAbs.mpr hd
  rwa [Int.natAbs_natCast] at this

theorem hilbertSymbol_some_eq_one_of_not_mem {p : ℕ} {a b : ℚˣ}
    (h : p ∉ contributingPrimes a b) : hilbertSymbol (some p) a b = 1 := by
  simp only [mem_contributingPrimes, not_or] at h
  obtain ⟨hp2, hp1, hp2'⟩ := h
  by_cases hprime : p.Prime
  · have hfac : Fact p.Prime := ⟨hprime⟩
    rw [hilbertSymbol_some, hilbertSymbolAtPrime_eq_odd hp2,
      hilbertSymbolOdd_eq_one_of_padicVal_eq_zero
        (padicVal_eq_zero_of_not_mem_primeFactors hprime hp1)
        (padicVal_eq_zero_of_not_mem_primeFactors hprime hp2')]
  · simp only [hilbertSymbol, dif_neg hprime]

theorem placeProd_eq_prod_of_subset {a b : ℚˣ} {S : Finset ℕ}
    (h : contributingPrimes a b ⊆ S) :
    placeProd a b = ∏ p ∈ S, hilbertSymbol (some p) a b := by
  rw [placeProd]
  exact Finset.prod_subset h fun x _ hx => hilbertSymbol_some_eq_one_of_not_mem hx

theorem placeProduct_eq_prod_of_subset {a b : ℚˣ} {S : Finset ℕ}
    (h : contributingPrimes a b ⊆ S) :
    placeProduct a b = (∏ p ∈ S, hilbertSymbol (some p) a b) * hilbertSymbol none a b := by
  show placeProd a b * hilbertSymbol none a b = _
  rw [placeProd_eq_prod_of_subset h]

theorem placeProduct_mul_left (a₁ a₂ b : ℚˣ) :
    placeProduct (a₁ * a₂) b = placeProduct a₁ b * placeProduct a₂ b := by
  set S : Finset ℕ := contributingPrimes (a₁ * a₂) b ∪ contributingPrimes a₁ b
    ∪ contributingPrimes a₂ b with hS
  have hsub1 : contributingPrimes (a₁ * a₂) b ⊆ S := by
    rw [hS]; exact Finset.subset_union_left.trans Finset.subset_union_left
  have hsub2 : contributingPrimes a₁ b ⊆ S := by
    rw [hS]; exact Finset.subset_union_right.trans Finset.subset_union_left
  have hsub3 : contributingPrimes a₂ b ⊆ S := by
    rw [hS]; exact Finset.subset_union_right
  have e1 := placeProduct_eq_prod_of_subset (a := a₁ * a₂) (b := b) hsub1
  have e2 := placeProduct_eq_prod_of_subset (a := a₁) (b := b) hsub2
  have e3 := placeProduct_eq_prod_of_subset (a := a₂) (b := b) hsub3
  have hkey : ∏ p ∈ S, hilbertSymbol (some p) (a₁ * a₂) b
      = (∏ p ∈ S, hilbertSymbol (some p) a₁ b) * (∏ p ∈ S, hilbertSymbol (some p) a₂ b) := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun p _ => hilbertSymbol_mul_left (some p) a₁ a₂ b
  rw [e1, e2, e3, hkey, hilbertSymbol_mul_left, mul_mul_mul_comm]

end Work.HilbertSymbol
