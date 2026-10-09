import Mathlib
import Submission.Work.HilbertSymbol.Places
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.HilbertSymbol

/-- `numDenNat a` is nonzero (indeed positive): it is `|num a| * den a` with `num a ≠ 0`. -/
private lemma numDenNat_pos (a : ℚˣ) : 0 < numDenNat a := by
  rw [numDenNat]
  exact Nat.mul_pos (Int.natAbs_pos.mpr (Rat.num_ne_zero.mpr a.ne_zero)) (Rat.den_pos _)

/-- `numDenNat` is submultiplicative for divisibility: the denominator-cleared numerator of a
product divides the product of the denominator-cleared numerators of the factors. -/
private lemma numDenNat_mul_dvd (a b : ℚˣ) : numDenNat (a * b) ∣ numDenNat a * numDenNat b := by
  have hnum : ((a : ℚ) * (b : ℚ)).num.natAbs ∣ (a : ℚ).num.natAbs * (b : ℚ).num.natAbs := by
    have h : ((a : ℚ) * (b : ℚ)).num ∣ (a : ℚ).num * (b : ℚ).num :=
      ⟨_, Rat.num_mul_num_eq_num_mul_gcd (a : ℚ) (b : ℚ)⟩
    have h2 := Int.natAbs_dvd_natAbs.mpr h
    rwa [Int.natAbs_mul] at h2
  have hden : ((a : ℚ) * (b : ℚ)).den ∣ (a : ℚ).den * (b : ℚ).den :=
    ⟨_, Rat.den_mul_den_eq_den_mul_gcd (a : ℚ) (b : ℚ)⟩
  have h := Nat.mul_dvd_mul hnum hden
  simp only [numDenNat, Units.val_mul]
  convert h using 1; ring

/-- The primes dividing `numDenNat (a * b)` are among those dividing `numDenNat a` or
`numDenNat b`. -/
private lemma primeFactors_numDenNat_mul_subset (a b : ℚˣ) :
    (numDenNat (a * b)).primeFactors ⊆ (numDenNat a).primeFactors ∪ (numDenNat b).primeFactors := by
  intro p hp
  obtain ⟨hpprime, hpdiv, _⟩ := Nat.mem_primeFactors.mp hp
  have hpdiv' : p ∣ numDenNat a * numDenNat b := hpdiv.trans (numDenNat_mul_dvd a b)
  rcases hpprime.dvd_mul.mp hpdiv' with h | h
  · exact Finset.mem_union_left _
      (Nat.mem_primeFactors.mpr ⟨hpprime, h, ne_of_gt (numDenNat_pos a)⟩)
  · exact Finset.mem_union_right _
      (Nat.mem_primeFactors.mpr ⟨hpprime, h, ne_of_gt (numDenNat_pos b)⟩)

theorem contributingPrimes_mul_subset (a a' b b' : ℚˣ) :
    contributingPrimes (a * a') (b * b')
      ⊆ contributingPrimes a b ∪ contributingPrimes a b' ∪ contributingPrimes a' b ∪ contributingPrimes a' b' := by
  intro p hp
  rw [mem_contributingPrimes] at hp
  have keyL : ∀ (x y : ℚˣ), p ∈ (numDenNat x).primeFactors → p ∈ contributingPrimes x y := by
    intro x y hx; rw [mem_contributingPrimes]; exact Or.inr (Or.inl hx)
  have keyR : ∀ (x y : ℚˣ), p ∈ (numDenNat y).primeFactors → p ∈ contributingPrimes x y := by
    intro x y hy; rw [mem_contributingPrimes]; exact Or.inr (Or.inr hy)
  rcases hp with rfl | hp | hp
  · exact Finset.mem_union_left _ (Finset.mem_union_left _
      (Finset.mem_union_left _ (two_mem_contributingPrimes a b)))
  · rcases Finset.mem_union.mp (primeFactors_numDenNat_mul_subset a a' hp) with h | h
    · exact Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_union_left _ (keyL a b h)))
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ (keyL a' b h))
  · rcases Finset.mem_union.mp (primeFactors_numDenNat_mul_subset b b' hp) with h | h
    · exact Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_union_left _ (keyR a b h)))
    · exact Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_union_right _ (keyR a b' h)))

end Work.HilbertSymbol
