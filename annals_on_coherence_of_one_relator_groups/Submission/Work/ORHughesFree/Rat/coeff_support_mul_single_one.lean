import Mathlib
import Submission.Work.ORHughesFree.Rat.FreeProduct.Model

namespace Work.ORHughesFree.Rat

/-- Coefficients of the product with `single p 1` over `ℕ`: since `ℕ` has no zero divisors
(and sums of naturals vanish only if all terms do), the coefficient at `r` is the sum of the
coefficients of `z` at the elements `q` with `q * p = r`. -/
theorem coeff_mul_single_one_eq {M : Type} [Monoid M] [DecidableEq M]
    (z : MonoidAlgebra ℕ M) (p r : M) :
    (z * MonoidAlgebra.single p 1).coeff r =
      ∑ q ∈ z.coeff.support, if q * p = r then z.coeff q else 0 := by
  rw [MonoidAlgebra.coeff_mul, Finsupp.sum]
  apply Finset.sum_congr rfl
  intro q hq
  rw [MonoidAlgebra.single, MonoidAlgebra.coeff_ofCoeff, Finsupp.sum_single_index]
  · simp
  · simp

theorem coeff_support_mul_single_one {M : Type} [Monoid M] [DecidableEq M]
    (z : MonoidAlgebra ℕ M) (p : M) :
    (z * MonoidAlgebra.single p 1).coeff.support = (z.coeff.support).image (fun q => q * p) := by
  classical
  ext r
  rw [Finsupp.mem_support_iff, Finset.mem_image]
  constructor
  · intro h
    rw [coeff_mul_single_one_eq] at h
    obtain ⟨a, ha, ha'⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
    have hap : a * p = r := by
      by_contra hne
      exact ha' (by rw [if_neg hne])
    exact ⟨a, ha, hap⟩
  · rintro ⟨a, ha, rfl⟩
    rw [coeff_mul_single_one_eq, ← Nat.pos_iff_ne_zero, Finset.sum_pos_iff]
    exact ⟨a, ha, by rw [if_pos rfl]; exact Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp ha)⟩

end Work.ORHughesFree.Rat
