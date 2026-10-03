import Mathlib

namespace Work.FIArea7

/-- If `g` is multiplicative on coprime arguments and `M`, `N` are coprime, then the sum of `g`
over the divisors of `M * N` is the product of the sums over the divisors of `M` and `N`. -/
lemma sum_divisors_mul_of_coprime {M N : ℕ} (hMN : M.Coprime N) {g : ℕ → ℝ}
    (hg : ∀ a b : ℕ, a.Coprime b → g (a * b) = g a * g b) :
    ∑ d ∈ (M * N).divisors, g d = (∑ d ∈ M.divisors, g d) * (∑ d ∈ N.divisors, g d) := by
  rw [Nat.divisors_mul, Finset.mul_def, Finset.sum_image (hMN.mul_injOn_divisors),
    Finset.sum_product]
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl (fun a ha => Finset.sum_congr rfl (fun b hb => ?_))
  rw [hg a b ((hMN.coprime_dvd_left (Nat.mem_divisors.mp ha).1).coprime_dvd_right
    (Nat.mem_divisors.mp hb).1)]

end Work.FIArea7
