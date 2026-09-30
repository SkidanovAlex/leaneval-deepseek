import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.SD

/-- `θ c - θ a` is the sum of `log p` over the primes `p` with `a < p ≤ c`, i.e. with
`⌊a⌋₊ < p ≤ ⌊c⌋₊`. -/
theorem theta_sub_eq_sum_Ioc (a c : ℝ) (hac : a ≤ c) :
    Chebyshev.theta c - Chebyshev.theta a =
      ∑ p ∈ (Finset.Ioc ⌊a⌋₊ ⌊c⌋₊).filter Nat.Prime, Real.log (p : ℝ) := by
  have hmn : ⌊a⌋₊ ≤ ⌊c⌋₊ := Nat.floor_mono hac
  have hdisj : Disjoint ((Finset.Ioc 0 ⌊a⌋₊).filter Nat.Prime)
      ((Finset.Ioc ⌊a⌋₊ ⌊c⌋₊).filter Nat.Prime) :=
    (Finset.Ioc_disjoint_Ioc_of_le (a := 0) (b := ⌊a⌋₊) (c := ⌊a⌋₊) (d := ⌊c⌋₊) le_rfl).mono
      (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  have hU : (Finset.Ioc 0 ⌊c⌋₊).filter Nat.Prime =
      (Finset.Ioc 0 ⌊a⌋₊).filter Nat.Prime ∪ (Finset.Ioc ⌊a⌋₊ ⌊c⌋₊).filter Nat.Prime := by
    rw [← Finset.filter_union, Finset.Ioc_union_Ioc_eq_Ioc (Nat.zero_le _) hmn]
  have hsplit : Chebyshev.theta c = Chebyshev.theta a +
      ∑ p ∈ (Finset.Ioc ⌊a⌋₊ ⌊c⌋₊).filter Nat.Prime, Real.log (p : ℝ) := by
    simp only [Chebyshev.theta]
    rw [hU, Finset.sum_union hdisj]
  linarith [hsplit]

end Work.BMF.SD
