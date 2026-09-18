import Mathlib.Data.Nat.Factorization.Basic

namespace Commons.NumberTheory.Nat

/-- The number of multiples of `q` in the interval `[1, m]` is `m / q`. -/
theorem card_multiples_Icc (m q : ℕ) :
    ((Finset.Icc 1 m).filter (fun h => q ∣ h)).card = m / q := by
  rw [show (Finset.Icc 1 m : Finset ℕ) = Finset.Ioc 0 m by
    ext x
    simp [Finset.mem_Icc, Finset.mem_Ioc]
    omega]
  exact Nat.Ioc_filter_dvd_card_eq_div m q

end Commons.NumberTheory.Nat