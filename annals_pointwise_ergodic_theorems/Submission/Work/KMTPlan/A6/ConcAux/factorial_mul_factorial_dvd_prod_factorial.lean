import Mathlib

namespace Work.KMTPlan.A6.ConcAux

theorem factorial_mul_factorial_dvd_prod_factorial (d i : ℕ) (hi : i ≤ d) :
    i.factorial * (d - i).factorial ∣ ∏ j ∈ Finset.range (d + 1), j.factorial := by
  exact dvd_trans (Nat.factorial_mul_factorial_dvd_factorial hi)
    (Finset.dvd_prod_of_mem (fun j => j.factorial)
      (Finset.mem_range.mpr (Nat.lt_succ_self d)))

end Work.KMTPlan.A6.ConcAux
