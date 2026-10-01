import Mathlib.Data.Nat.Totient

namespace Commons.Data.Nat

/-- For `m ≠ 0`, the gcd of `c` and `m` equals the sum of the totient function
over the divisors `k` of `m` which also divide `c`. -/
theorem gcd_eq_sum_totient_divisors_ne_zero {c m : ℕ} (hm : m ≠ 0) :
    Nat.gcd c m = ∑ k ∈ m.divisors.filter (fun k => k ∣ c), Nat.totient k := by
  rw [← Nat.sum_totient (Nat.gcd c m)]
  refine Finset.sum_congr ?_ ?_
  · ext k
    simp only [Finset.mem_filter, Nat.mem_divisors]
    constructor
    · intro h
      exact ⟨⟨h.1.trans (Nat.gcd_dvd_right c m), hm⟩, h.1.trans (Nat.gcd_dvd_left c m)⟩
    · intro h
      exact ⟨Nat.dvd_gcd h.2 h.1.1, fun hg => hm (Nat.gcd_eq_zero_iff.mp hg).2⟩
  · intro k _
    rfl

end Commons.Data.Nat