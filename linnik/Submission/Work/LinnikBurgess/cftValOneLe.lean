import Mathlib

namespace Work.LinnikBurgess

/-- For a prime `p` and a nonzero integer `z`, the `p`-adic valuation of `z` is at least `1`
exactly when `p` divides `z`. -/
lemma cftValOneLe {p : ℕ} [Fact p.Prime] {z : ℤ} (hz : z ≠ 0) :
    1 ≤ padicValInt p z ↔ (p : ℤ) ∣ z := by
  have h := padicValInt_dvd_iff (p := p) 1 z
  rw [pow_one] at h
  rw [h]
  simp [hz]

end Work.LinnikBurgess
