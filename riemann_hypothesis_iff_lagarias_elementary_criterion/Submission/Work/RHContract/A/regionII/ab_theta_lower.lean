import Mathlib
import Submission.Work.RHContract.A.regionII.abdefs

namespace Work.RHContract.A.regionII

/-- From a certified upper bound for the Chebyshev deficit `m - θ m ≤ (189/100)√m` at
*integers* `m ∈ [n, 501]`, we obtain the corresponding *real* lower bound
`t - 1 - (189/100)√t ≤ θ t` on `[n, 501]`.

Indeed, for `t ∈ [n, 501]` put `m = ⌊t⌋₊`.  Then `n ≤ m ≤ 501`, `θ t = θ m`
(`Chebyshev.theta_eq_theta_coe_floor`), `t - 1 < m` and `√m ≤ √t`, so
`t - 1 - (189/100)√t ≤ m - (189/100)√m ≤ θ m = θ t`. -/
lemma ab_theta_lower (n : ℕ)
    (hθint : ∀ m : ℕ, n ≤ m → m ≤ 501 → (m:ℝ) - Chebyshev.theta (m:ℝ) ≤ (189/100) * Real.sqrt m) :
    ∀ t : ℝ, (n:ℝ) ≤ t → t ≤ 501 → t - 1 - (189/100) * Real.sqrt t ≤ Chebyshev.theta t := by
  intro t ht_ge ht_le
  set m := ⌊t⌋₊ with hm
  have ht_nonneg : (0:ℝ) ≤ t := by
    have : (0:ℝ) ≤ (n:ℝ) := by positivity
    linarith
  have hm_ge_n : n ≤ m := by
    rw [hm]; exact Nat.le_floor ht_ge
  have hm_le : m ≤ 501 := by
    rw [hm]
    have h := Nat.floor_le_floor ht_le
    simpa using h
  have hbound := hθint m hm_ge_n hm_le
  have hθeq : Chebyshev.theta t = Chebyshev.theta (m:ℝ) := by
    rw [Chebyshev.theta_eq_theta_coe_floor t]
  have hfloor_le : (m:ℝ) ≤ t := by
    rw [hm]; exact Nat.floor_le ht_nonneg
  have hlt : t < (m:ℝ) + 1 := by
    rw [hm]; exact Nat.lt_floor_add_one t
  have hs : Real.sqrt (m:ℝ) ≤ Real.sqrt t := Real.sqrt_le_sqrt hfloor_le
  have h1 : t - 1 - (189/100) * Real.sqrt t ≤ (m:ℝ) - (189/100) * Real.sqrt (m:ℝ) := by
    have hc : (189/100:ℝ) * Real.sqrt (m:ℝ) ≤ (189/100) * Real.sqrt t := by
      nlinarith
    linarith
  rw [hθeq]
  linarith [hbound, h1]

end Work.RHContract.A.regionII
