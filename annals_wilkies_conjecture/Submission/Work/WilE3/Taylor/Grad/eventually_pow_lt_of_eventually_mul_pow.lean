import Mathlib

namespace Work.WilE3.Taylor.Grad

/-- If near `0` from the right `G t = t ^ n * g t` and `F t = t ^ k * h t`, and if
`(G t) ^ q < (F t) ^ (2 * p)` eventually, then `(g t) ^ q < t ^ d * (h t) ^ (2 * p)`
eventually, provided `2 * p * k = q * n + d`.

Indeed `(t ^ n * g t) ^ q = t ^ (n * q) * (g t) ^ q` and
`(t ^ k * h t) ^ (2 * p) = t ^ (k * (2 * p)) * (h t) ^ (2 * p)
= t ^ (n * q) * t ^ d * (h t) ^ (2 * p)`, so cancelling the positive factor
`t ^ (n * q)` (positive since `t > 0` near `0⁺`) gives the claim. -/
theorem eventually_pow_lt_of_eventually_mul_pow {G F g h : ℝ → ℝ} {n k q p d : ℕ} (hd : 2 * p * k = q * n + d) (hG : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), G t = t ^ n * g t) (hF : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), F t = t ^ k * h t) (hineq : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), (G t) ^ q < (F t) ^ (2 * p)) : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), (g t) ^ q < t ^ d * (h t) ^ (2 * p) := by
  filter_upwards [hG, hF, hineq, self_mem_nhdsWithin] with t hGt hFt hineq_t ht
  rw [hGt, hFt] at hineq_t
  rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul] at hineq_t
  have hkp : k * (2 * p) = n * q + d := by rw [mul_comm k (2 * p), hd, mul_comm q n]
  rw [hkp, pow_add] at hineq_t
  rw [mul_assoc] at hineq_t
  have htpos : 0 < t ^ (n * q) := pow_pos ht _
  exact lt_of_mul_lt_mul_left hineq_t (le_of_lt htpos)

end Work.WilE3.Taylor.Grad
