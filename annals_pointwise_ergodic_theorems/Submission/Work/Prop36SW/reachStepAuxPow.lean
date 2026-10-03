import Mathlib

namespace Work.Prop36SW

/-- Power bookkeeping for one reduction step: from `c * η ^ e ≤ γ` and `e * k ≤ M`
(so that multiplying the per-step constant `c` at most `e` times per unit of `k`,
i.e. `c ^ k * η ^ M`, is dominated by `(c * η ^ e) ^ k`) we get `c ^ k * η ^ M ≤ γ ^ k`.

The hypotheses `0 < η`, `η ≤ 1` make `η ^ ·` antitone, which is what lets the
`M`-th power of `η` be replaced by the (larger) `e * k`-th power. -/
theorem reachStepAuxPow {c γ η : ℝ} {e k M : ℕ} (hc : 0 ≤ c) (hη0 : 0 < η)
    (hη1 : η ≤ 1) (hmon : c * η ^ e ≤ γ) (hk : e * k ≤ M) :
    c ^ k * η ^ M ≤ γ ^ k := by
  have hη0' : (0 : ℝ) ≤ η := le_of_lt hη0
  have hck : (0 : ℝ) ≤ c ^ k := pow_nonneg hc k
  -- `η ^ M ≤ η ^ (e * k)` since `0 < η ≤ 1` and `e * k ≤ M`
  have h1 : η ^ M ≤ η ^ (e * k) := pow_le_pow_of_le_one hη0' hη1 hk
  have h2 : c ^ k * η ^ M ≤ c ^ k * η ^ (e * k) :=
    mul_le_mul_of_nonneg_left h1 hck
  have h3 : c ^ k * η ^ (e * k) = (c * η ^ e) ^ k := by
    rw [pow_mul, mul_pow]
  have h4 : (c * η ^ e) ^ k ≤ γ ^ k :=
    pow_le_pow_left₀ (mul_nonneg hc (pow_nonneg hη0' e)) hmon k
  calc c ^ k * η ^ M ≤ c ^ k * η ^ (e * k) := h2
    _ = (c * η ^ e) ^ k := h3
    _ ≤ γ ^ k := h4

end Work.Prop36SW
