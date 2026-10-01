import Mathlib

namespace Work.LinnikAreas.Density4

/-- Auxiliary real inequality: for any positive `s`,
`(s² - 1)(1 + 1/s)² ≤ s²(1 + 2/s)`. -/
private lemma sqrt_bound_aux (s : ℝ) (hs : 0 < s) :
    (s ^ 2 - 1) * (1 + 1 / s) ^ 2 ≤ s ^ 2 * (1 + 2 / s) := by
  field_simp
  nlinarith [sq_nonneg s, sq_nonneg (s + 1), sq_nonneg (s - 1)]

/-- The per-prime local inequality `(p-1)(1+p^{-1/2})² ≤ p(1+2p^{-1/2})`. -/
theorem prime_local_sqrt_bound (p : ℕ) (hp : p.Prime) :
    ((p : ℝ) - 1) * (1 + 1 / Real.sqrt (p : ℝ)) ^ 2
      ≤ (p : ℝ) * (1 + 2 / Real.sqrt (p : ℝ)) := by
  have hp_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  have hspos : 0 < Real.sqrt (p : ℝ) := Real.sqrt_pos.mpr hp_pos
  have hsq : Real.sqrt (p : ℝ) ^ 2 = (p : ℝ) := Real.sq_sqrt hp_pos.le
  have h := sqrt_bound_aux (Real.sqrt (p : ℝ)) hspos
  rwa [hsq] at h

end Work.LinnikAreas.Density4
