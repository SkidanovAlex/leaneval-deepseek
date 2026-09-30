import Mathlib
import Submission.Work.BW.poly_natDegree_eventually_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- A polynomial over `ℚ` that is eventually bounded below by `c·t^n` with `c > 0`
along the naturals has degree at least `n`. -/
theorem le_natDegree_of_eventually_le_pow {p : Polynomial ℚ} {n : ℕ} {c : ℚ} (hc : 0 < c)
    (hlower : ∀ᶠ t : ℕ in Filter.atTop, c * (t : ℚ) ^ n ≤ p.eval (t : ℚ)) :
    n ≤ p.natDegree := by
  have hcne : c ≠ 0 := ne_of_gt hc
  have heval : ∀ x : ℚ, (Polynomial.C c * Polynomial.X ^ n).eval x = c * x ^ n := fun x => by simp
  -- Reinterpret the lower bound as a comparison with the polynomial `c·X^n`.
  have hle : ∀ᶠ t : ℕ in Filter.atTop,
      (Polynomial.C c * Polynomial.X ^ n).eval (t : ℚ) ≤ p.eval (t : ℚ) := by
    filter_upwards [hlower] with t ht
    rwa [heval]
  -- That polynomial is nonnegative on the naturals because `c > 0`.
  have hQ : ∀ᶠ t : ℕ in Filter.atTop,
      0 ≤ (Polynomial.C c * Polynomial.X ^ n).eval (t : ℚ) := by
    filter_upwards with t
    rw [heval]
    positivity
  have h := poly_natDegree_eventually_le hle hQ
  rwa [Polynomial.natDegree_C_mul_X_pow n c hcne] at h

end Work.BW
