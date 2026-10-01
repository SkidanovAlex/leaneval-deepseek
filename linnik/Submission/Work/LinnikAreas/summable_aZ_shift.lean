import Mathlib
import Submission.Work.LinnikAreas.TFDefs
import Submission.Work.LinnikAreas.summable_int_of_ray
import Submission.Work.LinnikAreas.aZ_mul_summable_ray

namespace Work.LinnikAreas

/-- The `ℤ`-autocorrelation of `aZ r` with arbitrary integer shifts is summable:
`aZ r` is supported on the nonnegative integers and decays geometrically there, so the
product `p ↦ aZ r (p + k) * aZ r (p + l)` is supported on the ray `p ≥ max (-k) (-l)`
and decays like `(r^2)^p` along it. -/
theorem summable_aZ_shift (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) (k l : ℤ) :
    Summable (fun p : ℤ => aZ r (p + k) * aZ r (p + l)) := by
  -- `aZ r n` vanishes for negative `n`, so the product vanishes below `max (-k) (-l)`.
  set t : ℤ := max (-k) (-l) with ht
  have h0 : ∀ p : ℤ, p < t → aZ r (p + k) * aZ r (p + l) = 0 := by
    intro p hp
    rw [ht, lt_max_iff] at hp
    rcases hp with hp | hp
    · rw [aZ_eq_zero_of_neg r (by omega : p + k < 0), zero_mul]
    · rw [aZ_eq_zero_of_neg r (by omega : p + l < 0), mul_zero]
  -- Splitting the product off along the ray, the sum becomes the `ℕ`-indexed ray sum,
  -- which is eventually geometric with ratio `r ^ 2 < 1`.
  have hray : Summable (fun n : ℕ => aZ r ((n : ℤ) + (t + k)) * aZ r ((n : ℤ) + (t + l))) :=
    aZ_mul_summable_ray r hr0 hr1 (t + k) (t + l)
  have hray' :
      Summable (fun n : ℕ => (fun p : ℤ => aZ r (p + k) * aZ r (p + l)) (t + (n : ℤ))) := by
    convert hray using 1
    ext n
    dsimp only
    rw [show t + (n : ℤ) + k = (n : ℤ) + (t + k) by ring,
      show t + (n : ℤ) + l = (n : ℤ) + (t + l) by ring]
  exact summable_int_of_ray t h0 hray'

end Work.LinnikAreas
