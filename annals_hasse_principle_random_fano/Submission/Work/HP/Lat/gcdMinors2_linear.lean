import Mathlib
import Submission.Work.HP.Defs

namespace Work.HP.Lat

/-- For integers, the normalized `gcd`-monoid normalization is the absolute value. -/
lemma normalize_int_eq_natAbs (a : ℤ) : normalize a = (a.natAbs : ℤ) := by
  rw [← Int.abs_eq_normalize, Int.abs_eq_natAbs]

/-- The gcd of the `2 × 2` minors is multiplicative under forming linear combinations with a `2 × 2`
integer matrix: `gcdMinors2 (p x + q y) (r x + s y) = |p s - q r| * gcdMinors2 x y`. -/
theorem gcdMinors2_linear {ι : Type*} [Fintype ι] (x y : ι → ℤ) (p q r s : ℤ) :
    Work.HP.gcdMinors2 (p • x + q • y) (r • x + s • y)
      = (↑(Int.natAbs (p * s - q * r)) : ℤ) * Work.HP.gcdMinors2 x y := by
  -- Each `2 × 2` minor of `(p x + q y, r x + s y)` is `(p * s - q * r)` times the corresponding
  -- minor of `(x, y)`.
  have hpt : ∀ ij : ι × ι, ((p • x + q • y) ij.1) * ((r • x + s • y) ij.2)
      - ((p • x + q • y) ij.2) * ((r • x + s • y) ij.1)
      = (p * s - q * r) * (x ij.1 * y ij.2 - x ij.2 * y ij.1) := by
    intro ij
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [gcdMinors2, gcdMinors2]
  rw [Finset.gcd_congr rfl (fun ij _ => hpt ij), Finset.gcd_mul_left, normalize_int_eq_natAbs]

end Work.HP.Lat
