/-
# Area 4 / FI §15: the determinant `Δ` in coordinates (the congruence (15.1))

Elementary rewritings of `Δ(z₁,z₂) = Im(z̄₁z₂)` and its absolute value in terms of the coordinates
`zᵢ = rᵢ + i sᵢ`, together with the reduction of the divisibility `4d ∣ |Δ|` to a divisibility in
`ℤ` — this is what turns the arithmetic-progression condition of (15.1),
`r₁s₂ ≡ r₂s₁ (mod 4d)`, into `4d ∣ |Δ(z₁,z₂)|`.
-/
import Mathlib
import Submission.Work.FIPlan.Interface

namespace Work.FIArea4

open scoped BigOperators

/-- `Δ(z₁,z₂) = r₁s₂ - r₂s₁` (paper (6.1)/(15.1)). -/
lemma Delta_eq (z1 z2 : GaussianInt) :
    Work.FIPlan.Delta z1 z2 = z1.re * z2.im - z2.re * z1.im := by
  simp only [Work.FIPlan.Delta, Zsqrtd.im_mul, Zsqrtd.im_star, Zsqrtd.re_star]
  ring

/-- `Re(z̄₁z₂) = r₁r₂ + s₁s₂` (the numerator of the Jacobi symbol). -/
lemma re_star_mul_eq (z1 z2 : GaussianInt) :
    (star z1 * z2).re = z1.re * z2.re + z1.im * z2.im := by
  simp only [Zsqrtd.re_mul, Zsqrtd.re_star, Zsqrtd.im_star]
  ring

/-- `Δ(z₂,z₁) = -Δ(z₁,z₂)`. -/
lemma Delta_antisym (z1 z2 : GaussianInt) :
    Work.FIPlan.Delta z2 z1 = - Work.FIPlan.Delta z1 z2 := by
  rw [Delta_eq, Delta_eq]; ring

/-- `|Δ|` is symmetric. -/
lemma absDelta_comm (z1 z2 : GaussianInt) :
    Work.FIPlan.absDelta z2 z1 = Work.FIPlan.absDelta z1 z2 := by
  rw [Work.FIPlan.absDelta, Work.FIPlan.absDelta, Delta_antisym, Int.natAbs_neg]

/-- **The congruence (15.1)**: `4d ∣ |Δ(z₁,z₂)|` is exactly the divisibility in `ℤ` of
`r₁s₂ - r₂s₁` by `4d`. -/
lemma dvd_absDelta_iff (z1 z2 : GaussianInt) (d : ℕ) :
    (4 * d : ℕ) ∣ Work.FIPlan.absDelta z1 z2
      ↔ (4 * d : ℤ) ∣ (z1.re * z2.im - z2.re * z1.im) := by
  rw [Work.FIPlan.absDelta, Delta_eq]
  constructor
  · intro h
    have h' : (4 * d : ℤ) ∣ (((z1.re * z2.im - z2.re * z1.im)).natAbs : ℤ) := by
      exact_mod_cast h
    exact Int.dvd_natAbs.mp h'
  · intro h
    have h' : (4 * d : ℤ) ∣ (((z1.re * z2.im - z2.re * z1.im)).natAbs : ℤ) :=
      Int.dvd_natAbs.mpr h
    exact_mod_cast h'

/-- `gnorm` is multiplicative. -/
lemma gnorm_mul (z1 z2 : GaussianInt) :
    Work.FIPlan.gnorm (z1 * z2) = Work.FIPlan.gnorm z1 * Work.FIPlan.gnorm z2 := by
  simp [Work.FIPlan.gnorm, Zsqrtd.norm_mul, Int.natAbs_mul]

end Work.FIArea4
