import Mathlib
import Submission.Work.Holonomy3.defs

namespace Work.Holonomy3

open Submission.CDTPlan
open scoped BigOperators

/-- Scalar multiplication by a rational `c` on a power series is multiplication by the constant
power series `C c`, and the polynomial coefficient `P` absorbs it:
`P · (c • f) = (P * C c) · f`. -/
private lemma poly_mul_smul (c : ℚ) (P : Polynomial ℚ) (f : PowerSeries ℚ) :
    (P : PowerSeries ℚ) * (c • f) =
      (((P * Polynomial.C c : Polynomial ℚ)) : PowerSeries ℚ) * f := by
  rw [PowerSeries.smul_eq_C_mul, ← Polynomial.coe_C, ← mul_assoc, ← Polynomial.coe_mul]

theorem scale_polyIndependent {m : ℕ} (q : ℕ) (hq : 0 < q) (f : Fin m → PowerSeries ℚ) (h : Submission.CDTPlan.PolyIndependent f) : Submission.CDTPlan.PolyIndependent (fun i => (q : ℚ)⁻¹ • f i) := by
  intro P hP
  have hc : (q : ℚ)⁻¹ ≠ 0 := by
    have hq' : (q : ℚ) ≠ 0 := by exact_mod_cast hq.ne'
    exact inv_ne_zero hq'
  have hP' : ∑ i, (((P i * Polynomial.C ((q : ℚ)⁻¹) : Polynomial ℚ)) : PowerSeries ℚ) * f i = 0 := by
    rw [← hP]
    exact Finset.sum_congr rfl fun i _ => (poly_mul_smul ((q : ℚ)⁻¹) (P i) (f i)).symm
  intro i
  have hz : P i * Polynomial.C ((q : ℚ)⁻¹) = 0 :=
    h (fun i => P i * Polynomial.C ((q : ℚ)⁻¹)) hP' i
  rcases mul_eq_zero.mp hz with h1 | h2
  · exact h1
  · exact absurd h2 (Polynomial.C_ne_zero.mpr hc)

end Work.Holonomy3
