import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.GE.Gest

/-- **Cauchy–Schwarz (absolute value form)** for real finite sums:
`|∑ᵢ aᵢ bᵢ| ≤ √(∑ᵢ aᵢ²) · √(∑ᵢ bᵢ²)`.  Obtained by squaring (`Finset.sum_mul_sq_le_sq_mul_sq`),
taking square roots (`Real.sqrt_le_sqrt`), and splitting `√(XY) = √X √Y`. -/
theorem sum_mul_abs_le {n : ℕ} (a b : Fin n → ℝ) :
    |∑ i, a i * b i| ≤ Real.sqrt (∑ i, a i ^ 2) * Real.sqrt (∑ i, b i ^ 2) := by
  have hsq : (∑ i, a i * b i) ^ 2 ≤ (∑ i, a i ^ 2) * (∑ i, b i ^ 2) :=
    Finset.sum_mul_sq_le_sq_mul_sq Finset.univ a b
  calc |∑ i, a i * b i| = Real.sqrt ((∑ i, a i * b i) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt ((∑ i, a i ^ 2) * (∑ i, b i ^ 2)) := Real.sqrt_le_sqrt hsq
    _ = Real.sqrt (∑ i, a i ^ 2) * Real.sqrt (∑ i, b i ^ 2) :=
        Real.sqrt_mul (Finset.sum_nonneg fun i _ => sq_nonneg _) _

end Work.Diff.GE.Gest
