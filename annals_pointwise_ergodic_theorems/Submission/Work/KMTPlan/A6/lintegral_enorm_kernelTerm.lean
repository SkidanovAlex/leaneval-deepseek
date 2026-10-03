import Mathlib
import Submission.Work.KMTPlan.A6.SymSeq_coeff1

namespace Work.KMTPlan.A6

open MeasureTheory intervalIntegral
open scoped ENNReal

/-- The modulus of the character `e(z) = exp (2πiz)`, as an `ℝ≥0∞`-valued norm. -/
lemma enorm_eeC (z : ℝ) : ‖eeC z‖ₑ = 1 := by
  rw [show ‖eeC z‖ₑ = ENNReal.ofReal ‖eeC z‖ from by simp [enorm_eq_nnnorm], norm_eeC z]
  simp

/-- The pointwise kernel of the bilinear polynomial average has modulus
`‖K‖ ‖κ‖ ‖κ'‖`; integrating over the period `(0,1]` of total measure one gives that value. -/
theorem lintegral_enorm_kernelTerm (K : ℤ → ℤ → ℂ) (κ κ' : ℤ → ℂ) (p₁ p₂ : ℤ) (x : ℝ)
    (w : (ℤ × ℤ) × (ℤ × ℤ)) :
    ∫⁻ y, enorm ((K w.1.1 w.1.2 * Work.KMTPlan.A6.eeC (w.1.1 * x + w.1.2 * y))
          * (κ w.2.1 * Work.KMTPlan.A6.eeC (w.2.1 * x)
              * (κ' w.2.2 * Work.KMTPlan.A6.eeC (w.2.2 * y)))
          * Work.KMTPlan.A6.eeC (-(p₁ : ℝ) * x - (p₂ : ℝ) * y))
        ∂(MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) 1))
      = enorm (K w.1.1 w.1.2) * enorm (κ w.2.1) * enorm (κ' w.2.2) := by
  have hconst : (fun y : ℝ => enorm ((K w.1.1 w.1.2 * eeC (w.1.1 * x + w.1.2 * y))
          * (κ w.2.1 * eeC (w.2.1 * x)
              * (κ' w.2.2 * eeC (w.2.2 * y)))
          * eeC (-(p₁ : ℝ) * x - (p₂ : ℝ) * y)))
        = fun _ : ℝ => enorm (K w.1.1 w.1.2) * enorm (κ w.2.1) * enorm (κ' w.2.2) := by
    funext y
    simp only [enorm_mul, enorm_eeC, mul_one]
    rw [mul_assoc]
  rw [hconst, lintegral_const]
  simp

end Work.KMTPlan.A6
