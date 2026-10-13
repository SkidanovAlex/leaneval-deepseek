import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Coercivity.holder_two_mul
import Submission.Work.Coercivity.integrable_sqrt_mul_sqrt
import Submission.Work.FTS.EllipticEst.AngSecond.abs_setIntegral_le_sqrt_mul_sqrt

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.AngSecond

open MeasureTheory

/-- **Weighted Cauchy–Schwarz for `∫_s m·√A·√B`.**

If `m`, `A`, `B` are nonnegative and the *products* `m·A`, `m·B` are integrable on `s`, then the
weighted pairing `m·√A·√B` is integrable on `s` and

  `∫_s m·√A·√B ≤ √(∫_s m·A) · √(∫_s m·B)`.

The point is that no measurability of `m`, `A`, `B` themselves is assumed — only of the products
`m·A`, `m·B` (through their integrability).  Indeed `m·√A·√B = √(m·A)·√(m·B)` pointwise (all three
factors being nonnegative), and the right-hand side is a product of two functions that are
a.e. strongly measurable *because* `m·A` and `m·B` are integrable.  Integrability of the product
follows from the AM–GM domination `√(m·A)·√(m·B) ≤ ((m·A) + (m·B))/2`
(`Work.Coercivity.integrable_sqrt_mul_sqrt`), and the inequality is the ordinary Cauchy–Schwarz in
the weighted `L²` space (`Work.FTS.EllipticEst.AngSecond.abs_setIntegral_le_sqrt_mul_sqrt`), the
nonnegativity replacing the absolute value on the left. -/
theorem setIntegral_w_mul_sqrt_le {s : Set ℝ} {m A B : ℝ → ℝ}
    (hm : ∀ z, 0 ≤ m z) (hA : ∀ z, 0 ≤ A z) (hB : ∀ z, 0 ≤ B z)
    (hAi : MeasureTheory.IntegrableOn (fun z => m z * A z) s)
    (hBi : MeasureTheory.IntegrableOn (fun z => m z * B z) s) :
    MeasureTheory.IntegrableOn (fun z => m z * Real.sqrt (A z) * Real.sqrt (B z)) s
      ∧ ∫ z in s, m z * Real.sqrt (A z) * Real.sqrt (B z)
        ≤ Real.sqrt (∫ z in s, m z * A z) * Real.sqrt (∫ z in s, m z * B z) := by
  have hmA : ∀ z, 0 ≤ m z * A z := fun z => mul_nonneg (hm z) (hA z)
  have hmB : ∀ z, 0 ≤ m z * B z := fun z => mul_nonneg (hm z) (hB z)
  have hnonneg : ∀ z, 0 ≤ m z * Real.sqrt (A z) * Real.sqrt (B z) :=
    fun z => mul_nonneg (mul_nonneg (hm z) (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
  -- `m·√A·√B = √(m·A)·√(m·B)`, pointwise, for nonnegative `m`, `A`, `B`
  have hkey : ∀ z, Real.sqrt (m z * A z) * Real.sqrt (m z * B z)
      = m z * Real.sqrt (A z) * Real.sqrt (B z) := by
    intro z
    rw [Real.sqrt_mul (hm z) (A z), Real.sqrt_mul (hm z) (B z)]
    have hsq : Real.sqrt (m z) * Real.sqrt (m z) = m z := by
      rw [← sq, Real.sq_sqrt (hm z)]
    calc (Real.sqrt (m z) * Real.sqrt (A z)) * (Real.sqrt (m z) * Real.sqrt (B z))
        = (Real.sqrt (m z) * Real.sqrt (m z)) * (Real.sqrt (A z) * Real.sqrt (B z)) := by ring
      _ = m z * Real.sqrt (A z) * Real.sqrt (B z) := by rw [hsq]; ring
  -- integrability of the product, by AM–GM domination
  have hprod : Integrable (fun z => Real.sqrt (m z * A z) * Real.sqrt (m z * B z))
      (volume.restrict s) :=
    Work.Coercivity.integrable_sqrt_mul_sqrt (volume.restrict s)
      (fun z => m z * A z) (fun z => m z * B z) hAi hBi hmA hmB
  have hCint : MeasureTheory.IntegrableOn
      (fun z => m z * Real.sqrt (A z) * Real.sqrt (B z)) s :=
    hprod.congr (Filter.Eventually.of_forall hkey)
  refine ⟨hCint, ?_⟩
  -- the pointwise domination needed for the abstract Cauchy–Schwarz step
  have hslice : ∀ z ∈ s, |m z * Real.sqrt (A z) * Real.sqrt (B z)|
      ≤ Real.sqrt (m z * A z) * Real.sqrt (m z * B z) := by
    intro z _
    rw [abs_of_nonneg (hnonneg z)]
    exact (hkey z).symm.le
  have hbound := abs_setIntegral_le_sqrt_mul_sqrt (s := s)
    (A := fun z => m z * A z) (B := fun z => m z * B z)
    (C := fun z => m z * Real.sqrt (A z) * Real.sqrt (B z))
    hAi hBi hCint (fun z _ => hmA z) (fun z _ => hmB z) hslice
  have hpos : 0 ≤ ∫ z in s, m z * Real.sqrt (A z) * Real.sqrt (B z) :=
    integral_nonneg_of_ae (Filter.Eventually.of_forall hnonneg)
  calc ∫ z in s, m z * Real.sqrt (A z) * Real.sqrt (B z)
      = |∫ z in s, m z * Real.sqrt (A z) * Real.sqrt (B z)| := (abs_of_nonneg hpos).symm
    _ ≤ Real.sqrt (∫ z in s, m z * A z) * Real.sqrt (∫ z in s, m z * B z) := hbound

end Work.FTS.EllipticEst.AngSecond
