import Mathlib

/-!
# The mean of the conditional measure of a set

For a probability measure `μ` on a standard Borel space and an arbitrary self-map `T`, the
conditional measure `condExpKernel μ (invariants T) x` is a version of the conditional
distribution given the σ-algebra of `T`-invariant measurable sets.  Its value on a measurable set
`S` is (a.e.) the conditional expectation `μ⟦S | invariants T⟧`, so integrating it against `μ`
recovers `μ S` by the law of total probability.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable section

namespace Work.EKLEntJacobs

theorem kernel_mean {X : Type} [mX : MeasurableSpace X] [StandardBorelSpace X]
    (μ : MeasureTheory.Measure X) [MeasureTheory.IsProbabilityMeasure μ]
    (T : X → X) {S : Set X} (hS : MeasurableSet S) :
    ∫ x, ((ProbabilityTheory.condExpKernel μ (MeasurableSpace.invariants T) x) S).toReal ∂μ
      = (μ S).toReal := by
  -- `invariants T` is a sub-σ-algebra of the ambient one.
  have hm : MeasurableSpace.invariants T ≤ mX := MeasurableSpace.invariants_le T
  -- The kernel value on `S` is a version of the conditional expectation `μ⟦S | invariants T⟧`.
  have hker := ProbabilityTheory.condExpKernel_ae_eq_condExp (μ := μ)
      (m := MeasurableSpace.invariants T) (mΩ := mX) hm hS
  have hker' : (fun x =>
        ((ProbabilityTheory.condExpKernel μ (MeasurableSpace.invariants T) x) S).toReal)
      =ᵐ[μ] μ[S.indicator fun _ => (1 : ℝ) | MeasurableSpace.invariants T] := by
    simpa only [Measure.real_def] using hker
  -- Replace the integrand by its a.e. equal conditional expectation.
  rw [integral_congr_ae hker']
  -- Law of total probability for conditional expectation.
  rw [integral_condExp hm]
  -- The integral of the indicator of `S` is `μ S`.
  rw [integral_indicator hS, setIntegral_const, smul_eq_mul, mul_one]
  rfl

end Work.EKLEntJacobs
