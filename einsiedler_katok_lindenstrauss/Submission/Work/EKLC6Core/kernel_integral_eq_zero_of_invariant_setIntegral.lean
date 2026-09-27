import Mathlib
import Submission.Work.EKLC6Core.FibreAlongDefs

open MeasureTheory ProbabilityTheory

namespace Work.EKLC6Core

/-- If the integral of `g` over every `T`-invariant measurable set vanishes, then the integral of
`g` against the conditional kernel `condExpKernel μ (invariants T)` vanishes for `μ`-a.e. point. -/
theorem kernel_integral_eq_zero_of_invariant_setIntegral
    {μ : MeasureTheory.Measure Work.EKLContract.X3} [MeasureTheory.IsProbabilityMeasure μ]
    {T : Work.EKLContract.X3 → Work.EKLContract.X3} {g : Work.EKLContract.X3 → ℝ}
    (hg : MeasureTheory.Integrable g μ)
    (hzero : ∀ E : Set Work.EKLContract.X3,
      @MeasurableSet Work.EKLContract.X3 (MeasurableSpace.invariants T) E →
      ∫ y in E, g y ∂μ = 0) :
    ∀ᵐ x ∂μ, ∫ y, g y ∂(ProbabilityTheory.condExpKernel μ
      (MeasurableSpace.invariants T) x) = 0 := by
  -- The invariant σ-algebra is a sub-σ-algebra of the Borel σ-algebra of `X₃`.
  have hm : MeasurableSpace.invariants T ≤ Work.EKLContract.instMeasurableSpaceX3 :=
    MeasurableSpace.invariants_le T
  -- `condExpKernel μ (invariants T)` computes the conditional expectation: `E[g | invariants T]`
  -- agrees a.e. with the integral of `g` against the conditional kernel.
  have hcond := ProbabilityTheory.condExp_ae_eq_integral_condExpKernel
    (μ := μ) (m := MeasurableSpace.invariants T)
    (mΩ := Work.EKLContract.instMeasurableSpaceX3) hm hg
  -- It therefore suffices to show that `E[g | invariants T] = 0` a.e.
  have hceq : μ[g | MeasurableSpace.invariants T] =ᵐ[μ] (0 : Work.EKLContract.X3 → ℝ) := by
    symm
    -- Uniqueness of the conditional expectation: `0` is `invariants T`-measurable, integrable on
    -- every finite measure set, and has the same integral as `g` on every `invariants T`-measurable
    -- set (by hypothesis).
    refine MeasureTheory.ae_eq_condExp_of_forall_setIntegral_eq (m := MeasurableSpace.invariants T)
      (m₀ := Work.EKLContract.instMeasurableSpaceX3) hm hg ?_ ?_ ?_
    · intro s _ _
      exact MeasureTheory.integrableOn_zero
    · intro s hs _
      rw [hzero s hs]
      simp
    · exact aestronglyMeasurable_zero
  filter_upwards [hcond, hceq] with x hx hz
  rw [← hx]
  exact hz

end Work.EKLC6Core
