import Mathlib
import Submission.Work.EKLC6Core.Basic
import Submission.Work.EKLContract.Interfaces

namespace Work.EKLC6Core

/-- **EKL (4) / Pisa 7.16, extracted from `P_Leafwise`'s second half.**

Given a leaf-wise system `ν` for a horospherical subgroup `U` with respect to an
`A`-invariant probability measure `μ`, the `A`-covariance of `ν` holds on a single conull
subset of the conull domain `X'` of `ν`.

The content is entirely in clause (U7) of the frozen contract `Work.EKLContract.P_Leafwise`:
the family `P_Leafwise` already asserts, for every leaf-wise system, the existence of such an
`A`-covariant conull set; here we simply expose it in the form `Work.EKLC6Core.ACovariant`
that the C6 development uses.

Note that clause (U7) is only available *after* choosing a contractible exponent vector
`t0` for `U` (the third field of `IsHoro U`) and exhibiting the corresponding
`MeasurePreserving` instance; both are supplied by the hypotheses. -/
theorem acovariant_of_leafwise (hLeaf : Work.EKLContract.P_Leafwise)
    {μ : MeasureTheory.Measure Work.EKLContract.X3} [MeasureTheory.IsProbabilityMeasure μ]
    (hAinv : Work.EKLContract.IsAInvariant μ) {U : Subgroup Work.EKLContract.SL3}
    (hU : Work.EKLContract.IsHoro U)
    {ν : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3}
    {X' : Set Work.EKLContract.X3} (hL : Work.EKLContract.IsLeafwise μ U ν X') :
    ∃ X'' : Set Work.EKLContract.X3,
      X'' ⊆ X' ∧ MeasurableSet X'' ∧ μ (X''ᶜ) = 0 ∧ Work.EKLC6Core.ACovariant ν X'' := by
  -- A contractible exponent vector for `U`, from the definition of `IsHoro`.
  obtain ⟨t0, ht0⟩ := hU.2.2
  -- The diagonal flow along `t0` preserves `μ`, by `A`-invariance.
  have hmp : MeasureTheory.MeasurePreserving
      (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t0 • x) μ μ := hAinv t0
  -- Clause (U7) of `P_Leafwise`, specialised to `ν`, `X'`, and unfolded to `ACovariant`.
  exact (((hLeaf μ U hU t0 hmp ht0).2 ν X' hL).2.2.2.2.2.2.1 hAinv)

end Work.EKLC6Core
