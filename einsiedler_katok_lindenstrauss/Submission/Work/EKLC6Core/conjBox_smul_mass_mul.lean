import Mathlib
import Submission.Work.EKLC6Core.Basic
import Submission.Work.EKLC6Core.Covariant
import Submission.Work.EKLC6Core.conjBox_measurable
import Submission.Work.EKLC6Core.conjBox_nhds

/-!
# `EKLC6Core.conjBox_smul_mass_mul`

The *two-box normalisation identity*: at a point `y ∈ X' ∩ X''` whose image `aDiag s · y` is
again in `X' ∩ X''`, the masses of the two conjugate boxes sum to the normalising constant:

`ν (aDiag s · y) (conjBox U s) * ν y (conjBox U (-s)) = 1`.

Equivalently, the "information" `-log ν y (conjBox U (-s))` at `y` is the information
`-log ν (aDiag s · y) (conjBox U s)` transported to the shifted point, i.e. the function
`growthFun U ν (-s)` is the `a`-shift of `growthFun U ν s` (up to sign).

The proof is the one-step covariance `covariant_step` with the exponent vector `-s` and the test
set `C = conjBox U s`: it reads

`ν (aDiag s · y) (conjBox U s) * ν y (conjBox U (-s)) = ν y (conjBy (-s) (conjBox U s))`,

and the conjugation action cancels the exponents,
`conjBy (-s) (conjBox U s) = conjBox U ((-s) + s) = conjBox U 0 = Box1 U`,
whose `ν y`-mass is `1` by the normalisation field of `IsLeafwise`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal
open LeanEval.Dynamics.EinsiedlerKatokLindenstrauss

set_option linter.unusedVariables false

noncomputable section

namespace Work.EKLC6Core

open Work.EKLContract

/-- **The two-box normalisation identity.**  For a leaf-wise system `(μ, ν)` on `X'` carried by
the horospherical subgroup `U`, with `A`-covariance on `X''`, and for any exponent vector `s`
and any `y ∈ X' ∩ X''` with `aDiag s · y ∈ X' ∩ X''`,

`ν (aDiag s · y) (conjBox U s) * ν y (conjBox U (-s)) = 1`. -/
theorem conjBox_smul_mass_mul {μ : MeasureTheory.Measure Work.EKLContract.X3}
    [MeasureTheory.IsProbabilityMeasure μ]
    {U : Subgroup Work.EKLContract.SL3}
    {ν : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3}
    {X' X'' : Set Work.EKLContract.X3}
    (hL : Work.EKLContract.IsLeafwise μ U ν X') (hcov : Work.EKLC6Core.ACovariant ν X'')
    (hU : Work.EKLContract.IsHoro U)
    (s : Fin 3 → ℝ) {y : Work.EKLContract.X3}
    (hy : y ∈ X' ∩ X'') (hy' : Work.EKLContract.aDiag s • y ∈ X' ∩ X'') :
    ν (Work.EKLContract.aDiag s • y) (Work.EKLC6Core.conjBox U s) *
      ν y (Work.EKLC6Core.conjBox U (-s)) = 1 := by
  -- One-step covariance with exponent vector `-s` and test set `conjBox U s`.
  have hstep := covariant_step hL hcov (measurableSet_box1 hU) (-s) hy
    (by simpa using hy') (C := conjBox U s) (conjBox_measurable hU s)
  -- `ν (aDiag s · y) (conjBox U s) * ν y (conjBox U (-s)) = ν y (conjBox U 0)`
  rw [neg_neg, conjBy_conjBox, neg_add_cancel, conjBox_zero] at hstep
  -- and `ν y (conjBox U 0) = ν y (Box1 U) = 1` by normalisation.
  rw [hstep, hL.normalised y hy.1]

end Work.EKLC6Core

end
