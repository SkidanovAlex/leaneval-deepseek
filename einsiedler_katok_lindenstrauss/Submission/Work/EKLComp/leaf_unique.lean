import Mathlib
import Submission.Work.EKLComp.prove_X3
import Submission.Work.EKLRelCross.leafwise_unique

/-!
# Clause (U1) of the frozen contract: uniqueness of the leafwise measures

The uniqueness statement `Work.EKLRelCross.leafwise_unique` (Pisa Theorem 6.3) is proved there
from the background component `Work.EKLContract.P_X3` (`T₂`, Polish, Mahler compactness, uniform
injectivity, openness of the orbit maps of `X₃`), which is unconditional for `SL₃(ℝ)/SL₃(ℤ)` and
is proved in `Submission/Work/EKLComp/prove_X3.lean`.  This module discharges that hypothesis.

The mathematical content is: any two systems of leafwise measures `ν`, `ν'` for the same
probability `μ` and horospherical `U` contracted by the same measure-preserving `α^{t₀}` satisfy
the same conditional-expectation identity against every plaque algebra.  Since the left-hand side
of that identity does not involve the system, the pushforwards of `ν x|_S` and `ν' x|_S` under
`u ↦ u • x` are proportional on each shape `S`; normalising on `Box1 U` (the clause
`ν x (Box1 U) = 1`) forces the constant to `1`, so the two systems agree on every `V R ∩ U` and
hence, both being carried by `U`, on all of `U`.
-/

namespace Work.EKLComp

theorem leaf_unique (μ : MeasureTheory.Measure Work.EKLContract.X3) [MeasureTheory.IsProbabilityMeasure μ]
    (U : Subgroup Work.EKLContract.SL3) (hU : Work.EKLContract.IsHoro U) (t0 : Fin 3 → ℝ)
    (hmp : MeasureTheory.MeasurePreserving (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t0 • x) μ μ)
    (hcontr : ∀ u ∈ U, Filter.Tendsto (fun n : ℕ => Work.EKLContract.aDiag t0 ^ n * u * (Work.EKLContract.aDiag t0 ^ n)⁻¹) Filter.atTop (nhds 1))
    (ν : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3) (X' : Set Work.EKLContract.X3) (hL : Work.EKLContract.IsLeafwise μ U ν X') :
    ∀ (ν' : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3) (X'' : Set Work.EKLContract.X3), Work.EKLContract.IsLeafwise μ U ν' X'' → ∀ᵐ x ∂μ, ν' x = ν x :=
  Work.EKLRelCross.leafwise_unique prove_X3 μ U hU t0 hmp hcontr ν X' hL

end Work.EKLComp
