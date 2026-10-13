import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.TanTheta.Basic
import Submission.Work.FTS.EllipticEst.TanTheta.integrable_mul_of_sq_weight_of_aemeasurable

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.TanTheta

/-- Cauchy–Schwarz in `L²` for the weight `sin(2θ)^{-η}` on `(0, π/2)`, **with the
a.e.-measurability hypotheses that the statement needs**: if `f`, `g` are a.e. measurable on
`(0, π/2)` and `f² sin(2θ)^{-η}`, `g² sin(2θ)^{-η}` are integrable then so is
`f g sin(2θ)^{-η}`.

The two `AEMeasurable` hypotheses are not redundant: without them the statement is FALSE (see
the module docstring below), and the version *with* them is the theorem
`Work.FTS.EllipticEst.TanTheta.integrable_mul_of_sq_weight_of_aemeasurable`, which this
declaration simply re-exports under its historical name — so the call sites of the earlier
(a.e.-measurability-free, hence refutable) form keep working once they supply the two
measurability facts, which in every application come from `ContinuousOn.aemeasurable` for the
slices.

Route: write `f θ g θ sin(2θ)^{-η} = (f θ · sin(2θ)^{-η/2}) · (g θ · sin(2θ)^{-η/2})` on the
open interval (where `sin (2θ) > 0`, so `Real.rpow_add` applies), and use
`MeasureTheory.MemLp.mul` with the Hölder triple `2, 2, 1`. -/
theorem integrable_mul_of_sq_weight (η : ℝ) {f g : ℝ → ℝ}
    (hf_meas : AEMeasurable f
      (MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2))))
    (hg_meas : AEMeasurable g
      (MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2))))
    (hf : MeasureTheory.IntegrableOn
      (fun θ => (f θ) ^ 2 * (Real.sin (2 * θ)) ^ (-η)) (Set.Ioo 0 (Real.pi / 2)))
    (hg : MeasureTheory.IntegrableOn
      (fun θ => (g θ) ^ 2 * (Real.sin (2 * θ)) ^ (-η)) (Set.Ioo 0 (Real.pi / 2))) :
    MeasureTheory.IntegrableOn
      (fun θ => f θ * g θ * (Real.sin (2 * θ)) ^ (-η)) (Set.Ioo 0 (Real.pi / 2)) :=
  integrable_mul_of_sq_weight_of_aemeasurable η hf_meas hg_meas hf hg

/-! ### This statement is FALSE as written: it is missing a measurability hypothesis

`MeasureTheory.Integrable f μ` unfolds to `AEStronglyMeasurable f μ ∧ HasFiniteIntegral f μ`
(see `Mathlib.MeasureTheory.Function.L1Space.Integrable`) and `IntegrableOn f s μ` is, by
definition, `Integrable f (μ.restrict s)`.  Hence the *conclusion* above demands that
`fun θ => f θ * g θ * sin (2*θ) ^ (-η)` be a.e. strongly measurable, and that does **not**
follow from the two hypotheses:

* take `η = 0`, `g = fun _ => 1` and `f = 1_A - 1_{Aᶜ}` where `A ⊆ (0, π/2)` is not Lebesgue
  measurable (such an `A` exists in Lean's ambient classical logic — a Vitali set; note that
  `MeasureTheory.MeasureSpace ℝ` is the *Borel* σ-algebra, `borel ℝ`, which is not complete).
  Then `f ^ 2 = 1`, so both hypotheses hold (`(0, π/2)` has finite measure), while the
  conclusion would say that `f` is integrable, i.e. a.e. equal to a measurable function; that
  is false, since then `A = {θ ∈ (0, π/2) | f θ = 1}` would differ from a Borel set by a null
  set, hence would be Lebesgue measurable.
* Equivalently: the hypothesis `Integrable (fun θ => f θ ^ 2 * w θ)` only makes `f ^ 2 * w`
  (hence `f ^ 2`) a.e. measurable.  A.e. measurability of a *square* does not imply a.e.
  measurability of the function: the sign is unrecoverable (`(±1) ^ 2 = 1`), and Lean's `ℝ`
  carries the Borel σ-algebra, where non-measurable sign functions exist.  (Note that
  `Integrable.aestronglyMeasurable` applied to the hypothesis only yields measurability of
  `f ^ 2 * sin(2θ) ^ (-η)`, never of `f` itself.)

In the intended application `f` and `g` are slices of smooth (in particular measurable)
functions, so adding a.e. measurability of `f` and `g` is harmless.

**Repair applied here.**  `integrable_mul_of_sq_weight` above now carries the two extra
hypotheses `AEMeasurable f (volume.restrict (Ioo 0 (π/2)))` and
`AEMeasurable g (volume.restrict (Ioo 0 (π/2)))` (which hold whenever `f`, `g` are continuous
on the interval, by `ContinuousOn.aemeasurable`) and is proved by re-exporting the sorry-free
`Work.FTS.EllipticEst.TanTheta.integrable_mul_of_sq_weight_of_aemeasurable` of the sibling
module `Submission.Work.FTS.EllipticEst.TanTheta.integrable_mul_of_sq_weight_of_aemeasurable`.
The name is kept so that existing imports continue to build; a caller of the old
(measurability-free) form must now supply the two measurability facts, which is the *only*
change. -/

end Work.FTS.EllipticEst.TanTheta
