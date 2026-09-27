import Mathlib
import Submission.Work.EKLRelCross.entropy_cs_interface
import Submission.Work.EKLRelCross.plaque_ratio
import Submission.Work.EKLRelCross.leafwise_acovariant

/-!
# `Work.EKLRelCross.ae_covariance` — (U7), the `A`-covariance of a leafwise system

The statement is clause (U7) of the frozen contract `P_Leafwise` (EKL §2.1 (4), Pisa 7.16):
for an `A`-invariant probability measure `μ` on `X₃ = SL₃(ℝ)/SL₃(ℤ)`, a horospherical subgroup
`U` contracted by `α^{t₀}` and any system `ν` of leafwise measures on the conull set `X'`, there is
a conull `X'' ⊆ X'` on which the leafwise measures are equivariant for the diagonal flow:

`ν (aDiag s • x) = c • (ν x).map (g ↦ aDiag s * g * (aDiag s)⁻¹)`   (`x, aDiag s • x ∈ X''`).

The extra hypothesis `PlaqueRatio μ U ν` (the plaque-mass ratio (P1′), a consequence of the local
product structure and hence of the `condexp` field of `IsLeafwise`) is not needed for this clause;
the proof is the one developed in the workspace:

* `Work.EKLRelCross.per_t_covariance` — Pisa 7.16/7.17 for a single parameter `t` and `μ`-a.e. `x`
  (from the `condexp` field on flowers, i.e. `Work.EKLRelCross.covariant_shape`);
* `Work.EKLRelCross.covariance_bad_measurable` — the set
  `{(x,t) | ¬ CovPt ν t x}` is measurable, so Tonelli applies to it;
* `Work.EKLRelCross.leafwise_acovariant` — the Tonelli/cocycle upgrade of the per-parameter
  statement to a *single* conull `X''`, using
  `CovPt ν s y → CovPt ν h (aDiag s • y) → CovPt ν (s + h) y`.
-/

namespace Work.EKLRelCross

theorem ae_covariance (h2 : Work.EKLContract.P_X3) (μ : MeasureTheory.Measure Work.EKLContract.X3) [MeasureTheory.IsProbabilityMeasure μ]
    (U : Subgroup Work.EKLContract.SL3) (hU : Work.EKLContract.IsHoro U) (t0 : Fin 3 → ℝ)
    (ht0 : MeasureTheory.MeasurePreserving (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t0 • x) μ μ)
    (hcontr : ∀ u ∈ U, Filter.Tendsto (fun n : ℕ => Work.EKLContract.aDiag t0 ^ n * u * (Work.EKLContract.aDiag t0 ^ n)⁻¹) Filter.atTop (nhds 1))
    (ν : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3) (X' : Set Work.EKLContract.X3)
    (hL : Work.EKLContract.IsLeafwise μ U ν X')
    (hA : Work.EKLContract.IsAInvariant μ)
    (hP : Work.EKLRelCross.PlaqueRatio μ U ν) :
    Work.EKLRelCross.Covariance μ U ν X' := by
  exact Work.EKLRelCross.leafwise_acovariant h2 μ U hU t0 ht0 hcontr ν X' hL hA

end Work.EKLRelCross
