import Mathlib
import Submission.Work.EKLComp.LeafExistence
import Submission.Work.EKLComp.prove_X3
import Submission.Work.EKLRelCross.leafwise_acovariant

namespace Work.EKLComp

/-- **(U7)** The `A`-covariance of a leafwise-measure system (EKL §2.1 (4), Pisa 7.16/7.17):
on a conull set `X'' ⊆ X'`, the leafwise measure at `aDiag t • x` is proportional to the
conjugate (under `aDiag t`) of the leafwise measure at `x`.

This is the frozen clause (U7) of `P_Leafwise`.  The argument is classical: for each fixed `t`
the covariance holds for `μ`-a.e. `x` (Pisa 7.17 on the shapes of a flower family, with the
`condexp` field of `IsLeafwise`), and a Fubini/measurability upgrade over the parameter `t`
produces a single conull set on which it holds simultaneously for all `t`.  That development is
`Work.EKLRelCross.leafwise_acovariant`, which takes the `X₃`-background component `P_X3` as a
hypothesis; here we supply it from `Work.EKLComp.prove_X3`. -/
theorem leaf_acovariant (μ : MeasureTheory.Measure Work.EKLContract.X3) [MeasureTheory.IsProbabilityMeasure μ]
    (U : Subgroup Work.EKLContract.SL3) (hU : Work.EKLContract.IsHoro U) (t0 : Fin 3 → ℝ)
    (hmp : MeasureTheory.MeasurePreserving (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t0 • x) μ μ)
    (hcontr : ∀ u ∈ U, Filter.Tendsto (fun n : ℕ => Work.EKLContract.aDiag t0 ^ n * u * (Work.EKLContract.aDiag t0 ^ n)⁻¹) Filter.atTop (nhds 1))
    (ν : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3) (X' : Set Work.EKLContract.X3) (hL : Work.EKLContract.IsLeafwise μ U ν X') :
    Work.EKLContract.IsAInvariant μ → ∃ X'' ⊆ X', MeasurableSet X'' ∧ μ X''ᶜ = 0 ∧
        ∀ (t : Fin 3 → ℝ) (x : Work.EKLContract.X3), x ∈ X'' → Work.EKLContract.aDiag t • x ∈ X'' →
          ∃ c : ENNReal, c ≠ 0 ∧ c ≠ ⊤ ∧
            ν (Work.EKLContract.aDiag t • x) = c • (ν x).map (fun g => Work.EKLContract.aDiag t * g * (Work.EKLContract.aDiag t)⁻¹) := by
  intro hA
  exact Work.EKLRelCross.leafwise_acovariant (h2 := Work.EKLComp.prove_X3) (μ := μ)
    (U := U) (hU := hU) (t0 := t0) (ht0 := hmp) (hcontr := hcontr) (ν := ν) (X' := X') (hL := hL) hA

end Work.EKLComp
