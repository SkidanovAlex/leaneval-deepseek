import Mathlib
import Submission.Work.EKLComp.prove_X3
import Submission.Work.EKLRelCross.leafwise_propor

namespace Work.EKLComp

/-- **Clause (U5) of the frozen EKL contract (EKL (8))**: a leafwise measure which is
proportional to one of its right `U`-translates is equal to it.  This is the general form of
`Work.EKLRelCross.leafwise_propor`, which carries an extra `P_X3` hypothesis (here supplied by
`Work.EKLComp.prove_X3`). -/
theorem leaf_propor (μ : MeasureTheory.Measure Work.EKLContract.X3) [MeasureTheory.IsProbabilityMeasure μ]
    (U : Subgroup Work.EKLContract.SL3) (hU : Work.EKLContract.IsHoro U) (t0 : Fin 3 → ℝ)
    (hmp : MeasureTheory.MeasurePreserving (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t0 • x) μ μ)
    (hcontr : ∀ u ∈ U, Filter.Tendsto (fun n : ℕ => Work.EKLContract.aDiag t0 ^ n * u * (Work.EKLContract.aDiag t0 ^ n)⁻¹) Filter.atTop (nhds 1))
    (ν : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3) (X' : Set Work.EKLContract.X3) (hL : Work.EKLContract.IsLeafwise μ U ν X') :
    ∀ᵐ x ∂μ, ∀ u ∈ U, ∀ c : ENNReal,
        (ν x).map (fun g => g * u) = c • ν x → (ν x).map (fun g => g * u) = ν x :=
  Work.EKLRelCross.leafwise_propor prove_X3 μ U hU t0 hmp hcontr ν X' hL

end Work.EKLComp
