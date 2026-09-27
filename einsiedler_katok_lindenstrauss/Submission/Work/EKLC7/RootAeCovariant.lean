import Mathlib
import Submission.Work.EKLContract.Interfaces
import Submission.Work.EKLComp.prove_X3
import Submission.Work.EKLContract.Lemmas.isHoro_Uij
import Submission.Work.EKLC7.Defs
import Submission.Work.EKLRelCross.leafwise_acovariant

namespace Work.EKLC7

open MeasureTheory Filter Topology
open scoped ENNReal
open Work.EKLContract

set_option maxHeartbeats 800000

/-- **(U7) of the frozen EKL contract, at the root group `U_ij`.**  The `A`-covariance of a
leafwise system for `U_ij` on a single conull set (EKL (4) = Pisa 7.16/7.17): this is
`Work.EKLRelCross.leafwise_acovariant` at `U = Uij hij`, whose horosphericality is
`Work.EKLContract.Lemmas.isHoro_Uij`. -/
theorem RootAeCovariant (h2 : Work.EKLContract.P_X3)
    {μ : MeasureTheory.Measure Work.EKLContract.X3} [MeasureTheory.IsProbabilityMeasure μ]
    {i j : Fin 3} (hij : i ≠ j) (t0 : Fin 3 → ℝ)
    (hmp : MeasureTheory.MeasurePreserving (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t0 • x) μ μ)
    (hcontr : ∀ u ∈ Work.EKLContract.Uij hij, Filter.Tendsto (fun n : ℕ => Work.EKLContract.aDiag t0 ^ n * u * (Work.EKLContract.aDiag t0 ^ n)⁻¹) Filter.atTop (nhds 1))
    {ν : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3} {X' : Set Work.EKLContract.X3}
    (hL : Work.EKLContract.IsLeafwise μ (Work.EKLContract.Uij hij) ν X')
    (hA : Work.EKLContract.IsAInvariant μ) :
    ∃ X'' ⊆ X', MeasurableSet X'' ∧ μ X''ᶜ = 0 ∧
      ∀ (t : Fin 3 → ℝ) (x : Work.EKLContract.X3), x ∈ X'' → Work.EKLContract.aDiag t • x ∈ X'' →
        ∃ c : ENNReal, c ≠ 0 ∧ c ≠ ⊤ ∧
          ν (Work.EKLContract.aDiag t • x) = c • (ν x).map (fun g => Work.EKLContract.aDiag t * g * (Work.EKLContract.aDiag t)⁻¹) :=
  Work.EKLRelCross.leafwise_acovariant h2 μ (Work.EKLContract.Uij hij)
    (Work.EKLContract.Lemmas.isHoro_Uij hij) t0 hmp hcontr ν X' hL hA

end Work.EKLC7
