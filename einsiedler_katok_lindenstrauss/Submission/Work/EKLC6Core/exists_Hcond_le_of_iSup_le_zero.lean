import Mathlib
import Submission.Work.EKLC6Core.BiGenAux
import Submission.Work.EKLGen.tendsto_Hcond_iSup_univ

namespace Work.EKLC6Core

open MeasureTheory Filter

/-- Upward convergence of `Hcond` along a monotone sequence of sub-σ-algebras, in the
universe-polymorphic form of `Work.EKLGen.tendsto_Hcond_iSup_univ` (restated here only to fix
the ambient σ-algebra instance argument explicitly). -/
theorem tendsto_Hcond_iSup_aux {X : Type*} [mX : MeasurableSpace X] (μ : MeasureTheory.Measure X)
    [MeasureTheory.IsProbabilityMeasure μ] (Q : @Work.EKLContract.FinPart X mX)
    (Aseq : ℕ → MeasurableSpace X) (hmono : Monotone Aseq) (hle : ∀ n, Aseq n ≤ mX) :
    Filter.Tendsto (fun n => @Work.EKLContract.Hcond X mX μ Q (Aseq n)) Filter.atTop
      (nhds (@Work.EKLContract.Hcond X mX μ Q (⨆ n, Aseq n))) :=
  Work.EKLGen.tendsto_Hcond_iSup_univ (mX := mX) μ Q Aseq hmono hle

/-- If the conditional entropy of a finite partition `Q` with respect to the σ-algebra generated
by an increasing sequence `Aseq` of sub-σ-algebras of `mX` is `≤ 0`, then for every `ε > 0` some
member `Aseq N` of the sequence already has conditional entropy `≤ ε`.

Proof: by Lévy's upward theorem the numbers `Hcond μ Q (Aseq n)` converge to
`Hcond μ Q (⨆ n, Aseq n) ≤ 0 < ε`; take `N` beyond the point where they are within `ε` of the
limit. -/
theorem exists_Hcond_le_of_iSup_le_zero {X : Type*} [mX : MeasurableSpace X]
    (μ : MeasureTheory.Measure X) [MeasureTheory.IsProbabilityMeasure μ]
    (Q : @Work.EKLContract.FinPart X mX) (Aseq : ℕ → MeasurableSpace X)
    (hmono : Monotone Aseq) (hle : ∀ n, Aseq n ≤ mX)
    (h0 : @Work.EKLContract.Hcond X mX μ Q (⨆ n, Aseq n) ≤ 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, @Work.EKLContract.Hcond X mX μ Q (Aseq N) ≤ ε := by
  have htend := tendsto_Hcond_iSup_aux (mX := mX) μ Q Aseq hmono hle
  rcases (Metric.tendsto_atTop.mp htend) ε hε with ⟨N, hN⟩
  refine ⟨N, le_of_lt ?_⟩
  have hlt := (abs_lt.mp (hN N le_rfl)).2
  linarith

end Work.EKLC6Core
