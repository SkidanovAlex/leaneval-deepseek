import Mathlib
import Submission.Work.Diff.STE.B3.Comp
import Submission.Work.Diff.STE.B3.Data
import Submission.Work.Diff.STE.D.Setup
import Submission.Work.Diff.STE.D.ChartData_Rstar
import Submission.Work.Diff.STE.D.ChartData_genMap

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.Lead

set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 1000000

/-- **A finite sum of reconstructions has smooth chart data.**  The section
`p ↦ Σ i, D.Rstar i (G i) p` is a finite sum of the individual reconstructions
`D.Rstar i (fun a b z => G i z a b)`, each of which has smooth chart data by
`Work.Diff.STE.D.ChartData_Rstar` (the smoothness of `G i · a b` is exactly `hsm`), and
`ChartData` is preserved by finite sums (`Work.Diff.STE.D.GenMap.chartData_finset_sum`).  The
periodicity hypothesis `hper` is not needed for this statement (it is part of the intended use of
`Rstar`, where the coefficient families come from Fourier series). -/
theorem chartData_sum_Rstar
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (G : ι₀ → (Fin (Module.finrank ℝ E) → ℝ) → Fin (Module.finrank ℝ E) →
      Fin (Module.finrank ℝ E) → ℝ)
    (hsm : ∀ i a b, ContDiff ℝ (⊤ : ℕ∞) (fun z => G i z a b))
    (hper : ∀ i a b, Work.Diff.STE.Periodic1 (fun z => G i z a b)) :
    Work.Diff.STE.D.ChartData (I := I) (M := M)
      (fun p => ∑ i : ι₀, D.Rstar i (fun a b z => G i z a b) p) := by
  classical
  -- `Bil I M` is a Pi type, so a pointwise sum is the sum of the sections; rewrite the function
  -- `p ↦ Σ i, Rstar i (G i) p` into the section `Σ i, Rstar i (G i)`.
  have hsum : (fun p : M => ∑ i : ι₀, D.Rstar i (fun a b z => G i z a b) p)
      = (∑ i : ι₀, D.Rstar i (fun a b z => G i z a b)) := by
    funext p
    exact (Finset.sum_apply p (Finset.univ : Finset ι₀)
      (fun i => D.Rstar i (fun a b z => G i z a b))).symm
  rw [hsum]
  -- Each summand has smooth chart data, and `ChartData` is closed under finite sums.
  refine Work.Diff.STE.D.GenMap.chartData_finset_sum (I := I) (M := M) Finset.univ
    (fun i => D.Rstar i (fun a b z => G i z a b)) ?_
  intro i _
  exact Work.Diff.STE.D.ChartData_Rstar (I := I) (M := M) D i _
    (fun a b => hsm i a b)

end Work.Diff.STE.Lead
