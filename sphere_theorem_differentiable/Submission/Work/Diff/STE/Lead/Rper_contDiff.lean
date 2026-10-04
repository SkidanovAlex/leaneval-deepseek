import Mathlib
import Submission.Work.Diff.STE.B3.R_contDiff_of_chartData
import Submission.Work.Diff.STE.periodization_contDiff_periodic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Smoothness and periodicity of the periodised localised components

For Layer B3 data `D` (`B3Data ι₀ g₀`) and a section `h : Bil` whose chart matrix is smooth
(`Work.Diff.STE.D.ChartData h`), the periodised localised component `D.Rper i h a b` is `C^∞` and
`1`-periodic in every coordinate.

Route: `D.Rper i h a b` is the periodisation of the complexified component
`z ↦ ((D.R i h a b z : ℝ) : ℂ)`; the latter is smooth by
`Work.Diff.STE.B3.R_contDiff_of_chartData` (composed with `Complex.ofRealCLM`) and supported in the
open unit cube (its support is contained in that of `D.psi i`), so
`Work.Diff.STE.periodization_contDiff_periodic` applies.

This is the regularity input for both the `L²` bound `ENormSq 0 (D.Rper i h a b) ≤ C K²` of a
pointwise bounded section and for the single-coefficient bound
`‖fourierCoeff (D.Rper i h a b) μ‖ ≤ C √(D.BNorm 0 h)`.
-/

namespace Work.Diff.STE.Lead

open MeasureTheory BigOperators
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set Work.Diff.STE

set_option maxHeartbeats 800000

/-- **The periodised localised components of a section with smooth chart data are smooth and
`1`-periodic.** -/
lemma Rper_contDiff_and_periodic
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (h : Work.Diff.STE.Bil (I := I) (M := M))
    (hh : Work.Diff.STE.D.ChartData (I := I) (M := M) h) :
    ∀ i a b, ContDiff ℝ (⊤ : ℕ∞) (D.Rper i h a b)
      ∧ Work.Diff.STE.Periodic1 (D.Rper i h a b) := by
  intro i a b
  have hR : ContDiff ℝ (⊤ : ℕ∞) (D.R i h a b) :=
    Work.Diff.STE.B3.R_contDiff_of_chartData (I := I) (M := M) D h hh i a b
  have hsupp : Function.support (fun z => ((D.R i h a b z : ℝ) : ℂ)) ⊆
      Set.pi Set.univ (fun _ : Fin (Module.finrank ℝ E) => Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)) := by
    intro z hz
    refine D.psi_supp i ?_
    rw [Function.mem_support] at hz
    intro h0
    exact hz (by simp only [Work.Diff.STE.B3Data.R, h0, zero_mul, Complex.ofReal_zero])
  have hf : ContDiff ℝ (⊤ : ℕ∞) (fun z => ((D.R i h a b z : ℝ) : ℂ)) :=
    (Complex.ofRealCLM.contDiff (n := ((⊤ : ℕ∞) : WithTop ℕ∞))).comp hR
  have hmain := Work.Diff.STE.periodization_contDiff_periodic
    (fun z => ((D.R i h a b z : ℝ) : ℂ)) hf hsupp
  exact ⟨hmain.1, hmain.2.1⟩

end Work.Diff.STE.Lead
