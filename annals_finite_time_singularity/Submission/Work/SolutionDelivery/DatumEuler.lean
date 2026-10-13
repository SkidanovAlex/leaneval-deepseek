/-
# `Work.SolutionDelivery.DatumEuler` — the datum clauses of `AssemblyInputs`

The four datum clauses of `Work.StabilityFar.AssemblyInputs` — `div u₀ = 0`, `IsOdd u₀`,
`IsContDiffHolder ℝ α u₀`, and the `α`-power decay of `∇×u₀` — for the constructed datum
`u₀ = BS ω₀`, where `ω₀ = χ(ρ/L)·ωS` is the compactly supported cut-off of the paper's
self-similar initial vorticity.

This is the `Work.LWP.assembly_data` route, with the elementary properties of the cut-off furnished
by `Work.SolutionDelivery.DatumCut` and the decay clause automatic for a compactly supported
vorticity (`Work.SolutionDelivery.vorticityDecay_of_support_bdd`).
-/
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.SolutionDelivery.Datum
import Submission.Work.SolutionDelivery.DatumCut.datumData_of_cut

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open FiniteTimeSingularity Set Gradient Matrix Filter Topology MeasureTheory
open scoped Topology Matrix NNReal ENNReal

namespace Work.SolutionDelivery

namespace ConstructedSolution

variable {α : NNReal} (C : ConstructedSolution α)

/-- **The datum of the constructed solution is Lichtenstein–Gunther admissible.** -/
theorem datum_eulerData (hα : 0 < (α : ℝ)) (hα1 : (α : ℝ) ≤ 1) :
    Work.LWP.EulerData α (Work.LWP.biotSavart C.ω₀) :=
  (DatumCut.datumData_of_cut C.lwp C.hL C.hM hα hα1 C.ωS_meas C.ωS_bdd C.ωS_cdh C.ωS_div
    C.ωS_odd).1

/-- The same datum is Biot–Savart compatible (`Work.LWP.EulerDataBS`). -/
theorem datum_eulerDataBS (hα : 0 < (α : ℝ)) (hα1 : (α : ℝ) ≤ 1) :
    Work.LWP.EulerDataBS α (Work.LWP.biotSavart C.ω₀) :=
  (DatumCut.datumData_of_cut C.lwp C.hL C.hM hα hα1 C.ωS_meas C.ωS_bdd C.ωS_cdh C.ωS_div
    C.ωS_odd).2

/-- The four datum clauses, individually, in the exact shape of the `AssemblyInputs` fields. -/
theorem datum_div (hα : 0 < (α : ℝ)) (hα1 : (α : ℝ) ≤ 1) :
    div (Work.LWP.biotSavart C.ω₀) = 0 :=
  (C.datum_eulerData hα hα1).div_free

theorem datum_odd (hα : 0 < (α : ℝ)) (hα1 : (α : ℝ) ≤ 1) :
    IsOdd (Work.LWP.biotSavart C.ω₀) :=
  (C.datum_eulerData hα hα1).odd

theorem datum_contDiffHolder (hα : 0 < (α : ℝ)) (hα1 : (α : ℝ) ≤ 1) :
    IsContDiffHolder ℝ α (Work.LWP.biotSavart C.ω₀) :=
  (C.datum_eulerData hα hα1).contDiffHolder

theorem datum_vorticityDecay (hα : 0 < (α : ℝ)) (hα1 : (α : ℝ) ≤ 1) :
    Work.LWP.VorticityDecay α (vorticity (Work.LWP.biotSavart C.ω₀)) :=
  (C.datum_eulerData hα hα1).vort_decay

end ConstructedSolution

/-- **The maximal solution of the cut-off datum exists** — the `hmax` field of
`ConstructedSolution` is *not* an extra assumption: it is the LWP chapter's own
`MaximalSolutionExists` input applied to `BS ω₀`, for which `Work.SolutionDelivery.DatumCut`
supplies the `EulerData`/`EulerDataBS` hypotheses. -/
theorem exists_maximal_of_datum {α : NNReal} (hlwp : Work.LWP.LWPInputs α) {L M : ℝ}
    (hL : 0 < L) (hM : 0 ≤ M) {ωS : R3 → R3}
    (hmeas : MeasureTheory.AEStronglyMeasurable ωS MeasureTheory.volume)
    (hbdd : ∀ x : R3, ‖ωS x‖ ≤ M) (hcdh : IsContDiffHolder ℝ α ωS)
    (hα : 0 < (α : ℝ)) (hα1 : (α : ℝ) ≤ 1)
    (hdiv : ∀ x : R3, div (cutDatum L ωS) x = 0)
    (hodd : IsOdd (Work.LWP.biotSavart (cutDatum L ωS))) :
    ∃ T : ℝ, 0 < T ∧
      Nonempty (Work.LWP.MaximalSolution α (Work.LWP.biotSavart (cutDatum L ωS)) T) :=
  let h := DatumCut.datumData_of_cut hlwp hL hM hα hα1 hmeas hbdd hcdh hdiv hodd
  hlwp.maxExists _ h.1 h.2

end Work.SolutionDelivery
