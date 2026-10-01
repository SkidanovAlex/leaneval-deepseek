import Mathlib
import Submission.Work.LinnikAreas.area6Top
import Submission.Work.LinnikAreas.RepulsionCapDefs
import Submission.Work.LinnikAreas.siegelRestLowCap
import Submission.Work.LinnikAreas.boxSumCap
import Submission.Work.LinnikAreas.BGTZ
import Submission.Work.LinnikAreas.RestHighCombine
import Submission.Work.LinnikAreas.siegelSimpleInput
import Submission.Work.LinnikAreas.siegelZeroWeightSummable
import Submission.Work.LinnikAreas.siegelExpansion

/-!
# `Work.SiegelAbsorb.area6SiegelOfInputs` — AREA 6 from the two Siegel-absorption inputs

This is the assembly of `Submission/Work/LinnikAreas/area6OfCoreNodes.lean`'s `area6_of_cores_v4`
with the two inputs *replaced* by the ones the Siegel-absorption route provides
(`Submission/Work/LinnikAreas/AREA6_ROUTE_LEAD.md`, U1–U10):

* `hden : Siegel.PairDensityInput` — the `λ₁`-saving Deuring–Heilbronn count, proved in
  `SiegelAbsorb/pairDensityInput_siegel.lean` from the **capped** repulsion and the two proved
  family counts (no `LogFreeFamHalf (5/2)`, hence no Montgomery and no Huxley);
* `hfree : RestHighFreeSpec (-3/2)` and `hbgtz : RestHighBGTZSpec (-3/2)` — the two halves of the
  far-zero bound, proved in `SiegelAbsorb/RestHighBGTZSiegel_of_window.lean` from the **crude**
  family count `LogFreeFamHeight (9/2) (3/2)` (`SiegelAbsorb/famCountCrudeCorollaries.lean`) and
  the proved BGTZ repulsion, with no input from the middle range `σ ∈ [1/2, 3/4]`.

The low part is `siegelRestLowCap` (with the capped repulsion) and the box is `boxSumCap`; both
are unchanged, and `RestHighCombine` glues the two far-zero bounds.
-/

namespace Work.SiegelAbsorb

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

open Work.LinnikContract

/-- **AREA 6 from the capped repulsion and the two Siegel-absorption inputs.** -/
theorem area6_siegel_of_inputs {ε₀ : ℝ} (hε₀ : 0 < ε₀) (hε₀1 : ε₀ ≤ 1 / 2)
    (hrep : Work.LinnikAreas.RepulsionWithCap ε₀ (7 / 16))
    (hden : Work.LinnikAreas.Siegel.PairDensityInput)
    (hfree : Work.LinnikAreas.Siegel.RestHighFreeSpec (-3 / 2))
    (hbgtz : Work.LinnikAreas.Siegel.RestHighBGTZSpec (-3 / 2)) :
    Work.LinnikContract.Area6 := by
  have hLow := Work.LinnikAreas.siegelRestLowCap (ε₀ := ε₀) (c := 7 / 16) hε₀ hε₀1
    (by norm_num) hrep hden
  have hHigh := Work.LinnikAreas.RestHighCombine hfree hbgtz
  exact Work.LinnikAreas.Siegel.area6_of 1 (Work.LinnikAreas.siegelExpansion 1 le_rfl)
    (Work.LinnikAreas.boxSumCap (ε₀ := ε₀) (c := 7 / 16) 1 le_rfl hε₀ (by norm_num)
      Work.LinnikAreas.siegelSimpleInput hrep
      (fun q _ χ => Work.LinnikAreas.siegelZeroWeightSummable (q := q) (11 / 2) (3 / 10) χ)
      hLow hHigh)

end

end Work.SiegelAbsorb
