import Submission.Work.RHContract.Interfaces
import Submission.Work.RHContract.B.lcm_transfer
import Submission.Work.RHContract.B.transferInput_of_lcmTransfer
import Submission.Work.RHContract.B.sigmaOscillation_not_robin_upper
import Submission.Work.RHContract.Nonvacuity.psiTail_not_oscillation_of_RH
import Submission.Work.RHContract.B.landau_input
import Submission.Work.RHContract.A.RegionIIIFromMargin

/-!
# `Work.RHContract.Areas` — assembly of the three areas

This module contains the glue that turns the sub-lemmas of the area into the three area
statements of `Work.RHContract.Defs`:

* **AREA B2 (`TransferInput`) is DONE**: it follows from the proved
  `Work.RHContract.B.lcm_transfer` (Lemma T) through
  `Work.RHContract.B.transferInput_of_lcmTransfer`.
* **AREA A (`RobinCAFrom1530`)** is assembled from the three regions by
  `robinCAFrom1530_of_regions`; the region lemmas themselves are
  `Work.RHContract.A.robin_ca_regionI` / `II` / `III`.
* **AREA B1 (`LandauInput`)** is `Work.RHContract.B.landau_input`.
-/

open scoped ArithmeticFunction.sigma

namespace Work.RHContract

noncomputable section

/-- **AREA B2, proved.**  The elementary transfer at `n = lcm(1..⌊x⌋)`
(`Work.RHContract.B.lcm_transfer`, Lemma T of ROUTE_LEAD §3.1) yields
`TransferInput = (PsiTailOscillation → SigmaOscillation)`. -/
theorem transferInput_proved : TransferInput :=
  Work.RHContract.B.transferInput_of_lcmTransfer
    (fun x hx => Work.RHContract.B.lcm_transfer x hx)

/-- **AREA A from the three regions.**  A case split of `ξ(ε) ≥ 1530` on
`ξ < 3·10^4` (Region I), `3·10^4 ≤ ξ < 10^8` (Region II) and `10^8 ≤ ξ` (Region III).
Regions II and III are stated under `RiemannHypothesis`, Region I is unconditional. -/
theorem robinCAFrom1530_of_regions
    (hI : ∀ ε : ℝ, 0 < ε → (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ) →
      (Work.RHPlan.caXi ε : ℝ) < 30000 → Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε))
    (hII : RiemannHypothesis → ∀ ε : ℝ, 0 < ε → 30000 ≤ (Work.RHPlan.caXi ε : ℝ) →
      (Work.RHPlan.caXi ε : ℝ) < (10 : ℝ) ^ 8 → Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε))
    (hIII : RiemannHypothesis → ∀ ε : ℝ, 0 < ε → (10 : ℝ) ^ 8 ≤ (Work.RHPlan.caXi ε : ℝ) →
      Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε)) :
    RobinCAFrom1530 := by
  intro hRH ε hε hξ
  by_cases h1 : (Work.RHPlan.caXi ε : ℝ) < 30000
  · exact hI ε hε hξ h1
  · have h1' : 30000 ≤ (Work.RHPlan.caXi ε : ℝ) := le_of_not_gt h1
    by_cases h2 : (Work.RHPlan.caXi ε : ℝ) < (10 : ℝ) ^ 8
    · exact hII hRH ε hε h1' h2
    · exact hIII hRH ε hε (le_of_not_gt h2)

/-- **AREA B1, proved.**  `Work.RHContract.B.landau_input` (B7, ROUTE_LEAD §3.3). -/
theorem landauInput_proved : LandauInput := Work.RHContract.B.landau_input

/-- **The replacement contract with AREAS B1 and B2 discharged.**  A caller who supplies
AREA A gets the challenge theorem: `hA : RobinCAFrom1530`. -/
theorem rh_iff_of_areas_of_A (hA : RobinCAFrom1530) :
    RiemannHypothesis ↔ LeanEval.NumberTheory.LagariasElementaryCriterion :=
  rh_iff_of_areas' hA landauInput_proved transferInput_proved

/-- Backwards-compatible name for the version taking both B-areas explicitly. -/
theorem rh_iff_of_areas_of_B1 (hA : RobinCAFrom1530) (hL : LandauInput) :
    RiemannHypothesis ↔ LeanEval.NumberTheory.LagariasElementaryCriterion :=
  rh_iff_of_areas' hA hL transferInput_proved

/-- **The B1 conclusion is exactly the failure of RH.**  Given AREA A (`RobinCAFrom1530`) and
AREA B1 (`LandauInput`), the oscillation of `J` is *equivalent* to `¬ RiemannHypothesis`:
the forward direction is AREA A + the proved transfer (`transferInput_proved`, Lemma T + AREA
B2) + `B.sigmaOscillation_not_robin_upper` (unconditional), the backward direction is AREA B1.

In particular `PsiTailOscillation` is neither provable nor refutable in this workspace: RH
refutes it (`Nonvacuity.psiTail_not_oscillation_of_RH`) and `¬RH` implies it (AREA B1). -/
theorem psiTailOscillation_iff_not_RH (hA : RobinCAFrom1530) :
    PsiTailOscillation ↔ ¬ RiemannHypothesis := by
  constructor
  · intro hosc hRH
    exact Work.RHContract.B.sigmaOscillation_not_robin_upper (transferInput_proved hosc)
      (robin_upper_of_areaA hA hRH)
  · intro hnotRH
    exact landauInput_proved hnotRH

/-- The same statement in the "there is no oscillation under RH" form of
`Nonvacuity.psiTail_not_oscillation_of_RH`. -/
theorem psiTailOscillation_not_of_RH (h : RiemannHypothesis) : ¬ PsiTailOscillation :=
  Work.RHContract.Nonvacuity.psiTail_not_oscillation_of_RH h

end

end Work.RHContract
