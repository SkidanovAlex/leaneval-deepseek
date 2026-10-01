import Mathlib
import Submission.Work.LinnikAreas.area6Top
import Submission.Work.LinnikAreas.RepulsionCapDefs
import Submission.Work.LinnikAreas.RepulsionCap
import Submission.Work.LinnikAreas.BGTZRepE
import Submission.Work.LinnikAreas.PairDensityCap
import Submission.Work.LinnikAreas.siegelRestLowCap
import Submission.Work.LinnikAreas.boxSumCap
import Submission.Work.LinnikAreas.logFreeFamOfCoreNodes
import Submission.Work.LinnikAreas.RestHighFree
import Submission.Work.LinnikAreas.BGTZ.RestHighBGTZGenC
import Submission.Work.LinnikAreas.RestHighCombine
import Submission.Work.LinnikAreas.siegelExpansion
import Submission.Work.LinnikAreas.siegelSimpleInput
import Submission.Work.LinnikAreas.siegelZeroWeightSummable
import Submission.Work.LinnikAreas.BGTZ.ZFRInput_exists
import Submission.Work.LinnikAreas.LogFreeAux.logFreeNP93

/-!
# AREA 6 from the LogFree chapter's two nodes plus Montgomery — **no Huxley, no Jutila**

The two inputs of the lead's unified route (`Submission/Work/ZeroDensity/JUTILA_UNIFIED_LEAD.md`)

* `Work.ZeroDensity.LogFree.logFreeNP (93/100) (12/5)` — the log-free non-principal estimate
  `Σ'_{χ≠1} N(σ,T,χ) ≤ C(qT)^{(12/5)(1-σ)}` on `σ ≥ 93/100` (Heath-Brown §11's detector with the
  `O(1)` constants of the note), and
* `Work.ZeroDensity.LogFree.HuxleyNPWide` — Huxley's non-principal `12/5` (with one logarithm)
  on `3/4 ≤ σ ≤ 93/100`,

together with **Montgomery's sharp large-sieve estimate** `Work.ZeroDensity.MontgomerySharp`,
suffice for AREA 6 — with no use of the all-character Huxley estimate (whose principal-character
half is the `ζ` density estimate on `[3/4,4/5]`) and no use of Jutila's sharp theorem on `σ ≥ 4/5`.
The assembly is `Submission/Work/LinnikAreas/logFreeFamOfCoreNodes.lean` (the family count with
exponent exactly `5/2`, the exponent AREA 6 consumes) followed by the *unchanged* AREA 6 chain
`PairDensityCap` → `RestHighFree`/`RestHighBGTZGenC` → `siegelRestLowCap`/`boxSumCap`.
-/

namespace Work.LinnikAreas

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

open Work.LinnikContract

/-- **AREA 6 from the unified LogFree nodes and Montgomery's sharp estimate.** -/
theorem area6_of_cores_v4 (hRepGen : BGTZRepulsionGenE)
    (hlog : Work.ZeroDensity.LogFree.logFreeNP (93 / 100) (12 / 5))
    (hhux : Work.ZeroDensity.LogFree.HuxleyNPWide)
    (hM : Work.ZeroDensity.MontgomerySharp (1 / 1000)) :
    Work.LinnikContract.Area6 := by
  obtain ⟨ε₀, hε₀pos, hε₀half, hrepCap⟩ := repulsionWithCap_7_16 hRepGen
  obtain ⟨cZ₀, _hcZ₀, _hzfrL₀, hrepGenC⟩ := hRepGen
  obtain ⟨cZ, hcZ, hzfr⟩ := Work.LinnikAreas.BGTZ.ZFRInput_exists
  have hcount : Work.ZeroDensity.LogFreeFamHalf (5 / 2) :=
    logFreeFamHalf_of_coreNodes hlog hhux hM
  have hfam : Work.ZeroDensity.LogFreeFamHeight (5 / 2) (3 / 2) :=
    logFreeFamHeight_of_coreNodes hlog hhux hM
  have hden : Work.LinnikAreas.Siegel.PairDensityInput :=
    pairDensityInput_of_logFree_and_capRepulsion hε₀pos hcount hrepCap
  have hLow := siegelRestLowCap (ε₀ := ε₀) (c := 7 / 16) hε₀pos hε₀half (by norm_num)
    hrepCap hden
  have hC₀pos : (0 : ℝ) < max (1000 / cZ₀) 1000 :=
    lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  have hHigh := RestHighCombine (RestHighFree hfam)
      (Work.LinnikAreas.BGTZ.RestHighBGTZGenC cZ (max (1000 / cZ₀) 1000) hcZ hC₀pos
        hrepGenC hfam hzfr)
  exact Siegel.area6_of 1 (siegelExpansion 1 le_rfl)
    (boxSumCap (ε₀ := ε₀) (c := 7 / 16) 1 le_rfl hε₀pos (by norm_num) siegelSimpleInput
      hrepCap (fun q _ χ => siegelZeroWeightSummable (q := q) (11 / 2) (3 / 10) χ) hLow hHigh)

/-- **AREA 6 with the BGTZ repulsion discharged**, from the two LogFree nodes and Montgomery's
sharp estimate (in the `∀ B > 0` form of the ZeroDensity chapter's target
`Work.ZeroDensity.Montgomery.montgomerySharp`). -/
theorem area6_of_coreNodes_allB
    (hlog : Work.ZeroDensity.LogFree.logFreeNP (93 / 100) (12 / 5))
    (hhux : Work.ZeroDensity.LogFree.HuxleyNPWide)
    (hM : ∀ B : ℝ, 0 < B → Work.ZeroDensity.MontgomerySharp B) :
    Work.LinnikContract.Area6 :=
  area6_of_cores_v4 BGTZRepulsionGenE_proved hlog hhux (hM (1 / 1000) (by norm_num))

/-- **AREA 6 from the two remaining nodes alone**: Huxley's non-principal `12/5` widened to
`σ ≤ 93/100` (`Work.ZeroDensity.LogFree.HuxleyNPWide`, whose only remaining input is
`LogFree/contourHalfWideClean`) and Montgomery's sharp large-sieve estimate in its `∀ B > 0` form
(`Work.ZeroDensity.Montgomery.montgomerySharp`, whose only remaining input is the character
approximate functional equation `Montgomery/AfeProof/afePrimitiveBalanced`).  The log-free
non-principal estimate `logFreeNP (93/100) (12/5)` is now a **theorem**
(`Work.ZeroDensity.LogFree.logFreeNP_93_100_twelveFifths`, axiom-clean). -/
theorem area6_of_twoNodes
    (hhux : Work.ZeroDensity.LogFree.HuxleyNPWide)
    (hM : ∀ B : ℝ, 0 < B → Work.ZeroDensity.MontgomerySharp B) :
    Work.LinnikContract.Area6 :=
  area6_of_coreNodes_allB Work.LinnikAreas.LogFreeAux.logFreeNP_93_100_clean hhux hM

/-- The same with Montgomery at the fixed `B = 1/1000`. -/
theorem area6_of_coreNodes
    (hlog : Work.ZeroDensity.LogFree.logFreeNP (93 / 100) (12 / 5))
    (hhux : Work.ZeroDensity.LogFree.HuxleyNPWide)
    (hM : Work.ZeroDensity.MontgomerySharp (1 / 1000)) :
    Work.LinnikContract.Area6 :=
  area6_of_cores_v4 BGTZRepulsionGenE_proved hlog hhux hM

end

end Work.LinnikAreas
