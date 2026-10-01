import Mathlib
import Submission.Work.LinnikAreas.area6Top
import Submission.Work.LinnikAreas.RepulsionCapDefs
import Submission.Work.LinnikAreas.RepulsionCap
import Submission.Work.LinnikAreas.BGTZRepE
import Submission.Work.LinnikAreas.PairDensityCap
import Submission.Work.LinnikAreas.siegelRestLowCap
import Submission.Work.LinnikAreas.boxSumCap
import Submission.Work.LinnikAreas.logFreeFamOfTwelveFifths
import Submission.Work.LinnikAreas.RestHighFree
import Submission.Work.LinnikAreas.BGTZ.RestHighBGTZGenC
import Submission.Work.LinnikAreas.RestHighCombine
import Submission.Work.LinnikAreas.siegelExpansion
import Submission.Work.LinnikAreas.siegelSimpleInput
import Submission.Work.LinnikAreas.siegelZeroWeightSummable
import Submission.Work.LinnikAreas.BGTZ.ZFRInput_exists
import Submission.Work.ZeroDensity.LogFree.nonPrincipalTwelveFifths

/-!
# AREA 6 from the unified non-principal input `NonPrincipalTwelveFifths` and Huxley's `12/5`

This is the AREA 6 assembly of `Submission/Work/LinnikAreas/area6CapChain.lean` with the
Jutila input `Work.LinnikAreas.FamilyZeroDensityJutilaNP` (coefficient `2` on `σ ≥ 4/5`)
replaced by the lead's unified non-principal input

`Work.ZeroDensity.LogFree.NonPrincipalTwelveFifths`
(`Σ' N(σ,T,χ) ≤ C(qT)^{(12/5+ε)(1-σ)}` on `σ ≥ 3979/5000`),

which is the node `Work.ZeroDensity.LogFree.logFreeNP (93/100) (12/5)` glued with Huxley's
non-principal bound widened to `σ ≤ 93/100` (`JUTILA_UNIFIED_LEAD.md` §2.1: *Area 6 needs ... a
non-principal log-free bound with q-coefficient ≤ 5/2 on σ ≥ 4/5*; `12/5 + 1/10 = 5/2` is
exactly the requirement, and `3979/5000 = 0.7958 < 4/5`, so the range is covered).

Since the exponent `5/2` is unchanged, **every downstream lemma of the AREA 6 chain is reused
verbatim**: `deuringHeilbronnLogFreeCap`/`pairDensityInput_of_logFree_and_capRepulsion`
(`PairDensityCap.lean`), `RestHighFree`, `RestHighBGTZGenC` and the capped consumers
`siegelRestLowCap`, `boxSumCap`.  The only inputs are the two Propositions
`NonPrincipalTwelveFifths` and `Work.ZeroDensity.FamDensityEpsRange 0 (4/5) (12/5)` (Huxley,
all characters) together with the proved BGTZ repulsion `BGTZRepulsionGenE`; no clause of the
frozen AREA 3 certificate is used.
-/

namespace Work.LinnikAreas

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

open Work.LinnikContract

/-- **AREA 6 from the unified non-principal input and Huxley's `12/5`.**  The hypothesis `hNP` is
verbatim `Work.ZeroDensity.LogFree.NonPrincipalTwelveFifths`. -/
theorem area6_of_cores_v3 (hRepGen : BGTZRepulsionGenE)
    (hNP : Work.ZeroDensity.LogFree.NonPrincipalTwelveFifths)
    (hH : Work.ZeroDensity.FamDensityEpsRange 0 (4 / 5) (12 / 5)) :
    Work.LinnikContract.Area6 := by
  obtain ⟨ε₀, hε₀pos, hε₀half, hrepCap⟩ := repulsionWithCap_7_16 hRepGen
  obtain ⟨cZ₀, _hcZ₀, _hzfrL₀, hrepGenC⟩ := hRepGen
  obtain ⟨cZ, hcZ, hzfr⟩ := Work.LinnikAreas.BGTZ.ZFRInput_exists
  have hcount : Work.ZeroDensity.LogFreeFamHalf (5 / 2) :=
    logFreeFamHalf_of_nonPrincipalTwelveFifths hNP hH
  have hfam : Work.ZeroDensity.LogFreeFamHeight (5 / 2) (3 / 2) :=
    logFreeFamHeight_of_nonPrincipalTwelveFifths hNP hH
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

/-- **AREA 6 with the BGTZ repulsion discharged**: from the unified non-principal input and
Huxley's `12/5` alone. -/
theorem area6_of_nonPrincipalTwelveFifths
    (hNP : Work.ZeroDensity.LogFree.NonPrincipalTwelveFifths)
    (hH : Work.ZeroDensity.FamDensityEpsRange 0 (4 / 5) (12 / 5)) :
    Work.LinnikContract.Area6 :=
  area6_of_cores_v3 BGTZRepulsionGenE_proved hNP hH

/-- **AREA 6 from the two *pieces* of `NonPrincipalTwelveFifths` and Huxley's `12/5`**: the
log-free non-principal estimate at `σ₀ = 93/100` (`logFreeNP (93/100) (12/5)`), Huxley's
non-principal `12/5` widened to `σ ≤ 93/100` (`HuxleyNPWide`), and the all-character `12/5` on
`σ ≤ 4/5`.  The glue of the first two is the *proved* theorem
`Work.ZeroDensity.LogFree.nonPrincipalTwelveFifths`. -/
theorem area6_of_logFreeNP_and_huxleyNPWide (hRepGen : BGTZRepulsionGenE)
    (hlog : Work.ZeroDensity.LogFree.logFreeNP (93 / 100) (12 / 5))
    (hhux : Work.ZeroDensity.LogFree.HuxleyNPWide)
    (hH : Work.ZeroDensity.FamDensityEpsRange 0 (4 / 5) (12 / 5)) :
    Work.LinnikContract.Area6 :=
  area6_of_cores_v3 hRepGen (Work.ZeroDensity.LogFree.nonPrincipalTwelveFifths hlog hhux) hH

/-- The same with the BGTZ repulsion discharged. -/
theorem area6_of_logFreeNP_and_huxleyNPWide_proved
    (hlog : Work.ZeroDensity.LogFree.logFreeNP (93 / 100) (12 / 5))
    (hhux : Work.ZeroDensity.LogFree.HuxleyNPWide)
    (hH : Work.ZeroDensity.FamDensityEpsRange 0 (4 / 5) (12 / 5)) :
    Work.LinnikContract.Area6 :=
  area6_of_logFreeNP_and_huxleyNPWide BGTZRepulsionGenE_proved hlog hhux hH

end

end Work.LinnikAreas
