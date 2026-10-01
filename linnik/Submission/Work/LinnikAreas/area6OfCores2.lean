import Mathlib
import Submission.Work.LinnikAreas.area6Top
import Submission.Work.LinnikAreas.RepulsionCapDefs
import Submission.Work.LinnikAreas.RepulsionCap
import Submission.Work.LinnikAreas.BGTZRepE
import Submission.Work.LinnikAreas.PairDensityGen
import Submission.Work.LinnikAreas.siegelRestLowCap
import Submission.Work.LinnikAreas.boxSumCap
import Submission.Work.LinnikAreas.logFreeFamOfMontgomery
import Submission.Work.LinnikAreas.RestHighFreeGen
import Submission.Work.LinnikAreas.BGTZ.RestHighBGTZGenCGen
import Submission.Work.LinnikAreas.RestHighCombine
import Submission.Work.LinnikAreas.siegelExpansion
import Submission.Work.LinnikAreas.siegelSimpleInput
import Submission.Work.LinnikAreas.siegelZeroWeightSummable
import Submission.Work.LinnikAreas.BGTZ.ZFRInput_exists

/-!
# AREA 6 from Jutila's non-principal theorem plus **either** Montgomery or Huxley

This file re-runs the assembly of `Submission/Work/LinnikAreas/area6CapChain.lean` with the family
exponent `5/2` of the two `LogFreeFam` inputs **raised to `261/100 = 2.61`**, which is what makes
Montgomery's sharp large-sieve estimate (rather than Huxley's `12/5`) sufficient for the middle
range `3/5 ≤ σ ≤ 4/5` — see `Submission/Work/LinnikAreas/logFreeFamOfMontgomery.lean` for the
analysis of the three σ-ranges.

The chain is:

* `Work.LinnikAreas.BGTZRepulsionGenE` — the BGTZ repulsion at all heights
  (`Work.LinnikAreas.BGTZRepulsionGenE_proved`, proved and axiom-clean);
* Jutila's non-principal density theorem `Work.LinnikAreas.FamilyZeroDensityJutilaNP`
  (the statement of `Work.ZeroDensity.Jutila.jutilaNonPrincipal`);
* the *middle-range* density estimate, in either of the two forms
  * `Work.ZeroDensity.MontgomerySharp (1/1000)` (Montgomery's sharp large-sieve estimate, the
    chapter's own target `Work.ZeroDensity.Montgomery.montgomerySharp`), or
  * `Work.ZeroDensity.FamDensityEpsRange 0 (4/5) (12/5)` (Huxley's `12/5`),

and the conclusions are

* `area6_of_cores_v2 : BGTZRepulsionGenE → JutilaNP → MontgomerySharp (1/1000) → Area6`;
* `area6_of_cores_v2_allB` — the same with the `∀ B > 0` form of Montgomery;
* `area6_of_cores_v2_huxley : BGTZRepulsionGenE → JutilaNP → Huxley → Area6`.

Nothing else is used: no Huxley is needed in the first two, no Montgomery in the third, and no
clause of the frozen AREA 3 certificate `Work.LinnikContract.ZeroFreeCert` in any of them (the
capped repulsion `Work.LinnikAreas.repulsionWithCap_7_16` replaces it, exactly as in
`area6CapChain.lean`).
-/

namespace Work.LinnikAreas

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

open Work.LinnikContract

/-- **AREA 6 from Jutila's non-principal theorem, Montgomery's sharp large-sieve estimate and the
BGTZ repulsion.**  The family exponent is `261/100` throughout: it is what
`logFreeFamHalf_of_jutila_montgomery` / `logFreeFamHeight_of_jutila_montgomery` supply, and it
satisfies both `261/100 < 49/10` (the far-height requirement) and
`261/100 + 16/7 = 3427/700 < 49/10` (the Deuring--Heilbronn requirement of
`pairDensityInput_of_logFreeGen_and_capRepulsion`). -/
theorem area6_of_cores_v2 (hRepGen : BGTZRepulsionGenE)
    (hJ : FamilyZeroDensityJutilaNP) (hM : Work.ZeroDensity.MontgomerySharp (1 / 1000)) :
    Work.LinnikContract.Area6 := by
  obtain ⟨ε₀, hε₀pos, hε₀half, hrepCap⟩ := repulsionWithCap_7_16 hRepGen
  obtain ⟨cZ₀, _hcZ₀, _hzfrL₀, hrepGenC⟩ := hRepGen
  obtain ⟨cZ, hcZ, hzfr⟩ := Work.LinnikAreas.BGTZ.ZFRInput_exists
  have hcount : Work.ZeroDensity.LogFreeFamHalf ((261 : ℝ) / 100) :=
    logFreeFamHalf_of_jutila_montgomery hJ hM
  have hfam : Work.ZeroDensity.LogFreeFamHeight ((261 : ℝ) / 100) (3 / 2) :=
    logFreeFamHeight_of_jutila_montgomery hJ hM
  have hden : Work.LinnikAreas.Siegel.PairDensityInput :=
    pairDensityInput_of_logFreeGen_and_capRepulsion hε₀pos (by norm_num) (by norm_num) hcount hrepCap
  have hLow := siegelRestLowCap (ε₀ := ε₀) (c := 7 / 16) hε₀pos hε₀half (by norm_num)
    hrepCap hden
  have hC₀pos : (0 : ℝ) < max (1000 / cZ₀) 1000 :=
    lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  have hHigh := RestHighCombine (RestHighFreeGen hfam)
      (Work.LinnikAreas.BGTZ.RestHighBGTZGenCGen cZ (max (1000 / cZ₀) 1000) hcZ hC₀pos
        hrepGenC hfam hzfr)
  exact Siegel.area6_of 1 (siegelExpansion 1 le_rfl)
    (boxSumCap (ε₀ := ε₀) (c := 7 / 16) 1 le_rfl hε₀pos (by norm_num) siegelSimpleInput
      hrepCap (fun q _ χ => siegelZeroWeightSummable (q := q) (11 / 2) (3 / 10) χ) hLow hHigh)

/-- The same, with Montgomery's estimate in the `∀ B > 0` form in which the ZeroDensity chapter
states it (`Work.ZeroDensity.Montgomery.montgomerySharp`). -/
theorem area6_of_cores_v2_allB (hRepGen : BGTZRepulsionGenE)
    (hJ : FamilyZeroDensityJutilaNP)
    (hM : ∀ B : ℝ, 0 < B → Work.ZeroDensity.MontgomerySharp B) :
    Work.LinnikContract.Area6 :=
  area6_of_cores_v2 hRepGen hJ (hM (1 / 1000) (by norm_num))

/-- **AREA 6 from Jutila's non-principal theorem, Huxley's `12/5` and the BGTZ repulsion** — the
same chain as `area6_of_cores_v2`, with the middle-range input replaced by Huxley's family
estimate (the historical input of `area6CapChain.lean`).  Since a larger exponent is a weaker
hypothesis, `LogFreeFamHalf (5/2)` (Huxley at `ε = 1/10`) gives `LogFreeFamHalf (261/100)`, and
likewise in the height direction. -/
theorem area6_of_cores_v2_huxley (hRepGen : BGTZRepulsionGenE)
    (hJ : FamilyZeroDensityJutilaNP)
    (hH : Work.ZeroDensity.FamDensityEpsRange 0 (4 / 5) (12 / 5)) :
    Work.LinnikContract.Area6 := by
  obtain ⟨ε₀, hε₀pos, hε₀half, hrepCap⟩ := repulsionWithCap_7_16 hRepGen
  obtain ⟨cZ₀, _hcZ₀, _hzfrL₀, hrepGenC⟩ := hRepGen
  obtain ⟨cZ, hcZ, hzfr⟩ := Work.LinnikAreas.BGTZ.ZFRInput_exists
  have hcount : Work.ZeroDensity.LogFreeFamHalf ((261 : ℝ) / 100) :=
    logFreeFamHalf_of_jutila_huxley hJ hH
  have hfam : Work.ZeroDensity.LogFreeFamHeight ((261 : ℝ) / 100) (3 / 2) :=
    logFreeFamHeight_of_jutila_huxley hJ hH
  have hden : Work.LinnikAreas.Siegel.PairDensityInput :=
    pairDensityInput_of_logFreeGen_and_capRepulsion hε₀pos (by norm_num) (by norm_num) hcount hrepCap
  have hLow := siegelRestLowCap (ε₀ := ε₀) (c := 7 / 16) hε₀pos hε₀half (by norm_num)
    hrepCap hden
  have hC₀pos : (0 : ℝ) < max (1000 / cZ₀) 1000 :=
    lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  have hHigh := RestHighCombine (RestHighFreeGen hfam)
      (Work.LinnikAreas.BGTZ.RestHighBGTZGenCGen cZ (max (1000 / cZ₀) 1000) hcZ hC₀pos
        hrepGenC hfam hzfr)
  exact Siegel.area6_of 1 (siegelExpansion 1 le_rfl)
    (boxSumCap (ε₀ := ε₀) (c := 7 / 16) 1 le_rfl hε₀pos (by norm_num) siegelSimpleInput
      hrepCap (fun q _ χ => siegelZeroWeightSummable (q := q) (11 / 2) (3 / 10) χ) hLow hHigh)

/-- **AREA 6 with the BGTZ repulsion discharged**: from Jutila's non-principal theorem and
Montgomery's sharp large-sieve estimate alone (both as hypotheses of this statement). -/
theorem area6_of_jutila_montgomery (hJ : FamilyZeroDensityJutilaNP)
    (hM : Work.ZeroDensity.MontgomerySharp (1 / 1000)) : Work.LinnikContract.Area6 :=
  area6_of_cores_v2 BGTZRepulsionGenE_proved hJ hM

/-- **AREA 6 with the BGTZ repulsion discharged**, in the `∀ B > 0` form of Montgomery's estimate
(the ZeroDensity chapter's target `Work.ZeroDensity.Montgomery.montgomerySharp`). -/
theorem area6_of_jutila_montgomery_allB (hJ : FamilyZeroDensityJutilaNP)
    (hM : ∀ B : ℝ, 0 < B → Work.ZeroDensity.MontgomerySharp B) :
    Work.LinnikContract.Area6 :=
  area6_of_cores_v2_allB BGTZRepulsionGenE_proved hJ hM

/-- **AREA 6 with the BGTZ repulsion discharged**: from Jutila's non-principal theorem and
Huxley's `12/5` alone. -/
theorem area6_of_jutila_huxley (hJ : FamilyZeroDensityJutilaNP)
    (hH : Work.ZeroDensity.FamDensityEpsRange 0 (4 / 5) (12 / 5)) :
    Work.LinnikContract.Area6 :=
  area6_of_cores_v2_huxley BGTZRepulsionGenE_proved hJ hH

end

end Work.LinnikAreas
