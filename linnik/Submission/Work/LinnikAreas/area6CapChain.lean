import Mathlib
import Submission.Work.LinnikAreas.area6Top
import Submission.Work.LinnikAreas.RepulsionCapDefs
import Submission.Work.LinnikAreas.RepulsionCap
import Submission.Work.LinnikAreas.BGTZRepE
import Submission.Work.LinnikAreas.PairDensityCap
import Submission.Work.LinnikAreas.siegelRestLowCap
import Submission.Work.LinnikAreas.boxSumCap
import Submission.Work.LinnikAreas.logFreeFamHalfOfNonPrincipal
import Submission.Work.LinnikAreas.logFreeFamHeightOfNonPrincipal
import Submission.Work.LinnikAreas.RestHighFree
import Submission.Work.LinnikAreas.RestHighCombine
import Submission.Work.LinnikAreas.siegelExpansion
import Submission.Work.LinnikAreas.siegelSimpleInput
import Submission.Work.LinnikAreas.siegelZeroWeightSummable
import Submission.Work.LinnikAreas.BGTZ.RestHighBGTZGenC
import Submission.Work.LinnikAreas.BGTZ.ZFRInput_exists

/-!
# AREA 6 from the capped repulsion: **AREA 3 disappears from the dependency list**

This file assembles the frozen AREA 6 target from

* the *non-principal* Jutila family count `JutilaNonPrincipal`
  (`Work.ZeroDensity.Jutila.jutilaNonPrincipal`),
* Huxley's `12/5` family count `Work.ZeroDensity.FamDensityEpsRange 0 (4/5) (12/5)`,
* the BGTZ repulsion at all heights (`Work.LinnikAreas.BGTZRepulsionGenE`),

and **nothing else**: no clause of the frozen AREA 3 certificate
`Work.LinnikContract.ZeroFreeCert` is used.  The two former consumers of AREA 3 were

1. `Work.LinnikAreas.RepulsionWith (7/16)` (`RepulsionWith_of_ZeroFreeCert`), replaced here by the
   *capped* repulsion `RepulsionWithCap ε₀ (7/16)` (`LinnikAreas/RepulsionCap.lean`, proved from
   the proved unconditional zero-free region `BGTZ.ZFRInput` and the BGTZ repulsion);
2. the `λ₁`-saving density input `Siegel.PairDensityInput`, which `deuringHeilbronnLogFree`
   derives from the *uncapped* repulsion but which the capped repulsion also gives
   (`LinnikAreas/PairDensityCap.lean`).

The remaining pieces are the two `λ₁`-capped consumers `siegelRestLowCap` and `boxSumBoundCap`
(the uncapped `siegelRestLow`/`boxSumBound_of_inputs` with the repulsion hypothesis capped at
`λ₁ ≤ ε₀`), the `λ₁`-free high-zero bounds `RestHighFree`/`RestHighBGTZGenC`, the class-sum
expansion `siegelExpansion` (AREA 2), Landau's simplicity `siegelSimpleInput` and the kernel
summability `siegelZeroWeightSummable` --- all of them proved in this workspace and not using
AREA 3.
-/

namespace Work.LinnikAreas

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

open Work.LinnikContract

-- NOTE: the Jutila hypothesis is stated inline below (the name `JutilaNonPrincipal` is already
-- taken by `Submission.Work.LinnikAreas.area6CoresNp`, and the two modules may be imported
-- together).
/-- **AREA 6 from Jutila's non-principal theorem, Huxley's `12/5` and the BGTZ repulsion** --- the
frozen AREA 3 certificate is *not* used.  The `hJ` hypothesis is verbatim
`Work.ZeroDensity.Jutila.jutilaNonPrincipal`. -/
theorem area6_of_cores_cap (hRepGen : BGTZRepulsionGenE)
    (hJ : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ q : ℕ, 2 ≤ q → ∀ [NeZero q] (σ T : ℝ), (4 : ℝ) / 5 ≤ σ → σ ≤ 1 → 1 ≤ T →
        (∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
            Work.LinnikAreas.zeroCountIn χ σ T)
          ≤ C * ((q : ℝ) * T) ^ ((2 + ε) * (1 - σ)))
    (hH : Work.ZeroDensity.FamDensityEpsRange 0 (4 / 5) (12 / 5)) :
    Work.LinnikContract.Area6 := by
  obtain ⟨ε₀, hε₀pos, hε₀half, hrepCap⟩ := repulsionWithCap_7_16 hRepGen
  obtain ⟨cZ₀, _hcZ₀, _hzfrL₀, hrepGenC⟩ := hRepGen
  obtain ⟨cZ, hcZ, hzfr⟩ := Work.LinnikAreas.BGTZ.ZFRInput_exists
  have hcount : Work.ZeroDensity.LogFreeFamHalf (5 / 2) := logFreeFamHalfOfNonPrincipal hJ hH
  have hfam : Work.ZeroDensity.LogFreeFamHeight (5 / 2) (3 / 2) :=
    logFreeFamHeightOfNonPrincipal hJ hH
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

end

end Work.LinnikAreas
