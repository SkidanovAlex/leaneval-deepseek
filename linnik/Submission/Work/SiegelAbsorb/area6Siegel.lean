import Mathlib
import Submission.Work.SiegelAbsorb.area6SiegelOfInputs
import Submission.Work.SiegelAbsorb.highMassRep2
import Submission.Work.SiegelAbsorb.RestHighBGTZSiegel_of_window
import Submission.Work.SiegelAbsorb.pairDensityInput_siegel
import Submission.Work.SiegelAbsorb.famCountCrudeCorollaries
import Submission.Work.LinnikAreas.RepulsionCap
import Submission.Work.LinnikAreas.BGTZRepE
import Submission.Work.LinnikAreas.BGTZ.ZFRInput_exists
import Submission.Work.LinnikAreas.RestHighFreeGen

/-!
# `Work.SiegelAbsorb.area6Siegel` — **AREA 6 by Siegel absorption**, without Jutila, Huxley or
Montgomery

This is the final assembly of the Siegel-absorption route
(`Submission/Work/LinnikAreas/AREA6_ROUTE_LEAD.md`).  Every input is a theorem of this workspace,
axiom-clean:

* the capped Deuring–Heilbronn repulsion `repulsionWithCap_7_16` (`LinnikAreas/RepulsionCap.lean`),
  fed by the proved BGTZ repulsion at all heights (`LinnikAreas/BGTZRepE.lean`,
  `Work.LinnikAreas.BGTZRepulsionGenE_proved`);
* the two family counts of the middle of the argument
  (`SiegelAbsorb/famCount_nearLine.lean`, U4: coefficient `5/2` on `σ ≥ 93/100`;
  `SiegelAbsorb/famCountCrudeCorollaries.lean`, U3: the crude coefficient `9/2` on all of `[0,1]`);
* `SiegelAbsorb/logFreeNP34.lean`, U1: the log-free non-principal estimate
  `logFreeNP (3/4) (9/2)`, which is what U3 rests on for `σ ≥ 3/4`;
* `SiegelAbsorb/lamOf_ge_exp_neg.lean`, U2: Siegel's lower bound for `λ₁` in the exponential form
  `exp (-(a·log q)) ≤ λ₁` for any `a > 1/200` (used with `a = 21/1000` and `a = 7/250`);
* `SiegelAbsorb/dhCapTrunc.lean`, U5: the two-exponential matching on the truncated range
  `t ≤ (7/100)·𝓛` (exponent `67/14 < 24/5`);
* `SiegelAbsorb/pairDensityInput_siegel.lean`, U6: the `λ₁`-saving Deuring–Heilbronn count
  `Siegel.PairDensityInput` with `c = 24/5`;
* `SiegelAbsorb/highMassRep2.lean`, U8, and `SiegelAbsorb/RestHighBGTZSiegel_of_window.lean`, U9:
  the two-regime per-window mass bound and its conversion into the `λ₁`-saving far-zero bound
  `RestHighBGTZSpec (-3/2)`;
* `SiegelAbsorb/area6SiegelOfInputs.lean`: the (unchanged) AREA 6 assembly
  `siegelRestLowCap` → `boxSumCap` → `Siegel.area6_of`.

`area6_siegelRoute : Work.LinnikContract.Area6` is therefore a theorem of the workspace with no
analytic input beyond the proved AREA 6 chain; in particular it uses neither
`Work.ZeroDensity.Huxley.huxleyTwelveFifths` nor `Work.ZeroDensity.Jutila.jutilaNonPrincipal` nor
`Work.ZeroDensity.Montgomery.montgomerySharp` (all three of which still contain `sorry`s, and the
first two of which carry the *all-character* estimate on the middle range `σ ∈ [1/2, 3/4]`).
-/

namespace Work.SiegelAbsorb

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

open Work.LinnikContract

/-- **The `λ₁`-saving far-zero bound from the BGTZ repulsion and the two proved family counts.**
This is `Work.LinnikAreas.BGTZ.RestHighBGTZGenC` with the coefficient-`5/2` family count replaced
by the pair (near-line `5/2` on `σ ≥ 93/100`, crude `9/2` on `[0,1]`): the free (`λ ≥ λ₁`) branch
uses the crude count through `RestHighFree_of_lt`-style Abel summation, and the small-`λ₁` branch
uses `highMassRep2` (`WindowBoundHyp`) together with Siegel's lower bound in the form
`exp (-(7/250)·log q) ≤ λ₁`. -/
theorem RestHighBGTZSiegel (cZ C₀ : ℝ) (hcZ : 0 < cZ) (hC₀ : 0 < C₀)
    (hrep : Work.LinnikAreas.BGTZ.RepulsionGenC (11 / 5) (11 / 10) C₀)
    (hzfr : Work.LinnikAreas.BGTZ.ZFRInput cZ) :
    Work.LinnikAreas.Siegel.RestHighBGTZSpec (-3 / 2) :=
  RestHighBGTZSiegel_of_window
    (fun C₂ C₃ D₀ hC₂ hC₃ hD₀ => highMassRep2 C₂ C₃ D₀ hC₂ hC₃ hD₀)
    cZ C₀ hcZ hC₀ hrep hzfr

/-- **AREA 6 (the Siegel-zero case of Linnik's theorem) by Siegel absorption.** -/
theorem area6_siegelRoute : Work.LinnikContract.Area6 := by
  obtain ⟨ε₀, hε₀pos, hε₀half, hrepCap⟩ :=
    Work.LinnikAreas.repulsionWithCap_7_16 Work.LinnikAreas.BGTZRepulsionGenE_proved
  obtain ⟨cZ₀, _hcZ₀, _hzfrL₀, hrepGenC⟩ := Work.LinnikAreas.BGTZRepulsionGenE_proved
  obtain ⟨cZ, hcZ, hzfr⟩ := Work.LinnikAreas.BGTZ.ZFRInput_exists
  have hC₀pos : (0 : ℝ) < max (1000 / cZ₀) 1000 :=
    lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  exact area6_siegel_of_inputs hε₀pos hε₀half hrepCap
    (pairDensityInput_siegel hε₀pos hrepCap)
    (Work.LinnikAreas.RestHighFree_of_lt (by norm_num) logFreeFamHeight_crude)
    (RestHighBGTZSiegel cZ (max (1000 / cZ₀) 1000) hcZ hC₀pos hrepGenC hzfr)

end

end Work.SiegelAbsorb
