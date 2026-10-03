import Mathlib
import Submission.Work.KMTPlan.A6.Final

/-! Guidance from the project lead (the requester):

CONTEXT (project lead). This is an area of the FROZEN KMT contract (Submission/Work/KMTContract/Areas.lean; composition
exists_varEstHalfFin_Cv_of_areas PROVED, so proving all eight areas closes the problem). Read first:
* Submission/Work/KMTPlan/ROUTE_LEAD.md: §1 the DAG, §3.1 your area with its proof sketch, §3.3 the quantifier order, §3.4 the audit;
* Submission/Work/KMTContract/README.md;
* KMTContract/QUARANTINE.md: never use the quarantined statements (the old Peluse/Improv/SingleScale ones are false or vacuous).
Many tools are already proved in Submission/Work/** and Submission/Commons/** (ROUTE_LEAD §2.1 lists them); reuse them and do not
re-request what exists. Parallelise: request all independent pieces at once, and write the assembly against their statements while they run.

A6 = VarpL2KMT: varp at (2,2,1) with the gain 2^{−c·lmax}, from A1 and ImprovKMT. Small scales: Rademacher–Menshov + IW + shifted CZ
(mostly proved). Large scales: sampling + Lépingle + the arithmetic bilinear estimate. Share the model-operator definitions with A7: write
KMTPlan/Model.lean first (ROUTE_LEAD §4 staffing).

## State of this file (session on `Work.KMTPlan.A6`, H61)

`Work.KMTAreas.area_A6` is the wiring `Work.KMTPlan.A6.areaA6_final`, which assembles the area
from the two cases of the quadruple (per `Work.KMTPlan.Model`):

* `CaseHH` (`1 ≤ k₁ ∧ 1 ≤ k₂`) — the paper's Proposition `high-high-l2` with the improvement of
  §5: **proved** (`Work.KMTPlan.A6.highHighCase`), from the named inputs
  `Sub.VanishingF/G`, `Sub.BesselF/G`, `Sub.NonAliasingSize`, `Sub.LogGain`, `Sub.GoodScaleArith`
  (all proved in `Submission/Work/KMTPlan/A6/`: `projVanishingF`, `projVanishingG`, `besselF`,
  `besselG`, `nonAliasing_of_size`, `logTerm_le_gain`, `goodScaleArith`);
* `CaseRest` (`k₁ = 0 ∨ k₂ = 0`) — the §6 reduction to the model operators plus the §7/§8 model
  estimates: `Work.KMTPlan.A6.lowCase`, which assembles the scale split `LcSmall` (`A6/lowCase`,
  `A6/lowSmallScaled`) and `LcLarge` (`A6/lowLargeScaled`).

The two-case assembly is `Work.KMTPlan.A6.areaA6_of_cases` (`A6/Assembly.lean`, proved).

The mathematical content still outstanding at the time of writing is confined to the low case:

* `A6/lowSmallScaled.lean` — from `A6/lowSmallModelVar.lean` (paper §7: Rademacher--Menshov
  `rm-bil` + the single-scale estimate `ssu`) and `A6/lowSmallModelApprox.lean` (the `ℓ¹`
  model approximation `mod-approx` at the small scales);
* `A6/lowLargeScaled.lean` — from `LowModApprox` (the `mod-approx` error on the large scales,
  `A6/LowModApproxExactEstimate.lean`), `LowModelGain` (the paper's `model-est-2` /
  `all-all-large-2` with the arithmetic bilinear estimate `bile`, `A6/LowModelGainEstimate.lean`)
  and `LowExceptional` (proved, `A6/LowExceptionalEstimate.lean`).

Each of these is the target of a live sub-agent of H61, and the whole `(2,2,1)` low case is
organised in `A6/`+`A7/`+`Submission/Work/A7/`; the plan is recorded in `NOTES_A6_lowCase.md`,
`NOTES_A6_lowLargeScaled.md` and `Submission/Work/KMTPlan/ROUTE_LEAD.md`.
-/
namespace Work.KMTAreas

theorem area_A6 : Work.KMTContract.AreaA6 := Work.KMTPlan.A6.areaA6_final

end Work.KMTAreas


