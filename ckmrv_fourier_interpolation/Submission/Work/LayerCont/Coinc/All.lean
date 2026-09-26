/-
# The removable-coincidence contour layer (`Work.LayerCont.Coinc`): everything in one import

CKMRV §5.3, the *far* side of the line `Re τ = 1`: the second `SL(2,ℤ)`-translate of `τ` of height
`1/τ.im`, the **removable coincidence** `coincℂ τ = ST⁻¹τ = -1/(τ-1)`, whose residue vanishes
(`φ(TS) = 0`, `Work.LayerCont.hasResidue_Kfun_coinc`).  All of the contour mechanics here is
residue-free; the modular input is imported, not reproved.

Import this module for the whole area.  The pieces:

* `Work.LayerCont.Coinc.Defs` — `coincℂ` and its elementary geometry (`coincℂ_im_pos`,
  `ofComplex_coincℂ`, `coincℂ_eq`, `coincℂ_re_eq`, `coincℂ_im_eq`,
  `coincℂ_mem_openLeftRectℂ_iff(_mul)`, `one_lt_re_of_coincℂ_re_neg`, `ofComplex_eq_coinc_iff`,
  `imagAxis_ne_coinc`, `imagAxis_ne_smul_neg_one_vadd`);
* `Work.LayerCont.Coinc.DlccGeneric` — the `z₀`-generic cleanliness lemmas `dlcc_clean_generic`,
  `dlcc_clean_coinc`, `dlcc_continuousOn_generic`, `dlcc_differentiableAt_generic`;
* `Work.LayerCont.Coinc.Residue` — `tendsto_coinc_residue` (the vanishing residue limit);
* `Work.LayerCont.Coinc.DetourCoinc` — `detourLeftC_eq_interval_of_coinc` (the main deliverable);
* `Work.LayerCont.Coinc.CoincClean` — `j`-cleanliness of the axis from orbit-exclusions;
* `Work.LayerCont.Coinc.layerLowCoinc_eq_layerLow_far` — far-side `layerLowCoinc = layerLow`
  (and the pointwise detour form `detourLeftC_eq_interval_of_coinc_pointwise`);
* `Work.LayerCont.Coinc.layerLowCoinc_eq_layerLow_at` — its pointwise (single `τ`) form;
* `Work.LayerCont.Coinc.layerLowDouble_eq_layerLowAt_far` — far-side double-piece agreement
  `layerLowDouble = layerLowAt + sinSqC r * resCorr r τ` (and
  `detourLeftC_eq_interval_of_noOrbit_pointwise`);
* `Work.LayerCont.Coinc.layerLowDouble_eq_layerLowAt_at` — its pointwise (single `τ`) form;
* `Work.LayerCont.Coinc.Far` — guarded/unguarded ball forms of the two detour identities
  (`detourLeftC_eq_interval_of_coinc_far`, `detourLeftC_eq_interval_of_noOrbit_far`), the
  literal unguarded layer agreements, and the `resCorr`-free forms
  (`layerLowDouble_sub_resCorr_eq_layerLowAt_far`).
-/
import Submission.Work.LayerCont.Coinc.Defs
import Submission.Work.LayerCont.Coinc.DlccGeneric
import Submission.Work.LayerCont.Coinc.Residue
import Submission.Work.LayerCont.Coinc.DetourCoinc
import Submission.Work.LayerCont.Coinc.CoincClean
import Submission.Work.LayerCont.Coinc.layerLowCoinc_eq_layerLow_far
import Submission.Work.LayerCont.Coinc.layerLowCoinc_eq_layerLow_at
import Submission.Work.LayerCont.Coinc.layerLowDouble_eq_layerLowAt_far
import Submission.Work.LayerCont.Coinc.layerLowDouble_eq_layerLowAt_at
import Submission.Work.LayerCont.Coinc.Far
