/-
# Area `LCSmooth`: everything in one import

`import Submission.Work.LCSmooth.All` brings in

* `Work.LCSmooth.smoothGrade` — the grade `∞` of the project, with
  `smoothGrade_eq_final : smoothGrade = Work.Final.smoothGrade` and
  `smoothGrade_eq_infty : smoothGrade = (∞ : ℕ∞ω)`;
* `Work.LCSmooth.lcConn_contMDiff` — the smoothness of the Levi-Civita connection in the generic
  framework variable block (with the instance `instContMDiffCovariantDerivativeLcConn`), and
  `Work.LCSmooth.lcConn_contMDiff_homSection`, the same fact unwound;
* `Work.LCSmooth.chartedRiemConn` / `instChartedRiemConn` — the Levi-Civita connection of a
  `Work.Final.ChartedRiem` manifold bundled as a `Work.Final.ChartedRiemConn`
  (smooth, torsion free, metric compatible);
* `Work.LCSmooth.cov_smooth`, `Work.LCSmooth.mhatCov_contMDiff`, `Work.LCSmooth.cov_smooth_infty`
  — **the `cov_smooth` field of `Work.Final.FinalInputs`** at the assembled space `M̂`, together
  with the global instance `instContMDiffCovariantDerivativeMhatCov` that discharges it by
  typeclass inference, and the bundled connection `mhatChartedRiemConn`;
* `Work.LCSmooth.mhatLES`, `Work.LCSmooth.mhatLES_hX` — the Mayer–Vietoris long exact sequence of
  the cover `M̂ = A ∪ B` and the identification of its `(k,2)`-slot with the singular homology of
  `M̂`, both constructed from `[Work.Space.RTData]` alone (the values of the fields `L` and `hX`);
* the curvature field from either curvature datum (`Work.LCSmooth.curvLe_of_models_mhat`,
  `Work.LCSmooth.curvLe_of_secNonpos_mhat`) and the assemblers of `Work.Final.FinalInputs`
  (`Work.LCSmooth.finalInputsOfCurvLe`, `…OfModels`, `…OfSecNonpos`, `…OfModelsAndMV`,
  `…OfCurvLeAndMV`);
* the challenge theorem from the still-owed data,
  `Work.LCSmooth.aspherical_integer_homology_four_sphere_of_homology_data` (inputs: the chart-model
  curvature datum `hmodels` and the homology identifications `eM`, `eN`, `hsq`), and
  `…_of_data` / `…_of_inputs` with the Mayer–Vietoris data supplied explicitly;
* the delegated chapter items `Work.LCSmooth.contMDiffOn_chrB` (the chart Christoffel symbol of a
  smooth connection is `C^∞`), `Work.LCSmooth.contMDiffOn_dB` (its derivative in the base point
  likewise) and `Work.LCSmooth.chartGram_mhatCov_chrB_eq_koszul` (the Koszul identity in charts
  for the connection of `M̂`, with no hypotheses).

See `Submission/Work/LCSmooth/NOTES.md` for the report.
-/
import Submission.Work.LCSmooth.Defs
import Submission.Work.LCSmooth.Mhat
import Submission.Work.LCSmooth.MhatMV
import Submission.Work.LCSmooth.Field
import Submission.Work.LCSmooth.contMDiffOn_chrB
import Submission.Work.LCSmooth.chartGram_mhatCov_chrB_eq_koszul
import Submission.Work.LCSmooth.contMDiffOn_dB

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.LCSmooth

end Work.LCSmooth
