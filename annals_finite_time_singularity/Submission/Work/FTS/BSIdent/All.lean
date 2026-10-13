/-
# `Work.FTS.BSIdent.All` — the umbrella import of the `BSIdent` chapter

Import this module to obtain the whole chapter: the definitions (`Defs`), the curl identity
(`Curl`), the identification (`Ident`, `Package`, `Liouville.Hid`), **route C** (`Weyl/*`,
`hid_of_pointwise`, `hid_of_corrected`), the geometry of the ansatz field (`Bundle`) and its
supporting calculus (`OddExt/*`, `Cyl/*`, `Auxiliary` style helpers).

## What is here

* `Work.FTS.BSIdent.Uax`, `PhiOdd`, `PhiOddSlice`, `ssPsi`, `merPsi` — the vocabulary (`Defs`);
* `Work.FTS.BSIdent.vorticity_psiField_merPsi` — **the curl identity**: on `Uax`, the vorticity of
  the ansatz field is the re-signed physical vorticity `−physOmega`;
* **ROUTE C (the lead's prescription, `FTS_HARD_DESIGN.md` §(C))** —
  * `Work.FTS.BSIdent.Weyl.weylPairPrinciple` — the Weyl/Liouville pair principle, discharged from
    the (now hole-free) `Work.FTS.PressureOn.weyl_pair`;
  * `Work.FTS.BSIdent.Weyl.weakGrad_zero_of_pointwise_div`,
    `…weakCurl_zero_of_pointwise_curl` — the two weak equations of a field from *pointwise*
    identities off the two coordinate planes;
  * `Work.FTS.BSIdent.Weyl.physVel_neg_physOmega_slice` — the curl/divergence/`C¹`/decay package of
    `physVel (−physOmega)` from `RegPkg`;
  * `Work.FTS.BSIdent.psiFieldCorr` (`Weyl/Corrected.lean`) — the **corrected** stream-function
    field (the Lean `Cyl.psiField` jumps at the axis; see the module docstring there);
  * `Work.FTS.BSIdent.Weyl.continuous_psiFieldCorr` — the pasting lemma making `psiFieldCorr`
    continuous from the one-sided axis limits;
  * `Work.FTS.BSIdent.Weyl.merPsi_corrected_bundle` — the geometric bundle (continuity + decay) of
    the corrected ansatz field for the concrete meridian data;
  * **`Work.FTS.BSIdent.hid_of_pointwise`** — **THE IDENTIFICATION BY ROUTE C**: from the
    corrected field's continuity, decay and agreement on `Uax` (plus the elliptic law and the
    off-axis `C²` of the meridian stream function) it concludes the design's `hid`;
  * **`Work.FTS.BSIdent.hid_of_corrected`** — the same with the corrected field *exhibited* from
    the analytic data of `Φ` (no `BiotSavartInverse`, no `DivCurlLiouville`, no `C¹` at the axis);
* `Work.FTS.BSIdent.hid_of_biotSavartInverse`, `hid`, `hid_of_IsBslSol` (`Ident`, `Package`) —
  **route A**, from `Work.LWP.BiotSavartInverse`;
* `Work.FTS.BSIdent.hid_of_divCurlLiouville` (`Liouville/Hid.lean`) — **route B**;
* `Work.FTS.BSIdent.AnsatzBundle`, `AnsatzBundleSub` (`Bundle.lean`) — the bundle predicates, their
  model case and their inhabitation.

`NOTES.md` (same directory) records the provenance of every hypothesis, the sign convention, the
axis artefact, and the one-line change the design's firing theorem needs.
-/
import Mathlib.Tactic.MinImports
import Submission.Work.FTS.BSIdent.Defs
import Submission.Work.FTS.BSIdent.Curl
import Submission.Work.FTS.BSIdent.Ident
import Submission.Work.FTS.BSIdent.Package
import Submission.Work.FTS.BSIdent.Bundle
import Submission.Work.FTS.BSIdent.Liouville.Hid
import Submission.Work.FTS.BSIdent.Weyl
import Submission.Work.FTS.BSIdent.Weyl.Corrected
import Submission.Work.FTS.BSIdent.Weyl.weylPairPrinciple
import Submission.Work.FTS.BSIdent.Weyl.weakGrad_zero_of_pointwise_div
import Submission.Work.FTS.BSIdent.Weyl.weakCurl_zero_of_pointwise_curl
import Submission.Work.FTS.BSIdent.Weyl.physVel_neg_physOmega_slice
import Submission.Work.FTS.BSIdent.Weyl.continuous_psiFieldCorr
import Submission.Work.FTS.BSIdent.Weyl.merPsi_corrected_bundle
import Submission.Work.FTS.BSIdent.hid_of_pointwise
import Submission.Work.FTS.BSIdent.hid_of_corrected
import Submission.Work.FTS.BSIdent.Defs.dense_Uax
import Submission.Work.FTS.BSIdent.Defs.contDiffAt_merPsi_slice
import Submission.Work.FTS.BSIdent.Defs.contDiffAt_Phi_of_merPsi
import Submission.Work.FTS.BSIdent.Defs.contDiffAt_psiField_merPsi_of_mem_Uax
import Submission.Work.FTS.BSIdent.Parity.isOdd_sub
import Submission.Work.FTS.BSIdent.Cyl.div_psiField_merPsi
import Submission.Work.FTS.BSIdent.Cyl.psiField_r_mul_V_eq_axiField
import Submission.Work.FTS.BSIdent.Cyl.sublinear_axiField
import Submission.Work.FTS.BSIdent.Axi.contDiff_axiField
import Submission.Work.FTS.BSIdent.Liouville.biotSavart_congr_ae
import Submission.Work.FTS.BSIdent.Liouville.continuous_vorticity_of_contDiff
import Submission.Work.FTS.BSIdent.OddExt.bslOp_PhiOdd_of_pos
import Submission.Work.FTS.BSIdent.OddExt.bslOp_PhiOdd_of_neg
import Submission.Work.FTS.BSIdent.OddExt.bslOp_const_mul
import Submission.Work.FTS.BSIdent.OddExt.pthIter_PhiOdd_of_neg
import Submission.Work.FTS.BSIdent.OddExt.pzIter_PhiOdd_of_neg
import Submission.Work.FTS.BSIdent.Bundle.ansatzBundleSub_of_r_mul_V
import Submission.Work.FTS.BSIdent.Curl.bslOp_eq_of_vorticity_eq
import Submission.Work.FTS.BSIdent.Curl.exists_mem_Uax_rho_theta
import Submission.Work.FTS.BSIdent.Parity.isOdd_physVel_neg_physOmega

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end
