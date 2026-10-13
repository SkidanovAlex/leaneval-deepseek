/-
Work module for the Elgindi finite-time singularity project.

# `AeI1Fts/I1PaperWeakMixed` — the `I₁` bound of the paper in the weak (a.e.) class

This module used to carry all of the development of the `I₁` bound of Elgindi's Step 2
(Annals **194** (2021), tex 873–890) in the a.e. class `AeData`; it was 45 KB, above the
project's 30 KB-per-file build guard.  The content now lives in three chunks with the *same*
namespace and declaration names, and this file is the aggregator:

* `AeI1Fts/I1WMSliceA.lean` — the `θ`-slice flux/IBP bounds `slice_second_of_ibp`,
  `slice_flux_ibp_small`, `slice_second_le_flux`, `slice_second_le_flux_small`;
* `AeI1Fts/I1WMSliceB.lean` — `slice_second_le_cut`, `integrableOn_Iθo_of_*`,
  `slice_second_le_cut_auto` (the `θ`-cutoff route, where the end-point flux input is free);
* `AeI1Fts/I1WMOuter.lean` — `Upsi_slice_bound_integrated`, `Upsi_bound_integrated` and the
  leaf theorem `I1PaperWeakMixed` (still open).

Consumers keep importing `Submission.Work.FTS.EllipticEst.AeI1Fts.I1PaperWeakMixed`.
-/
import Mathlib.Tactic.MinImports
import Submission.Work.FTS.EllipticEst.H2W.Ae.Defs
import Submission.Work.FTS.EllipticEst.AngAWeak.Basic
import Submission.Work.FTS.EllipticEst.remov.AeI1PaperDefs
import Submission.Work.FTS.EllipticEst.AeI1Fts.Defs
import Submission.Work.FTS.EllipticEst.AngAWeak.slicePairIneqFluxFree
import Submission.Work.FTS.EllipticEst.H2W.SlotA.sharpHardyOpen
import Submission.Work.FTS.EllipticEst.AeI1Fts.Upsi_A_integrable
import Submission.Work.FTS.EllipticEst.AeI1Fts.Upsi_P_integrable_ae
import Submission.Work.FTS.EllipticEst.AeI1Fts.I1WMSliceA
import Submission.Work.FTS.EllipticEst.AeI1Fts.I1WMSliceB
import Submission.Work.FTS.EllipticEst.AeI1Fts.I1WMOuter

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end
