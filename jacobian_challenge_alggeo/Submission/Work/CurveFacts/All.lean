/-
Copyright (c) 2026 The Jacobian challenge team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: area CurveFacts
-/
import Submission.Work.CurveFacts.SmoothReduced
import Submission.Work.CurveFacts.CurveOfOver
import Submission.Work.CurveFacts.smooth_sections
import Submission.Work.CurveFacts.KrullDim.ringKrullDim_le_of_isLocalization
import Submission.Work.CurveFacts.KrullDim.ringKrullDim_le_of_isStandardEtale
import Submission.Work.CurveFacts.KrullDim.rank_kaehler_of_isStandardEtale
import Submission.Work.CurveFacts.KrullDim.ringKrullDimLE_one_of_etale_mvPolynomial_fin_one
import Submission.Work.CurveFacts.KrullDim.krullDimLE_localizationAtPrime_of_isStandardSmoothOfRelativeDimension_one
import Submission.Work.CurveFacts.krullDimLE_stalk_of_smoothOfRelativeDimension_one
import Submission.Work.CurveFacts.nontrivial_of_smoothOfRelativeDimension_one
import Submission.Work.CurveFacts.chartRing_isIntegrallyClosed
import Submission.Work.CurveFacts.isIntegrallyClosed_stalk_sym
import Submission.Work.CurveFacts.isIntegrallyClosed_stalk_sym_tensor
import Submission.Work.CurveFacts.bcKF_ptDiv
import Submission.Work.CurveFacts.ptBaseChange_prod
import Submission.Work.CurveFacts.ptBaseChange_prodV
import Submission.Work.CurveFacts.AddCompat
import Submission.Work.CurveFacts.SymSumMap
import Submission.Work.CurveFacts.symSumMap_addMap
import Submission.Work.CurveFacts.isAddSumMap_of_isAddSumMapPow
import Submission.Work.CurveFacts.kl_add_of_input_pow
import Submission.Work.CurveFacts.kl_of_input_of_isProper
import Submission.Work.CurveFacts.kl_of_input
import Submission.Work.CurveFacts.kl_add_of_input

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


/-!
# Area `CurveFacts` — the whole chapter

Import this module for everything of area `CurveFacts`
(`Submission/Work/NOTES_LEAD_jacobian_closure.md` §2.A, items A1–A6):

* **A1** `Work.CurveFacts.isReduced_of_smooth`, `Work.CurveFacts.geometricallyReduced_of_smooth`;
* **A2** `Work.CurveFacts.krullDimLE_stalk_of_smoothOfRelativeDimension_one`;
* **A3** `Work.CurveFacts.nontrivial_of_smoothOfRelativeDimension_one`;
* **A4** `Work.CurveFacts.isIntegrallyClosed_stalk_sym`,
  `Work.CurveFacts.isIntegrallyClosed_stalk_sym_tensor`;
* **A5** `Work.CurveFacts.bcKF_ptDiv`;
* **A6** `Work.CurveFacts.kl_of_input`, `Work.CurveFacts.kl_add_of_input` (and the variants
  `Work.CurveFacts.kl_of_input_of_isProper`, `Work.CurveFacts.kl_add_of_input_pow`);

and, for the two interface defects of area `UP`/`GC` that A6 exposes,

* `Work.CurveFacts.IsAddSumMap`, `Work.CurveFacts.IsAddSumMapPow` (`AddCompat.lean`) -- the
  `addMap`/`sumMap` compatibility that `Work.GroupChunk.Input` does not carry;
* `Work.CurveFacts.symSumMap`, `Work.CurveFacts.symSumMap_addMap` (`SymSumMap.lean`,
  `symSumMap_addMap.lean`) -- that compatibility, **proved** for the concrete symmetric powers of
  area `SY`;
* `Work.CurveFacts.isAddSumMap_of_isAddSumMapPow` -- the upgrade from the `powMap`-level datum to
  the field-point datum that `kl_add` consumes;

together with the convenience constructor `Work.CurveFacts.curveOfOver` (A1+A2+A3 give the three
extra fields of `Work.CurveBasics.Curve`) and the auxiliary results of the subdirectory
`Submission/Work/CurveFacts/KrullDim/`.

See `Submission/Work/CurveFacts/NOTES.md` for the item-by-item index and for the two deviations
from the requested statement types (`Work.Universal.Input.kl` needs `[IsProper A.hom]`, and
`Work.Universal.Input.kl_add` needs the `addMap`/`sumMap` compatibility
`Work.CurveFacts.IsAddSumMap`).
-/
