/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Area BcDiv: divisor base change `C_L ↔ C` over an `L`-field `F`, and the `SymBC` bundle

This module collects the files of area `BcDiv`:

* `Basic` — the comparison square `Work.BcDiv.BCSquare.cmp` of two base changes of a curve and the
  identification `Work.BcDiv.bcDiv : Dv (C_L) F ≃+ Dv C F` of the divisor groups (B1);
* `deg_bcDiv`, `linEquiv_bcDiv_iff`, `ell_bcDiv` — degree, linear equivalence and `ℓ` are
  preserved by `bcDiv` (B2);
* `Points`, `ramIdx_cmp`, `bcDiv_ptDiv` — the point-level shadow `Work.BcDiv.bcPtK` and point
  divisors (B3);
* `bcDiv_bc` — compatibility of `bcDiv` with the base change `DivBase.bc` of SY (B4);
* `SymPts`, `PbPt`, `betaK_surjective`, `betaK_isAffineHom`, `ptsK_map`, `powMap_betaK` — the
  comparison `βK` of symmetric powers, its affineness and surjectivity, and the induced bijection
  `ptsK` on field points with its naturality (B5);
* `divOf_ptsK` — compatibility of `divOf` with `bcDiv` (B6);
* `symBCBundle` — the assembly of area CH's bundle `Work.Charts.SymBC` (B7);
* `Tower`, `Transport` — auxiliary material on composite algebra structures and on the transport
  of `divOf` along an equality of indices.
-/
import Submission.Work.BcDiv.Basic
import Submission.Work.BcDiv.PbPt
import Submission.Work.BcDiv.Points
import Submission.Work.BcDiv.SymPts
import Submission.Work.BcDiv.Tower
import Submission.Work.BcDiv.Transport
import Submission.Work.BcDiv.deg_bcDiv
import Submission.Work.BcDiv.linEquiv_bcDiv_iff
import Submission.Work.BcDiv.ell_bcDiv
import Submission.Work.BcDiv.ramIdx_cmp
import Submission.Work.BcDiv.bcDiv_ptDiv
import Submission.Work.BcDiv.bcDiv_bc
import Submission.Work.BcDiv.betaK_surjective
import Submission.Work.BcDiv.betaK_isAffineHom
import Submission.Work.BcDiv.ptsK_map
import Submission.Work.BcDiv.powMap_betaK
import Submission.Work.BcDiv.divOf_ptsK
import Submission.Work.BcDiv.symBCBundle

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.

