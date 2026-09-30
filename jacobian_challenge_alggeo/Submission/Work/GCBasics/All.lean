/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Area GB (GCBasics) — the exported API

Import this module to get the whole chapter of shared conventions of the Jacobian drive:

* `Work.GCBasics.Basic` — `Sch`, `specOf`, `RPt`, `FPt`, `RPt.map`, `RPt.LandsIn`,
  `resField`, `resPt`, `genPt`, `closedPt`, `Opens.toOver`, `Opens.ιOver`, `Dominates`,
  and the scoped bridge `overClass`;
* `Work.GCBasics.Points` — points of products, points of opens and points of glued schemes,
  and `exists_valuationSubring_dominating`;
* `Work.GCBasics.DivApi` — `Dv`, `Ddeg`, `ell`, `LinEquiv` (with its basic laws), `prin`,
  `div0`, `Pic`, `Pic0` and their class maps;
* `Work.GCBasics.DivBaseChange` — the interface for base change of divisors along field
  extensions (`ell_baseChange`, `linEquiv_baseChange_iff`), a named input from area CB;
* `Work.GCBasics.GC` — the same names under the `Work.GC` name used in the lead's notes.

Further results (all over Mathlib, area CB and the files above):

* `Work.GCBasics.hom_ext_of_resPt` — morphisms out of a reduced `K`-scheme are detected by
  residue-field points (HOMEXT of the shared conventions);
* `Work.GCBasics.ell_eq_of_linEquiv` — `ℓ` is invariant under linear equivalence;
* `Work.GCBasics.linEquiv_eq_of_ell_eq_one` — `ℓ(D) = 1` for effective `D` pins down the
  representative;
* `Work.GCBasics.ell_eq_one_iff` — the characterisation of `ℓ(D) = 1` by uniqueness of the
  effective representative (given `ℓ(0) = 1`, an input from area RR);
* `Work.GCBasics.ell_le_one_of_deg_eq_zero` — an effective divisor of degree zero has
  `ℓ ≤ 1`;
* `Work.GCBasics.fpt_exists_factor` — a field point of a glued scheme factors through one
  of the pieces;
* `Work.GCBasics.map_landsIn` — landing in an open subscheme is preserved by base change of
  the field of definition;
* `Work.GCBasics.div_eq_zero_iff_isConstant` — a rational function with trivial divisor is
  constant;
* `Work.GCBasics.closedPt_apply`, `Work.GCBasics.genPt_apply` — the value of `closedPt` and
  of `genPt` at the closed point of the spectrum.
-/
import Submission.Work.GCBasics.Basic
import Submission.Work.GCBasics.Points
import Submission.Work.GCBasics.DivApi
import Submission.Work.GCBasics.DivBaseChange
import Submission.Work.GCBasics.GC
import Submission.Work.GCBasics.hom_ext_of_resPt
import Submission.Work.GCBasics.ell_eq_of_linEquiv
import Submission.Work.GCBasics.linEquiv_eq_of_ell_eq_one
import Submission.Work.GCBasics.ell_eq_one_iff
import Submission.Work.GCBasics.ell_le_one_of_deg_eq_zero
import Submission.Work.GCBasics.fpt_exists_factor
import Submission.Work.GCBasics.map_landsIn
import Submission.Work.GCBasics.div_eq_zero_iff_isConstant
import Submission.Work.GCBasics.closedPt_apply
import Submission.Work.GCBasics.genPt_apply

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.

