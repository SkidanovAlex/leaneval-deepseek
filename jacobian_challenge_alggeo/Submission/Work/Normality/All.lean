/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Area NM — normality of the curve powers and of `Symⁿ C`: the exported API

Import this module to get the whole normality chapter.  The consumers are the `DM`/`DOM` engine
(which needs `∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)` for `X = Sym^N C` and for the
curve powers) and `UP`.

## The scheme-level predicate

* `Work.Normality.HasIntegrallyClosedStalks X` — by definition
  `∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)`.

## How to produce it

* `Work.Normality.HasIntegrallyClosedStalks.of_isAffineOpen_cover` — a scheme covered by affine
  opens whose rings of sections are domains and integrally closed has integrally closed stalks.
  This is the form used for `Symⁿ C`, whose charts are the spectra of the invariant rings
  `(Γ(C,U)^{⊗n})^{S_n}` (see `Work.Normality.hasIntegrallyClosedStalks_of_invariants_charts`).
* `Work.Normality.hasIntegrallyClosedStalks_of_smooth` — a smooth, integral scheme over a field
  has integrally closed stalks; this is the form used for `Cⁿ`
  (see `Work.Normality.isIntegrallyClosed_stalk_pow`).
* `Work.Normality.hasIntegrallyClosedStalks_of_isStandardSmooth_charts` — the same conclusion from
  standard smooth charts over the base field, which is the interface used to prove the previous
  item.

## The algebra behind it

* `Work.Normality.isIntegrallyClosed_of_smooth` — **the main theorem**: a domain which is standard
  smooth of relative dimension `n` over a field is integrally closed;
* `Work.Normality.isIntegrallyClosed_of_isStandardSmooth`, and the stronger
  `Work.Normality.isIntegrallyClosed_of_smooth_algebra` — a domain which is a smooth algebra over
  a field is integrally closed;
* `Work.Normality.isIntegrallyClosed_invariants` — the fixed points of a finite group acting on an
  integrally closed domain are integrally closed (plus
  `Work.Normality.isIntegrallyClosed_invariants_of_smooth`, the form used for the charts of
  `Symⁿ C`);
* `Work.Normality.isIntegrallyClosed_stalk_of_isAffineOpen` — localising an integrally closed
  domain at a prime gives an integrally closed ring.
-/
import Submission.Work.Normality.Basic
import Submission.Work.Normality.CurvePow
import Submission.Work.Normality.Scheme
import Submission.Work.Normality.Sym
import Submission.Work.Normality.bijective_mapBaseChange_complement
import Submission.Work.Normality.formallySmooth_of_bijective_mapBaseChange
import Submission.Work.Normality.hasIntegrallyClosedStalks_of_smooth
import Submission.Work.Normality.injective_algebraMap_tensorProduct_fractionRing
import Submission.Work.Normality.isDomain_tensorProduct_fractionRing
import Submission.Work.Normality.isField_of_etale_of_isDomain
import Submission.Work.Normality.isIntegrallyClosedIn_tensorProduct_fractionRing
import Submission.Work.Normality.isIntegrallyClosed_invariants
import Submission.Work.Normality.isIntegrallyClosed_of_smooth
import Submission.Work.Normality.isIntegrallyClosed_of_smooth_algebra
import Submission.Work.Normality.isIntegrallyClosed_stalk_of_isAffineOpen
import Submission.Work.Normality.isIntegrallyClosed_stalk_pow

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.

