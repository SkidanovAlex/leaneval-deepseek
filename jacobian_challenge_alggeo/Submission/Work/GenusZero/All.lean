/-
Copyright (c) 2026 The Jacobian challenge team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: area GenusZero
-/
import Submission.Work.GenusZero.Basic
import Submission.Work.GenusZero.PointDiv
import Submission.Work.GenusZero.Principal
import Submission.Work.GenusZero.Principal.linEquiv_of_deg_eq
import Submission.Work.GenusZero.Const
import Submission.Work.GenusZero.Rigidity
import Submission.Work.GenusZero.Rigid.isConstant_of_genus_zero
import Submission.Work.GenusZero.Albanese.exists_unique_ofCurve_comp_of_genus_zero
import Submission.Work.GenusZero.PointSum.sumMapOfModel_eq_of_deg_eq_of_genus_zero
import Submission.Work.GenusZero.Over.exists_unique_comp_toUnit_ofOver
import Submission.Work.GenusZero.Trivial

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


/-!
# Area GenusZero: the `g = 0` Jacobian package

The complete area.  Importing this module gives access to

* `Work.GenusZero.principal_of_deg_zero` — Riemann–Roch at genus zero: a divisor of degree zero
  on a curve of genus zero is principal; together with its consequences
  `Work.GenusZero.deg_eq_zero_iff_principal` (principal ⇔ degree zero) and
  `Work.GenusZero.linEquiv_iff_deg_eq` (`Principal.lean`), and
  `Work.GenusZero.Principal.linEquiv_of_deg_eq`;
* `Work.GenusZero.const_of_genus_zero_hasPoint` — rigidity: a morphism from a curve of genus
  zero with a rational point to an abelian variety is constant (`Const.lean`);
* `Work.GenusZero.eq_const_of_genus_zero` — the pointed form of rigidity, in the shape required
  by the challenge, and its `Over`-level restatement
  `Work.GenusZero.eq_const_of_genus_zero_ofOver` (`Rigidity.lean`);
* `Work.GenusZero.Rigid.isConstant_of_genus_zero` — every map from a genus-zero curve with a
  rational point to an abelian variety is constant, and `Work.GenusZero.existsUnique_const_of_genus_zero`
  its `∃!` form;
* `Work.GenusZero.Albanese.exists_unique_ofCurve_comp_of_genus_zero` — the universal property of
  the trivial Jacobian;
* `Work.GenusZero.sumOfPoints_eq_of_genus_zero` — the sum of the images of a multiset of points
  at genus zero depends only on the number of points;
* `Work.GenusZero.PointSum.sumMapOfModel_eq_of_deg_eq_of_genus_zero` — the sum map at genus zero
  is constant in the degree;
* `Work.GenusZero.Over.exists_unique_comp_toUnit_ofOver` — the universal property of the trivial
  Jacobian for a curve given at the `Over (Spec k)` level;
* `Work.GenusZero.jacPkg_of_genus_zero` / `Work.GenusZero.jacPkgExists_of_genus_zero` — the
  Jacobian package with `J = 𝟙_` (`Trivial.lean`).

The vocabulary of the area (base change of points, the unique map to the terminal object, the
divisor of a point) lives in `Basic.lean` and `PointDiv.lean`; `NOTES.md` in this directory
records the design and the interface for callers.
-/
