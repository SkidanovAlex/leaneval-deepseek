/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Area DS — Galois descent: everything

Convenience aggregator: importing this module gives the whole algebra half of area DS, namely

* the vocabulary and basic API of semilinear Galois actions (`Basic`, `GaloisBasis`, `Invariants`);
* Speiser's result for modules and for algebras (`moduleSpeiser`, `speiser`) and the resulting
  equivalences (`SpeiserEquiv`);
* the affine case (`baseChange_fixed_iff`, `affine_desc`);
* the scheme-theoretic quotient by the base change (`Scheme`, `baseChange_isQuotient`) and the
  descent of `Γ`-invariant morphisms (`desc_of_invariant`).

See `Submission/Work/Descent/NOTES.md` for the design and the exact names.
-/
import Submission.Work.Descent.Basic
import Submission.Work.Descent.GaloisBasis
import Submission.Work.Descent.Invariants
import Submission.Work.Descent.exists_coeffs_left
import Submission.Work.Descent.exists_coeffs_right
import Submission.Work.Descent.dedekind_module
import Submission.Work.Descent.exists_trace_one
import Submission.Work.Descent.moduleSpeiser
import Submission.Work.Descent.speiser
import Submission.Work.Descent.SpeiserEquiv
import Submission.Work.Descent.baseChange_fixed_iff
import Submission.Work.Descent.affine_desc
import Submission.Work.Descent.Scheme
import Submission.Work.Descent.baseChange_isQuotient
import Submission.Work.Descent.desc_of_invariant

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

