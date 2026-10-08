/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# `[PGL(2,q) : PSL(2,q)] = 2` in the `M110` copy of the `ℙ¹` model

Port of `Submission/Work/AUTL2/Aut/pglIndex.lean` into the `DSTR/M110` tree (which is the
copy of the `ℙ¹` model this area imports), so that the DS10a development can use

* `Work.AUTL2.Aut.mem_pslImage_iff_isSquare_det` :
  `pglHom F (mk B) ∈ pslImage F ↔ IsSquare B.det`
* `Work.AUTL2.Aut.pglIndex` : `(pslImage F).relIndex (pglImage F) = 2`
* `Work.AUTL2.Aut.isSquare_units_or`

without importing the `AUTL2` copy of the vocabulary (which would clash).
-/
import Mathlib
import Submission.Work.DSTR.M110.Defs
import Submission.Work.DSTR.M110.Normalizer.Defs
import Submission.Work.DSTR.M110.Aut.pglHomInjective
import Submission.Work.DSTR.M110.Aut.squareDichotomy
import Submission.Work.AUTL2.Aut.pglIndex

open scoped MatrixGroups LinearAlgebra.Projectivization
open OnePoint

namespace Work.AUTL2.Aut

open Work.AUTL2

variable (F : Type*) [Field F] [DecidableEq F]


end Work.AUTL2.Aut
