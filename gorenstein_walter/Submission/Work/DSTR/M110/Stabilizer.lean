/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# AREA AUTL2 : the point stabilizers in `PSL(2,F)`

* `Work.AUTL2.element_fixing_infty`: an element of `pslImage F` fixing `∞` is affine
  `x ↦ a²x + b` (this is the Borel subgroup of `PSL(2,F)`);
* `Work.AUTL2.fixing_infty_zero`: an element of `pslImage F` fixing `∞` and `0` is a dilation
  `x ↦ a²x`;
* `Work.AUTL2.exists_pslImage_map_to_infty`: `pslImage F` is transitive on `ℙ¹(F)`.
-/
import Mathlib
import Submission.Work.DSTR.M110.Defs
import Submission.Work.DSTR.M110.Mobius
import Submission.Work.AUTL2.Stabilizer

open scoped MatrixGroups LinearAlgebra.Projectivization
open OnePoint

namespace Work.AUTL2

variable (F : Type*) [Field F] [DecidableEq F]


end Work.AUTL2
