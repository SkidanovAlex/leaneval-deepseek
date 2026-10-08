/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# AREA AUTL2 / Normalizer : the translation subgroup and the diagonal scalar

Vocabulary for the computation `N_{Sym(ℙ¹(F))}(PSL(2,F)) = PΓL(2,F)`:

* `Work.AUTL2.Normalizer.translHom`, `translSub`: the group `U = {x ↦ x + b} ≅ (F,+)`;
* `Work.AUTL2.Normalizer.smulPerm`: the permutation `x ↦ c·x` (`∞ ↦ ∞`), which lies in
  `pglImage F` (it is the image of the diagonal matrix `diag(c,1) ∈ GL(2,F)`).
-/
import Mathlib
import Submission.Work.DSTR.M110.Defs
import Submission.Work.DSTR.M110.Mobius
import Submission.Work.DSTR.M110.Stabilizer
import Submission.Work.AUTL2.Normalizer.Defs

open scoped MatrixGroups LinearAlgebra.Projectivization
open OnePoint

namespace Work.AUTL2.Normalizer

variable (F : Type*) [Field F] [DecidableEq F]

/-! ## The translation subgroup `U` -/


/-! ## The scalar `x ↦ c·x` as an element of `PGL(2,F)` -/


end Work.AUTL2.Normalizer
