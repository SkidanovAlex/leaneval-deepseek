/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# AREA AUTL2 / Normalizer : `N(PSL(2,q)) = PΓL(2,q)`

The main computation of step A3 of the AUTL2 design:

* `Work.AUTL2.Normalizer.le_pgammaL` : every permutation of `ℙ¹(F)`, `F = GF(p^k)` (`p` odd),
  normalizing the image of `PSL(2,F)` lies in `PΓL(2,F)`.

The proof is the classical one: a normalizing permutation `π` is first moved (by an element of
`PSL`) to a permutation `π₁` fixing `∞`, i.e. normalizing the Borel subgroup `B`.  Inside `B`
the translation subgroup `U = {x ↦ x + b}` is characterized by "no fixed point in `F`", hence is
`π₁`-invariant, and conjugation gives an additive bijection `s` of `(F,+)` with
`π₁ ∘ transl b = transl (s b) ∘ π₁`.  From this, `π₁` is affine, `π₁ x = c + s x`; conjugating the
diagonal elements `dil a` (fixed points `0,∞`) gives the square-linearity `s(a²x) = b² s x`, which
(using that every element of `F` is a difference of two squares, char `≠ 2`) makes
`σ := s / s 1` an automorphism of `F` and `s x = s 1 · σ x`.  Hence
`π₁ = transl c ∘ (x ↦ s 1 · x) ∘ galHom σ ∈ PΓL(2,F)`, and so is `π`.

The only two ingredients that are not elementary are supplied as separate lemmas:
`Work.AUTL2.Normalizer.mem_translSub_of_pslImage_of_fpf` (the fixed-point characterization of
translations) and `Work.AUTL2.Normalizer.exists_fieldAut_of_sq_smul` (the square-linearity ⟹
semi-linearity step).
-/
import Mathlib
import Submission.Work.DSTR.M110.Defs
import Submission.Work.DSTR.M110.Mobius
import Submission.Work.DSTR.M110.Stabilizer
import Submission.Work.DSTR.M110.Normalizer.Defs
import Submission.Work.DSTR.M110.Normalizer.mem_translSub_of_pslImage_of_fpf
import Submission.Work.DSTR.M110.Normalizer.exists_fieldAut_of_sq_smul
import Submission.Work.AUTL2.Normalizer.le_pgammaL

open scoped MatrixGroups LinearAlgebra.Projectivization
open OnePoint

namespace Work.AUTL2.Normalizer

variable (F : Type*) [Field F] [DecidableEq F]


end Work.AUTL2.Normalizer
