/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# AREA AUTL2 : the Möbius action of `PSL(2,F)` on `ℙ¹(F)`

Computational layer of the area `Submission/Work/AUTL2/`:

* `Work.AUTL2.transl`: `x ↦ x + b`, `∞ ↦ ∞`, an element of `pslImage F`;
* `Work.AUTL2.dil`: `x ↦ a²x`, `∞ ↦ ∞`, an element of `pslImage F`;
* `Work.AUTL2.weylEl`: `x ↦ -1/x`, an element of `pslImage F`;
* `element_fixing_infty`: an element of `pslImage F` fixing `∞` is affine `x ↦ a²x + b`
  (the Borel subgroup of `PSL(2,F)`);
* `perm_three_transitive`: `PGL(2,F)` is 3-transitive on `ℙ¹(F)`.
-/
import Mathlib
import Submission.Work.DSTR.M110.Defs
import Submission.Work.AUTL2.Mobius

open scoped MatrixGroups LinearAlgebra.Projectivization
open OnePoint

namespace Work.AUTL2

variable (F : Type*) [Field F] [DecidableEq F]


/-- The entries of the matrices used below, in a form `simp` can consume. -/
private lemma unipotent_entry (b : F) :
    ((unipotentMat F b : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = !![1, b; 0, 1] := rfl
private lemma diag_entry (a : Fˣ) :
    ((diagMat F a : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = !![↑a, 0; 0, ↑a⁻¹] := rfl
private lemma weyl_entry :
    ((weylMat F : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = !![0, 1; -1, 0] := rfl


end Work.AUTL2
