import Mathlib
import Submission.Work.L2F.Defs
import Submission.Work.L2F.Props.pgl_r_subgroup_cyclic

/-!
# Auxiliary notions for `odd_subgroup_cyclic_or_fixes_line`

This file collects the vocabulary used by `Submission/Work/L2F/Props/odd_subgroup_cyclic_or_fixes_line.lean`
and by the auxiliary lemmas delegated for it.

* `UnipotentMatrix g`: `g` is a non-scalar matrix which is a scalar plus a nonzero nilpotent,
  i.e. has a repeated eigenvalue (characteristic free formulation).
* `SemisimpleSL g`: `g` is non-scalar and its characteristic polynomial `X² - tr g · X + det g`
  is separable; concretely, in odd characteristic `(tr g)² ≠ 4 det g`, in characteristic `2`
  `tr g ≠ 0`.  (For `g ∈ SL(2,F)` this is exactly "`g` has two distinct eigenvalues in `F̄`".)
* `HasCommonEigenvectorSL H`: the subgroup `H ≤ SL(2,F)` fixes a line of `F²`, i.e. has a common
  eigenvector.
-/

open scoped MatrixGroups
open Matrix

namespace Work.L2F.Props

/-- `g` is unipotent: `g = λ·1 + N` with `N` nilpotent and `N ≠ 0` (equivalently: `g` has a
single eigenvalue in an algebraic closure, and is not a scalar).  Characteristic free. -/
def UnipotentMatrix {F : Type*} [Field F] (g : Matrix (Fin 2) (Fin 2) F) : Prop :=
  ∃ a : F, g - a • (1 : Matrix (Fin 2) (Fin 2) F) ≠ 0 ∧
    (g - a • (1 : Matrix (Fin 2) (Fin 2) F)) * (g - a • (1 : Matrix (Fin 2) (Fin 2) F)) = 0

/-- `g` is semisimple: `g` is not a scalar and its characteristic polynomial `X² - tr g · X + det g`
has distinct roots (i.e. is separable).  In odd characteristic this is `((tr g)² ≠ 4 det g)`;
in characteristic `2` it is `tr g ≠ 0`. -/
def SemisimpleSL {F : Type*} [Field F] (g : Matrix (Fin 2) (Fin 2) F) : Prop :=
  (∀ c : F, g ≠ c • (1 : Matrix (Fin 2) (Fin 2) F)) ∧
    ((2 : F) ≠ 0 ∧ g.trace ^ 2 - 4 * g.det ≠ 0 ∨ (2 : F) = 0 ∧ g.trace ≠ 0)

/-- The subgroup `H ≤ SL(2,F)` fixes a line of `F²` (has a common eigenvector). -/
def HasCommonEigenvectorSL {F : Type*} [Field F]
    (H : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)) : Prop :=
  ∃ v : Fin 2 → F, v ≠ 0 ∧ ∀ g ∈ H, ∃ c : F,
    (g : Matrix (Fin 2) (Fin 2) F) *ᵥ v = c • v

end Work.L2F.Props
