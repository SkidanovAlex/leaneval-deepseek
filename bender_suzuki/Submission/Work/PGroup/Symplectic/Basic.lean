import Mathlib
import Submission.Work.PGroup.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `p`-groups of symplectic type (P. Hall's theorem, FT 3.5)

A finite `p`-group `P` is said to be *of symplectic type* when every abelian characteristic
subgroup of `P` is cyclic (Gorenstein, *Finite Groups*, §5.4, condition `dc(P) = 1`).  By a
theorem of P. Hall (Gorenstein Theorem 5.4.9; Feit–Thompson 3.5) such a group is the central
product of an extraspecial group and a group which, for odd `p`, is cyclic.

This file fixes the vocabulary and records the first elementary facts.
-/

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open scoped Classical Pointwise
open Subgroup

noncomputable section

namespace Work.PGroup

variable {X : Type*} [Group X]

/-- **Groups of symplectic type.**  Every abelian characteristic subgroup of `X` is cyclic. -/
def AllAbelianCharCyclic (X : Type*) [Group X] : Prop :=
  ∀ A : Subgroup X, A.Characteristic → IsMulCommutative A → ∃ a : X, A = Subgroup.zpowers a

theorem AllAbelianCharCyclic.eq_zpowers {h : AllAbelianCharCyclic X} {A : Subgroup X}
    (hA : A.Characteristic) (hab : IsMulCommutative A) : ∃ a : X, A = Subgroup.zpowers a :=
  h A hA hab

/-- The centre of a group of symplectic type is cyclic. -/
theorem center_eq_zpowers_of_allAbelianCharCyclic (h : AllAbelianCharCyclic X) :
    ∃ a : X, Subgroup.center X = Subgroup.zpowers a :=
  h (Subgroup.center X) Subgroup.centerCharacteristic
    (isMulCommutative_iff.mpr fun x y => Subtype.ext (Subgroup.mem_center_iff.mp y.2 x))

end Work.PGroup
