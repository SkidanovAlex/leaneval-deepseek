import Mathlib
import Submission.Work.SSGRoute.prop5.magnusLieDefs
import Submission.Work.SSGRoute.prop5.witt.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Bracket monomials and the Lie span

The `ℤ`-span of the commutator monomials attached to binary trees of a fixed size.  This is the
"Lie part" of the degree-`j` component of the free associative algebra, and the main object
compared with `nestedSpan` and `lyndonSpan` in `nested_eq_lyndon_span`.
-/

noncomputable section

namespace Work.SSGRoute.prop5

variable {X : Type*}

/-- The commutator monomial in `FreeAssoc X` attached to a binary tree. -/
def brkMon (X : Type*) : Magma X → FreeAssoc X
  | .gen x => wordEl [x]
  | .mul a b => brkMon X a * brkMon X b - brkMon X b * brkMon X a

@[simp] theorem brkMon_gen (X : Type*) (x : X) :
    brkMon X (Magma.gen x) = wordEl [x] := rfl

@[simp] theorem brkMon_mul (X : Type*) (a b : Magma X) :
    brkMon X (Magma.mul a b) = brkMon X a * brkMon X b - brkMon X b * brkMon X a := rfl

/-- The **Lie span**: the `ℤ`-span of the bracket monomials of degree `j`. -/
def lieSpan (X : Type*) (j : ℕ) : Submodule ℤ (FreeAssoc X) :=
  Submodule.span ℤ {a : FreeAssoc X | ∃ c : Magma X, Magma.size c = j ∧ a = brkMon X c}

end Work.SSGRoute.prop5
