/-
# Tools for reduced words in a free group

This file collects two elementary combinatorial gadgets used in the proof that `K[F(X)]` is a
domain (equivalently: that a free group has the unique product property), namely the inverse of an
alphabet letter and the length of the longest common prefix of two lists.

The mathematical content is that the Cayley graph of a free group is a tree, whose geodesics from
the identity are exactly the prefixes of reduced words; the quantitative form of this fact is the
formula `FreeGroup.norm (a⁻¹ * b) + 2 * lcpLen (toWord a) (toWord b) = norm a + norm b`.
-/
import Mathlib

set_option autoImplicit false

namespace Work.ORLyndon

/-- The inverse of an alphabet letter `(a, b)` of a free group, namely `(a, !b)`.

This is the function appearing in `FreeGroup.invRev`, bundled with a name. -/
def invSym {α : Type*} (x : α × Bool) : α × Bool := (x.1, !x.2)

@[simp] theorem invSym_fst {α : Type*} (x : α × Bool) : (invSym x).1 = x.1 := rfl

@[simp] theorem invSym_snd {α : Type*} (x : α × Bool) : (invSym x).2 = !x.2 := rfl

@[simp] theorem invSym_invSym {α : Type*} (x : α × Bool) : invSym (invSym x) = x := by
  cases x with
  | mk a b => cases b <;> rfl

theorem invSym_ne_self {α : Type*} (x : α × Bool) : invSym x ≠ x := by
  cases x with
  | mk a b => cases b <;> simp [invSym]

/-- The length of the longest common prefix of two lists. -/
def lcpLen {β : Type*} [DecidableEq β] : List β → List β → ℕ
  | [], _ => 0
  | _, [] => 0
  | a :: as, b :: bs => if a = b then 1 + lcpLen as bs else 0

@[simp] theorem lcpLen_nil_left {β : Type*} [DecidableEq β] (Z : List β) : lcpLen [] Z = 0 := rfl

@[simp] theorem lcpLen_nil_right {β : Type*} [DecidableEq β] (W : List β) : lcpLen W [] = 0 := by
  cases W <;> rfl

theorem lcpLen_cons_cons {β : Type*} [DecidableEq β] (a b : β) (as bs : List β) :
    lcpLen (a :: as) (b :: bs) = if a = b then 1 + lcpLen as bs else 0 := rfl

end Work.ORLyndon
