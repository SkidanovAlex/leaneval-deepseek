/-
Copyright (c) 2024. All rights reserved.

# The two-step groups of Higman's table

Higman's Theorem 1 describes every Suzuki 2-group as one of `A(n,θ)`, `B(n,θ,ε)`, `C(n,ε)`,
`D(n,θ,ε)`.  All four are of the following shape: an extension of an elementary abelian
`2`-group `Z` by an elementary abelian `2`-group `A` with a biadditive cocycle `b : A → A → Z`,
the group law being
`(a,z) * (a',z') = (a + a', z + z' + b a a')`.

This file builds that uniform construction and proves it is a group (the `Group` instance is
`TwoStep.instGroup`).  The four families are defined in `Submission.Work.Higman.Family`.
-/

import Submission.Work.Higman.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Work.Higman

/-- An additive commutative group of exponent two (`z + z = 0`). -/
class AddExpTwo (Z : Type*) [AddCommGroup Z] : Prop where
  /-- Every element is its own negative. -/
  add_self : ∀ z : Z, z + z = 0

instance instAddExpTwoField (F : Type*) [Field F] [CharP F 2] : AddExpTwo F where
  add_self z := CharTwo.add_self_eq_zero z

instance instAddExpTwoProd (A B : Type*) [AddCommGroup A] [AddCommGroup B] [AddExpTwo A]
    [AddExpTwo B] : AddExpTwo (A × B) where
  add_self z := by
    have h1 : z.1 + z.1 = 0 := AddExpTwo.add_self z.1
    have h2 : z.2 + z.2 = 0 := AddExpTwo.add_self z.2
    exact Prod.ext h1 h2

theorem AddExpTwo.add_add_add_add {Z : Type*} [AddCommGroup Z] [AddExpTwo Z] (a b : Z) :
    a + b + a + b = 0 := by
  rw [show a + b + a + b = (a + b) + (a + b) from by abel, AddExpTwo.add_self]

/-- The cocycle `b` is additive in each variable.

Declared as a `class` (rather than a `structure` in `Prop`) so that it can be used as an
instance argument of the `Group (TwoStep A Z b)` instance below. -/
class Biadd {A Z : Type*} [AddCommGroup A] [AddCommGroup Z] (b : A → A → Z) : Prop where
  /-- Additivity in the first variable. -/
  add_left : ∀ a a' c, b (a + a') c = b a c + b a' c
  /-- Additivity in the second variable. -/
  add_right : ∀ a c c', b a (c + c') = b a c + b a c'

namespace Biadd

variable {A Z : Type*} [AddCommGroup A] [AddCommGroup Z] {b : A → A → Z} [Biadd b]

theorem zero_left (a : A) : b 0 a = 0 := by
  have h : b 0 a = b 0 a + b 0 a := by simpa using Biadd.add_left (b := b) (0 : A) (0 : A) a
  exact add_left_cancel (by rw [add_zero]; exact h.symm)

theorem zero_right (a : A) : b a 0 = 0 := by
  have h : b a 0 = b a 0 + b a 0 := by simpa using Biadd.add_right (b := b) a (0 : A) (0 : A)
  exact add_left_cancel (by rw [add_zero]; exact h.symm)

end Biadd

/-- The underlying type of the two-step group with cocycle `b`. -/
structure TwoStep (A : Type*) (Z : Type*) [AddCommGroup A] [AddCommGroup Z] (b : A → A → Z)
    where
  /-- The `A`-coordinate. -/
  fst : A
  /-- The `Z`-coordinate. -/
  snd : Z

namespace TwoStep

variable {A Z : Type*} [AddCommGroup A] [AddCommGroup Z] {b : A → A → Z} [Biadd b]
  [AddExpTwo A] [AddExpTwo Z]

instance instMul : Mul (TwoStep A Z b) where
  mul x y := ⟨x.fst + y.fst, x.snd + y.snd + b x.fst y.fst⟩

instance instOne : One (TwoStep A Z b) where
  one := ⟨0, 0⟩

instance instInv : Inv (TwoStep A Z b) where
  inv x := ⟨x.fst, x.snd + b x.fst x.fst⟩

@[simp] theorem fst_mul (x y : TwoStep A Z b) : (x * y).fst = x.fst + y.fst := rfl

@[simp] theorem snd_mul (x y : TwoStep A Z b) :
    (x * y).snd = x.snd + y.snd + b x.fst y.fst := rfl

@[simp] theorem fst_one : (1 : TwoStep A Z b).fst = 0 := rfl

@[simp] theorem snd_one : (1 : TwoStep A Z b).snd = 0 := rfl

@[simp] theorem fst_inv (x : TwoStep A Z b) : x⁻¹.fst = x.fst := rfl

@[simp] theorem snd_inv (x : TwoStep A Z b) : x⁻¹.snd = x.snd + b x.fst x.fst := rfl

@[ext] theorem ext_iff {x y : TwoStep A Z b} (h1 : x.fst = y.fst) (h2 : x.snd = y.snd) : x = y := by
  cases x; cases y; simp_all

theorem mul_assoc' (x y z : TwoStep A Z b) : x * y * z = x * (y * z) := by
  ext <;> simp only [fst_mul, snd_mul, Biadd.add_left, Biadd.add_right] <;> abel

theorem one_mul' (x : TwoStep A Z b) : 1 * x = x := by
  ext
  · simp
  · simp only [snd_mul, snd_one, fst_one, zero_add]
    rw [Biadd.zero_left (b := b) x.fst, add_zero]

theorem inv_mul_cancel' (x : TwoStep A Z b) : x⁻¹ * x = 1 := by
  ext
  · simpa using AddExpTwo.add_self x.fst
  · simp only [fst_inv, snd_inv, fst_mul, snd_mul, fst_one, snd_one]
    exact AddExpTwo.add_add_add_add x.snd (b x.fst x.fst)

instance instGroup : Group (TwoStep A Z b) :=
  Group.ofLeftAxioms mul_assoc' one_mul' inv_mul_cancel'

/-- The underlying type of `TwoStep A Z b` is `A × Z`. -/
def toProd : TwoStep A Z b ≃ A × Z where
  toFun x := (x.fst, x.snd)
  invFun p := ⟨p.1, p.2⟩
  left_inv x := by cases x; rfl
  right_inv p := by cases p; rfl

instance instFinite [Finite A] [Finite Z] : Finite (TwoStep A Z b) :=
  Finite.of_injective (fun x : TwoStep A Z b => (x.fst, x.snd)) (by
    intro x y h
    cases x with
    | mk x1 x2 =>
      cases y with
      | mk y1 y2 =>
        simp only [Prod.mk.injEq] at h
        rw [h.1, h.2])

theorem card_eq [Finite A] [Finite Z] :
    Nat.card (TwoStep A Z b) = Nat.card A * Nat.card Z :=
  (Nat.card_congr toProd).trans (Nat.card_prod A Z)

/-- Squaring in the two-step group is given by the diagonal of the cocycle. -/
theorem sq_eq (x : TwoStep A Z b) : x ^ 2 = ⟨0, b x.fst x.fst⟩ := by
  rw [pow_two]
  ext
  · simp [AddExpTwo.add_self]
  · simp only [snd_mul]
    rw [AddExpTwo.add_self, zero_add]

theorem sq_eq_one_iff (x : TwoStep A Z b) : x ^ 2 = 1 ↔ b x.fst x.fst = 0 := by
  rw [sq_eq]
  constructor
  · intro h
    have := congrArg (fun y : TwoStep A Z b => y.snd) h
    simpa using this
  · intro h
    ext
    · rfl
    · simpa using h

/-- An element of the two-step group is central exactly when the cocycle is symmetric at it. -/
theorem mem_center_iff (x : TwoStep A Z b) :
    x ∈ Subgroup.center (TwoStep A Z b) ↔ ∀ y : A, b x.fst y = b y x.fst := by
  rw [Subgroup.mem_center_iff]
  constructor
  · intro h y
    have h1 := congrArg (fun t : TwoStep A Z b => t.snd) (h ⟨y, 0⟩)
    rw [snd_mul, snd_mul] at h1
    simp only [fst_one, snd_one, zero_add, add_zero] at h1
    exact (add_left_cancel h1).symm
  · intro h y
    ext
    · simp only [fst_mul]; abel
    · simp only [snd_mul]
      rw [h y.fst]; abel

/-- `{(0,z)}`, the subgroup of elements with trivial `A`-coordinate (it is the centre of the
models of types `A`, `B`, `C`, `D`). -/
def kerFst : Subgroup (TwoStep A Z b) where
  carrier := {x | x.fst = 0}
  one_mem' := rfl
  mul_mem' := by
    intro x y hx hy
    show (x * y).fst = 0
    rw [fst_mul, hx, hy, zero_add]
  inv_mem' := by
    intro x hx
    show x⁻¹.fst = 0
    rw [fst_inv]
    exact hx

@[simp] theorem mem_kerFst {x : TwoStep A Z b} : x ∈ kerFst ↔ x.fst = 0 := Iff.rfl

theorem kerFst_le_center : kerFst ≤ Subgroup.center (TwoStep A Z b) := by
  intro x hx
  rw [mem_center_iff]
  intro y
  rw [mem_kerFst] at hx
  rw [hx]
  simp only [Biadd.zero_left, Biadd.zero_right]

end TwoStep

end Work.Higman
