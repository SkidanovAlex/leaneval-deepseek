/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The universal rational `U`-semiring `Rat(U)` (the term model)

[JZLA20, §4.2] constructs the universal rational `U`-semiring `Rat(U)` as an inductive closure of
the group `U` under sums, products and the rational operation `⋄`; its defining property
([JZLA20, Lemma 4.2]) is that for every rational `U`-semiring `A` there is a *unique* morphism of
rational `U`-semirings `Rat(U) → A` (together with its extension to `Rat(U) ∪ {0}`).

This file builds a concrete model of that universal object.  `RTerm U` is the absolutely free
algebra for the signature of rational `U`-semirings (constants `0`, `1`, binary `+`, `*`, unary
`⋄`, and the two `U`-actions).  A term is interpreted in every rational `U`-semiring `A` by
`RTerm.eval`, and `RatU U` is the quotient of `RTerm U` by "equal in every rational
`U`-semiring".  This quotient is the initial rational `U`-semiring:

* `RatU.instSemiring` : the semiring structure (the quotient of the free term algebra);
* `RatU.rational` : the rational `U`-semiring structure;
* `RatU.lift_existsUnique` : for every rational `U`-semiring `A` there is a unique morphism
  `RatU U →+* A` commuting with `⋄` and the two `U`-actions.
-/
import Mathlib
import Submission.Work.ORHughesFree.JZLA20

set_option autoImplicit false

universe u

namespace Work.ORHughesFree

/-- The absolutely free algebra (term model) for the signature of rational `U`-semirings: the
constants `0`, `1`, the binary operations `+`, `*`, the unary rational operation `⋄`, and the two
`U`-actions `u · _` and `_ · u`. -/
inductive RTerm (U : Type) where
  /-- the constant `0` -/
  | z : RTerm U
  /-- the constant `1` -/
  | o : RTerm U
  /-- the sum of two terms -/
  | add : RTerm U → RTerm U → RTerm U
  /-- the product of two terms -/
  | mul : RTerm U → RTerm U → RTerm U
  /-- the rational operation `⋄` -/
  | rat : RTerm U → RTerm U
  /-- the left `U`-action `u · _` -/
  | smulL : U → RTerm U → RTerm U
  /-- the right `U`-action `_ · u` -/
  | smulR : U → RTerm U → RTerm U

namespace RTerm

variable {U : Type}

/-- The value of a term in a rational `U`-semiring `A`. -/
def eval [Group U] (A : Type) [Semiring A] (rA : RationalUSemiring U A) : RTerm U → A
  | .z => 0
  | .o => 1
  | .add a b => eval A rA a + eval A rA b
  | .mul a b => eval A rA a * eval A rA b
  | .rat a => rA.ratOp (eval A rA a)
  | .smulL u a => rA.smul u (eval A rA a)
  | .smulR u a => rA.smulRight (eval A rA a) u

variable [Group U]

/-- Two terms are *equivalent* if they have the same value in every rational `U`-semiring. -/
def Rel (a b : RTerm U) : Prop :=
  ∀ (A : Type) [Semiring A] (rA : RationalUSemiring U A), eval A rA a = eval A rA b

theorem rel_refl (a : RTerm U) : Rel a a := fun A i rA => rfl

theorem Rel.symm {a b : RTerm U} (h : Rel a b) : Rel b a := fun A i rA => (h A rA).symm

theorem Rel.trans {a b c : RTerm U} (h1 : Rel a b) (h2 : Rel b c) : Rel a c :=
  fun A i rA => (h1 A rA).trans (h2 A rA)

theorem Rel.add {a a' b b' : RTerm U} (h1 : Rel a a') (h2 : Rel b b') :
    Rel (RTerm.add a b) (RTerm.add a' b') := by
  intro A i rA
  show eval A rA a + eval A rA b = eval A rA a' + eval A rA b'
  rw [h1 A rA, h2 A rA]

theorem Rel.mul {a a' b b' : RTerm U} (h1 : Rel a a') (h2 : Rel b b') :
    Rel (RTerm.mul a b) (RTerm.mul a' b') := by
  intro A i rA
  show eval A rA a * eval A rA b = eval A rA a' * eval A rA b'
  rw [h1 A rA, h2 A rA]

theorem Rel.rat {a a' : RTerm U} (h : Rel a a') : Rel (RTerm.rat a) (RTerm.rat a') := by
  intro A i rA
  show rA.ratOp (eval A rA a) = rA.ratOp (eval A rA a')
  rw [h A rA]

theorem Rel.smulL (u : U) {a a' : RTerm U} (h : Rel a a') :
    Rel (RTerm.smulL u a) (RTerm.smulL u a') := by
  intro A i rA
  show rA.smul u (eval A rA a) = rA.smul u (eval A rA a')
  rw [h A rA]

theorem Rel.smulR (u : U) {a a' : RTerm U} (h : Rel a a') :
    Rel (RTerm.smulR u a) (RTerm.smulR u a') := by
  intro A i rA
  show rA.smulRight (eval A rA a) u = rA.smulRight (eval A rA a') u
  rw [h A rA]

/-- The setoid of terms with the same value in every rational `U`-semiring. -/
def setoid (U : Type) [Group U] : Setoid (RTerm U) where
  r := Rel
  iseqv := ⟨rel_refl, fun h => h.symm, fun h1 h2 => h1.trans h2⟩

end RTerm

/-- **A model of the universal rational `U`-semiring `Rat(U)`**: the quotient of the free
term algebra by the relation "equal in every rational `U`-semiring". -/
def RatU (U : Type) [Group U] : Type := Quotient (RTerm.setoid U)

namespace RatU

variable {U : Type} [Group U]

/-- The class of a term in `RatU U`. -/
def mk (t : RTerm U) : RatU U := Quotient.mk'' t

instance : Zero (RatU U) := ⟨Quotient.mk'' RTerm.z⟩
instance : One (RatU U) := ⟨Quotient.mk'' RTerm.o⟩
instance : Add (RatU U) :=
  ⟨Quotient.map₂ RTerm.add (fun a₁ a₂ h₁ b₁ b₂ h₂ => RTerm.Rel.add h₁ h₂)⟩
instance : Mul (RatU U) :=
  ⟨Quotient.map₂ RTerm.mul (fun a₁ a₂ h₁ b₁ b₂ h₂ => RTerm.Rel.mul h₁ h₂)⟩

theorem mk_zero : (mk RTerm.z : RatU U) = 0 := rfl

theorem mk_one : (mk RTerm.o : RatU U) = 1 := rfl

theorem mk_add (a b : RTerm U) : (mk (RTerm.add a b) : RatU U) = mk a + mk b := rfl

theorem mk_mul (a b : RTerm U) : (mk (RTerm.mul a b) : RatU U) = mk a * mk b := rfl

instance instSemiring : Semiring (RatU U) where
  add_assoc := by
    rintro ⟨a⟩ ⟨b⟩ ⟨c⟩
    refine Quotient.sound ?_
    intro A i rA
    show RTerm.eval A rA a + RTerm.eval A rA b + RTerm.eval A rA c =
      RTerm.eval A rA a + (RTerm.eval A rA b + RTerm.eval A rA c)
    rw [add_assoc]
  zero_add := by
    rintro ⟨a⟩
    refine Quotient.sound ?_
    intro A i rA
    show (0 : A) + RTerm.eval A rA a = RTerm.eval A rA a
    rw [zero_add]
  add_zero := by
    rintro ⟨a⟩
    refine Quotient.sound ?_
    intro A i rA
    show RTerm.eval A rA a + 0 = RTerm.eval A rA a
    rw [add_zero]
  add_comm := by
    rintro ⟨a⟩ ⟨b⟩
    refine Quotient.sound ?_
    intro A i rA
    show RTerm.eval A rA a + RTerm.eval A rA b = RTerm.eval A rA b + RTerm.eval A rA a
    rw [add_comm]
  nsmul := nsmulRec
  nsmul_zero := fun x => rfl
  nsmul_succ := fun n x => rfl
  mul_assoc := by
    rintro ⟨a⟩ ⟨b⟩ ⟨c⟩
    refine Quotient.sound ?_
    intro A i rA
    show RTerm.eval A rA a * RTerm.eval A rA b * RTerm.eval A rA c =
      RTerm.eval A rA a * (RTerm.eval A rA b * RTerm.eval A rA c)
    rw [mul_assoc]
  one_mul := by
    rintro ⟨a⟩
    refine Quotient.sound ?_
    intro A i rA
    show (1 : A) * RTerm.eval A rA a = RTerm.eval A rA a
    rw [one_mul]
  mul_one := by
    rintro ⟨a⟩
    refine Quotient.sound ?_
    intro A i rA
    show RTerm.eval A rA a * 1 = RTerm.eval A rA a
    rw [mul_one]
  zero_mul := by
    rintro ⟨a⟩
    refine Quotient.sound ?_
    intro A i rA
    show (0 : A) * RTerm.eval A rA a = 0
    rw [zero_mul]
  mul_zero := by
    rintro ⟨a⟩
    refine Quotient.sound ?_
    intro A i rA
    show RTerm.eval A rA a * 0 = 0
    rw [mul_zero]
  left_distrib := by
    rintro ⟨a⟩ ⟨b⟩ ⟨c⟩
    refine Quotient.sound ?_
    intro A i rA
    show RTerm.eval A rA a * (RTerm.eval A rA b + RTerm.eval A rA c) =
      RTerm.eval A rA a * RTerm.eval A rA b + RTerm.eval A rA a * RTerm.eval A rA c
    rw [left_distrib]
  right_distrib := by
    rintro ⟨a⟩ ⟨b⟩ ⟨c⟩
    refine Quotient.sound ?_
    intro A i rA
    show (RTerm.eval A rA a + RTerm.eval A rA b) * RTerm.eval A rA c =
      RTerm.eval A rA a * RTerm.eval A rA c + RTerm.eval A rA b * RTerm.eval A rA c
    rw [right_distrib]

/-- The rational operation on `RatU U`. -/
noncomputable def ratOp : RatU U → RatU U :=
  Quotient.map RTerm.rat (fun _ _ h => RTerm.Rel.rat h)

/-- The left `U`-action on `RatU U`. -/
noncomputable def smul (u : U) : RatU U → RatU U :=
  Quotient.map (RTerm.smulL u) (fun _ _ h => RTerm.Rel.smulL u h)

/-- The right `U`-action on `RatU U`. -/
noncomputable def smulRight (x : RatU U) (u : U) : RatU U :=
  Quotient.map (RTerm.smulR u) (fun _ _ h => RTerm.Rel.smulR u h) x

theorem mk_rat (a : RTerm U) : (mk (RTerm.rat a) : RatU U) = ratOp (mk a) := rfl

theorem mk_smulL (u : U) (a : RTerm U) : (mk (RTerm.smulL u a) : RatU U) = smul u (mk a) := rfl

theorem mk_smulR (u : U) (a : RTerm U) : (mk (RTerm.smulR u a) : RatU U) = smulRight (mk a) u :=
  rfl

/-- **The rational `U`-semiring structure on `Rat(U)`** ([JZLA20, §4.2]). -/
noncomputable def rational : RationalUSemiring U (RatU U) where
  ratOp := ratOp
  smul := smul
  smulRight := smulRight
  smul_eq_mul := by
    rintro u ⟨a⟩
    refine Quotient.sound ?_
    intro A i rA
    show rA.smul u (RTerm.eval A rA a) = rA.smul u 1 * RTerm.eval A rA a
    rw [rA.smul_eq_mul]
  smulRight_eq_mul := by
    rintro ⟨a⟩ u
    refine Quotient.sound ?_
    intro A i rA
    show rA.smulRight (RTerm.eval A rA a) u = RTerm.eval A rA a * rA.smulRight 1 u
    rw [rA.smulRight_eq_mul]
  smul_mul := by
    rintro u v
    refine Quotient.sound ?_
    intro A i rA
    show rA.smul (u * v) 1 = rA.smul u 1 * rA.smul v 1
    rw [rA.smul_mul]
  smul_one_one := by
    refine Quotient.sound ?_
    intro A i rA
    show rA.smul 1 1 = (1 : A)
    rw [rA.smul_one_one]
  smulRight_one_one := by
    refine Quotient.sound ?_
    intro A i rA
    show rA.smulRight 1 1 = (1 : A)
    rw [rA.smulRight_one_one]
  smulRight_one := by
    intro u
    refine Quotient.sound ?_
    intro A i rA
    show rA.smulRight 1 u = rA.smul u 1
    rw [rA.smulRight_one]
  rat_smul := by
    rintro u v ⟨a⟩
    refine Quotient.sound ?_
    intro A i rA
    show rA.ratOp (rA.smul u (rA.smulRight (RTerm.eval A rA a) v)) =
      rA.smulRight (rA.smul v⁻¹ (rA.ratOp (RTerm.eval A rA a))) u⁻¹
    rw [rA.rat_smul]
  ratOp_zero := by
    change RatU.ratOp (RatU.mk RTerm.z) = RatU.mk RTerm.z
    refine Quotient.sound ?_
    intro A i rA
    exact rA.ratOp_zero

/-- **`⋄ 0 = 0` in `Rat(U)`.**  This is the difference with the *naive* total model of
`Rat(U)`: by `RationalUSemiring.ratOp_zero` the rational operation is required to fix `0`, so the
quotient `RatU U` identifies `⋄ 0` with `0` (as in the paper, where `⋄ 0` is not defined at all),
instead of adjoining the degenerate element `⋄ 0`. -/
theorem ratOp_zero : RatU.ratOp (0 : RatU U) = 0 :=
  (rational (U := U)).ratOp_zero

/-- `RatU.ratOp` (the model's own rational operation) is the `ratOp` field of the structure
`RatU.rational` — they are the same function, definitionally. -/
theorem ratOp_eq_rational (z : RatU U) : RatU.ratOp z = (rational (U := U)).ratOp z := rfl

/-- The universal morphism of rational `U`-semirings from `Rat(U)` to a rational `U`-semiring
`A` ([JZLA20, Lemma 4.2]). -/
noncomputable def lift (A : Type) [Semiring A] (rA : RationalUSemiring U A) : RatU U →+* A where
  toFun := Quotient.lift (RTerm.eval A rA) (fun _ _ h => h A rA)
  map_one' := rfl
  map_zero' := rfl
  map_mul' := by rintro ⟨a⟩ ⟨b⟩; rfl
  map_add' := by rintro ⟨a⟩ ⟨b⟩; rfl

theorem lift_apply (A : Type) [Semiring A] (rA : RationalUSemiring U A) (t : RTerm U) :
    lift A rA (mk t) = RTerm.eval A rA t := rfl

/-- `RatU.lift` is a morphism of rational `U`-semirings. -/
theorem lift_isHom (A : Type) [Semiring A] (rA : RationalUSemiring U A) :
    IsRationalUSemiringHom rational rA (lift A rA) where
  map_rat := by rintro ⟨a⟩; rfl
  map_smul := by rintro u ⟨a⟩; rfl
  map_smulRight := by rintro ⟨a⟩ u; rfl

/-- Uniqueness of the universal morphism: every morphism of rational `U`-semirings
`Rat(U) → A` is `RatU.lift A rA`. -/
theorem lift_unique (A : Type) [Semiring A] (rA : RationalUSemiring U A) (g : RatU U →+* A)
    (hg : IsRationalUSemiringHom rational rA g) : g = lift A rA := by
  ext x
  refine Quotient.inductionOn x ?_
  intro t
  show g (mk t) = lift A rA (mk t)
  have key : ∀ t : RTerm U, g (mk t) = RTerm.eval A rA t := by
    intro t
    induction t with
    | z => exact g.map_zero
    | o => exact g.map_one
    | add a b iha ihb => rw [mk_add, map_add, iha, ihb]; rfl
    | mul a b iha ihb => rw [mk_mul, map_mul, iha, ihb]; rfl
    | rat a iha =>
      show g (rational.ratOp (mk a)) = RTerm.eval A rA (RTerm.rat a)
      rw [hg.map_rat, iha,
        show rA.ratOp (RTerm.eval A rA a) = RTerm.eval A rA (RTerm.rat a) from rfl]
    | smulL u a iha =>
      show g (rational.smul u (mk a)) = RTerm.eval A rA (RTerm.smulL u a)
      rw [hg.map_smul, iha,
        show rA.smul u (RTerm.eval A rA a) = RTerm.eval A rA (RTerm.smulL u a) from rfl]
    | smulR u a iha =>
      show g (rational.smulRight (mk a) u) = RTerm.eval A rA (RTerm.smulR u a)
      rw [hg.map_smulRight, iha,
        show rA.smulRight (RTerm.eval A rA a) u = RTerm.eval A rA (RTerm.smulR u a) from rfl]
  rw [key t, lift_apply]

/-- **[JZLA20, Lemma 4.2]**: for every rational `U`-semiring `A` there is a *unique* morphism of
rational `U`-semirings `Rat(U) → A`.  Thus `RatU U` is the initial rational `U`-semiring. -/
theorem lift_existsUnique (A : Type) [Semiring A] (rA : RationalUSemiring U A) :
    ∃! f : RatU U →+* A, IsRationalUSemiringHom rational rA f :=
  ⟨lift A rA, lift_isHom A rA, fun g hg => lift_unique A rA g hg⟩

end RatU

end Work.ORHughesFree
