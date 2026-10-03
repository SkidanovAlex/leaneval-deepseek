/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The JZLA20 algebraic engine: interfaces for §4 and the statements of §5--§6

This file records, in Lean, the *interfaces* used by the JZLA20 algebraic engine
(A. Jaikin-Zapirain and D. López-Álvarez, arXiv:1810.12135):

* `RationalUSemiring U R` : the axioms of a rational `U`-semiring ([JZLA20, §4]);
* `RootedTrees` : the semiring of finite rooted trees with its `exp` operation and its well-order,
  carrying the exact content of [JZLA20, Lemma 4.1];
* `RatComplexity U` : the universal rational `U`-semiring `Rat(U)` with the complexity
  `Tree : Rat(U) → T`, carrying the content of [JZLA20, Lemma 4.2] and [JZLA20, Lemma 4.3];
* `IsStarRegularRank` : rank functions admitting an epic ∗-regular envelope ([JZLA20, §2.4]).

The key lemma [JZLA20, Proposition 5.1] and its carrier `Prop51Data` live in
`Submission.Work.ORHughesFree.Prop51` (they use the skew Laurent series ring
`Work.ORHughesFree.SkewLaurentSeries`).

The structures in this file are *hypothesis interfaces*: an inhabitant is a model of the
combinatorial machinery of [JZLA20, §4].  The statements of [JZLA20, Proposition 5.1] and
[JZLA20, Theorem 6.1] are recorded as `Prop`-valued definitions at the end.
-/
import Mathlib
import Submission.Work.ORHughesFree.SylvesterRank
import Submission.Work.ORHughesFree.StarRegular
import Submission.Work.ORHughesFree.Epic
import Submission.Work.ORHughesFree.DivisionClosure
import Submission.Work.ORHughesFree.NaturalExtension

set_option autoImplicit false

universe u

namespace Work.ORHughesFree

/-! ### Rational `U`-semirings ([JZLA20, §4]) -/

/-- A **rational `U`-semiring** ([JZLA20, §4]): an additive commutative monoid with an associative
multiplication and a unit, distributive over the addition, with a rational operation
`⋄ : R → R` and a compatible `U`-biset structure, subject to `(u r v)⋄ = v⁻¹ r⋄ u⁻¹`. -/
structure RationalUSemiring (U : Type u) [Group U] (R : Type u) [Semiring R] where
  /-- the rational operation `⋄` -/
  ratOp : R → R
  /-- the left action of `U` -/
  smul : U → R → R
  /-- the right action of `U` -/
  smulRight : R → U → R
  /-- the left action is multiplication by the image of `U` -/
  smul_eq_mul : ∀ (u : U) (r : R), smul u r = smul u 1 * r
  /-- the right action is multiplication by the image of `U` -/
  smulRight_eq_mul : ∀ (r : R) (u : U), smulRight r u = r * smulRight 1 u
  /-- the image of `U` is multiplicative -/
  smul_mul : ∀ (u v : U), smul (u * v) 1 = smul u 1 * smul v 1
  /-- the identity of `U` acts as the identity -/
  smul_one_one : smul 1 1 = 1
  /-- the identity of `U` acts as the identity -/
  smulRight_one_one : smulRight 1 1 = 1
  /-- the two `U`-actions agree on `1`: `1 · u = u · 1`.  In the paper `R` is a `U`-*biset* on
  which `U` acts *by multiplication* by its image in the units of `R`; this axiom says that the
  left and right actions give the same image of `u`, i.e. `smulRight 1 u = smul u 1`.  Together
  with `smulRight_eq_mul` it makes the right action an action (`smulRight (smulRight r v) u =
  smulRight r (v * u)`). -/
  smulRight_one : ∀ u : U, smulRight 1 u = smul u 1
  /-- the rational axiom `(u r v)⋄ = v⁻¹ r⋄ u⁻¹` -/
  rat_smul : ∀ (u v : U) (r : R), ratOp (smul u (smulRight r v)) =
    smulRight (smul v⁻¹ (ratOp r)) u⁻¹
  /-- `⋄ 0 = 0`.  This is **not** an axiom of [JZLA20, §4] — there `⋄` is defined only on the
  *non-zero* elements of `Rat(U) = ℕ[U ♮ X] ∖ {0}`, so that `⋄ 0` simply does not exist.  It is,
  however, satisfied by *every* geometric model appearing in the paper: for a division closure
  ([JZLA20, §4.3]) the rational operation is "inverse if invertible, and `0` otherwise", so
  `⋄ 0 = 0`; the same holds for the relative inverse of [JZLA20, §4.4].  Requiring it makes the
  initial object `RatU U` of `Rat/RTerm.lean` isomorphic to the paper's `Rat(U) ∪ {0}` — without
  it the universal object contains the spurious element `⋄ 0`, which is fixed by both `U`-actions
  and lies in `Rat(V)` for every subgroup `V`, and which refutes [DHS04, Theorem 5.7] (the
  existence of the *source* subgroup) in the naive total model; see `Rat/Geo/NOTES.md`. -/
  ratOp_zero : ratOp 0 = 0

/-- A **morphism of rational `U`-semirings** ([JZLA20, §4]): a ring homomorphism respecting the
rational operation and the two `U`-actions. -/
structure IsRationalUSemiringHom {U : Type u} [Group U] {R S : Type u} [Semiring R] [Semiring S]
    (rR : RationalUSemiring U R) (rS : RationalUSemiring U S) (f : R →+* S) : Prop where
  /-- `f` commutes with `⋄`. -/
  map_rat : ∀ x : R, f (rR.ratOp x) = rS.ratOp (f x)
  /-- `f` commutes with the left `U`-action. -/
  map_smul : ∀ (u : U) (x : R), f (rR.smul u x) = rS.smul u (f x)
  /-- `f` commutes with the right `U`-action. -/
  map_smulRight : ∀ (x : R) (u : U), f (rR.smulRight x u) = rS.smulRight (f x) u

/-! ### Finite rooted trees ([JZLA20, §4.1]) -/

/-- The **algebraic part** of the finite rooted trees of [JZLA20, §4.1]: the addition identifies
the roots, the multiplication is the product operation, `exp` is the tree with a single child, and
`fam` is the family of subtrees. -/
structure RootedTreeAlgebra (T : Type u) [AddCommMonoid T] [CommMonoid T] [Distrib T] where
  /-- the tree with a single child `X` (the "root extension") -/
  exp : T → T
  /-- the one-vertex tree is `0` and `exp 0 = 1` is the one-edge tree -/
  exp_zero : exp 0 = 1
  /-- `exp (X + Y) = exp X * exp Y` -/
  exp_add : ∀ x y : T, exp (x + y) = exp x * exp y
  /-- the family of subtrees of a tree -/
  fam : T → Multiset T
  /-- the family of `exp X` is the singleton `{X}` -/
  fam_exp : ∀ x : T, fam (exp x) = {x}
  /-- `X` is the sum of `exp Y` over its family -/
  sum_fam : ∀ x : T, ((fam x).map exp).sum = x
  /-- the product formula `X · Y = ∑_{X' ∈ fam X, Y' ∈ fam Y} exp (X' + Y')` -/
  mul_eq : ∀ x y : T, x * y =
    (((fam x).bind (fun a => (fam y).map (fun b => exp (a + b))))).sum

/-- The **finite rooted trees** of [JZLA20, §4.1]: their algebra (`RootedTreeAlgebra`) together
with the well-order of [DHS04, Lemma 3.3], satisfying [JZLA20, Lemma 4.1]. -/
structure RootedTrees (T : Type u) [AddCommMonoid T] [CommMonoid T] [Distrib T]
    extends RootedTreeAlgebra T where
  /-- the well-order of [DHS04, Lemma 3.3] -/
  le : T → T → Prop
  le_refl : ∀ x : T, le x x
  le_antisymm : ∀ {x y : T}, le x y → le y x → x = y
  le_trans : ∀ {x y z : T}, le x y → le y z → le x z
  le_total : ∀ x y : T, le x y ∨ le y x
  le_wf : WellFounded fun x y : T => le x y ∧ x ≠ y
  /-- [JZLA20, Lemma 4.1(i)] -/
  add_le_add : ∀ {a b c d : T}, le a b → le c d → le (a + c) (b + d)
  /-- [JZLA20, Lemma 4.1(i)] -/
  add_le_add_eq : ∀ {a b c d : T}, le a b → le c d → (a + c = b + d ↔ a = b ∧ c = d)
  /-- [JZLA20, Lemma 4.1(ii)] -/
  mul_le_mul : ∀ {a b c d : T}, le a b → le c d → le (a * c) (b * d)
  /-- [JZLA20, Lemma 4.1(ii)] -/
  mul_le_mul_eq : ∀ {a b c d : T}, a ≠ 0 → c ≠ 0 → le a b → le c d →
    (a * c = b * d ↔ a = b ∧ c = d)

/-! ### The universal rational `U`-semiring with its complexity ([JZLA20, §4.2]) -/

/-- A **model of the universal rational `U`-semiring with its complexity**: the data `Rat(U)` with
its rational `U`-semiring structure ([JZLA20, §4.2]) and the complexity map `Tree` with the
properties collected in [JZLA20, Lemma 4.3].  The remaining content of Lemma 4.2 -- that the
universal morphism `Φ_{H,A} : Rat(E × H) → D_{H,A}` of [JZLA20, §4.3] is surjective -- is
recorded separately, since it is relative to a target ring. -/
structure RatComplexity (U : Type u) [Group U] (T : Type u) [AddCommMonoid T] [CommMonoid T]
    [Distrib T] (R : Type u) [Semiring R] where
  /-- the tree semiring -/
  trees : RootedTrees T
  /-- the rational `U`-semiring structure on `Rat(U) ∪ {0}` -/
  rational : RationalUSemiring U R
  /-- the complexity of an element of `Rat(U) ∪ {0}`, i.e. the universal morphism to `T` -/
  tree : R → T
  /-- the extra zero of `Rat(U) ∪ {0}` maps to the one-vertex tree -/
  tree_zero : tree 0 = 0
  /-- [JZLA20, Lemma 4.3(ii)] -/
  tree_one : tree 1 = 1
  /-- [JZLA20, Lemma 4.3(iii)] -/
  tree_add : ∀ x y : R, tree (x + y) = tree x + tree y
  /-- [JZLA20, Lemma 4.3(v)] -/
  tree_mul : ∀ x y : R, tree (x * y) = tree x * tree y
  /-- [JZLA20, Lemma 4.3(xi)], for non-zero `x`.  The paper states this only for non-zero elements
  (there `Rat(U) = ℕ[U ♮ X] ∖ {0}` has no zero and `⋄ 0` is undefined); with the axiom
  `RationalUSemiring.ratOp_zero` (`⋄ 0 = 0`) the case `x = 0` reads `tree 0 = tree 0`, which is
  `tree_zero`.  The tree model of `Rat/TreeModel.lean` accordingly has `⋄ 0 = 0`. -/
  tree_rat : ∀ x : R, x ≠ 0 → tree (rational.ratOp x) = trees.exp (trees.exp (tree x))
  /-- [JZLA20, Lemma 4.3(iv)] -/
  tree_add_le : ∀ x y : R, trees.le (tree x) (tree x + tree y)
  /-- [JZLA20, Lemma 4.3(iv)] -/
  tree_add_eq : ∀ x y : R, y ≠ 0 → tree x + tree y ≠ tree x
  /-- [JZLA20, Lemma 4.3(vi)] -/
  tree_mul_le : ∀ x y : R, x ≠ 0 → y ≠ 0 → trees.le (tree x) (tree x * tree y)
  /-- [JZLA20, Lemma 4.3(vi)] -/
  tree_mul_eq_iff : ∀ x y : R, x ≠ 0 → y ≠ 0 → (tree x * tree y = tree x ↔ tree y = 1)
  /-- [JZLA20, Lemma 4.2]: `Rat(U) ∪ {0}` is the universal (initial) rational `U`-semiring. -/
  lift : ∀ (A : Type u) [Semiring A] (rA : RationalUSemiring U A),
    ∃! f : R →+* A, IsRationalUSemiringHom rational rA f

/-! ### ∗-regular rank functions ([JZLA20, §2.4]) -/

/-- A Sylvester rank function is **∗-regular** if it is the pullback along an epic ∗-homomorphism
from a positive definite ∗-regular ring carrying a faithful rank function ([JZLA20, §2.4], the class
`P*reg`). -/
def IsStarRegularRank {R : Type u} [Ring R] (rk : SylvesterRank R) : Prop :=
  ∃ (U : Type u) (_ : Ring U) (_ : StarRing U) (_ : IsStarRegular U)
    (_ : IsPositiveDefiniteStarRegular U) (φ : R →+* U) (rkU : SylvesterRank U),
    IsEpic φ ∧ rkU.IsFaithful ∧ ∀ (n m : ℕ) (A : Matrix (Fin n) (Fin m) R),
      rk.rk n m A = rkU.rk n m (A.map φ)

end Work.ORHughesFree
