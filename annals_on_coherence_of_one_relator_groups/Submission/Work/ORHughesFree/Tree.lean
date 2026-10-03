/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Finite rooted trees

`Tree` is the type of finite rooted trees up to isomorphism, i.e. the initial algebra of the
multiset functor `X ↦ Multiset X`.  It carries the operations of [JZLA20, §4.1]:

* `add` identifies the roots (their families of subtrees are combined);
* `mul` is `x * y = ∑_{x' ∈ fam x, y' ∈ fam y} exp (x' + y')`;
* `exp x` is the tree with the single child `x`;
* `0` is the one-vertex tree and `1 = exp 0` the one-edge tree.

Representatives are `List`-nested trees, and isomorphism is equality of the multisets of children,
recursively.  The operations are defined on representatives chosen by `Quotient.out`; the
accompanying lemmas (`Tree.add_comm`, …, `Tree.mul_eq`) show that the resulting structure is a
commutative semiring and satisfies the recursion of [JZLA20, §4.1].
-/
import Mathlib

set_option autoImplicit false

universe u

namespace Work.ORHughesFree

/-- Raw finite rooted trees: a node together with an ordered list of children. -/
inductive MTree where
  /-- a node with the given children -/
  | node : List MTree → MTree

namespace MTree

/-- The children of a raw tree. -/
def children : MTree → List MTree
  | .node l => l

end MTree

/- Isomorphism of raw trees: equality of the multisets of children, recursively (`PermRel l l'`
says that the two lists are the same as multisets of pairwise isomorphic trees). -/
mutual
  inductive Iso : MTree → MTree → Prop
    | node {l l' : List MTree} : PermRel l l' → Iso (MTree.node l) (MTree.node l')
  inductive PermRel : List MTree → List MTree → Prop
    | nil : PermRel [] []
    | cons {x y : MTree} {l l' : List MTree} :
        Iso x y → PermRel l l' → PermRel (x :: l) (y :: l')
    | swap (x y : MTree) (l : List MTree) : PermRel (x :: y :: l) (y :: x :: l)
    | refl (l : List MTree) : PermRel l l
    | symm {l l' : List MTree} : PermRel l l' → PermRel l' l
    | trans {l l' l'' : List MTree} : PermRel l l' → PermRel l' l'' → PermRel l l''
end

theorem Iso.refl : ∀ t : MTree, Iso t t
  | .node l => Iso.node (PermRel.refl l)

theorem Iso.symm : ∀ {t t' : MTree}, Iso t t' → Iso t' t
  | _, _, Iso.node h => Iso.node (PermRel.symm h)

theorem Iso.trans : ∀ {t t' t'' : MTree}, Iso t t' → Iso t' t'' → Iso t t''
  | _, _, _, Iso.node h, Iso.node h' => Iso.node (PermRel.trans h h')

/-- The kernel of `PermRel` on children: `Iso`-equivalent trees have `PermRel`-equivalent children. -/
theorem PermRel.of_iso_children {t t' : MTree} (h : Iso t t') :
    PermRel (MTree.children t) (MTree.children t') := by
  cases h with
  | node h => exact h

instance isoSetoid : Setoid MTree where
  r := Iso
  iseqv := ⟨Iso.refl, fun h => Iso.symm h, fun h h' => Iso.trans h h'⟩

/-- The type of finite rooted trees up to isomorphism. -/
def Tree : Type := Quotient isoSetoid

namespace Tree

/-- The tree with the single child `x`. -/
noncomputable def exp (x : Tree) : Tree := Quotient.mk'' (MTree.node [Quotient.out x])

/-- `x + y` is the tree whose family of subtrees is the union of those of `x` and `y`
(equivalently, `x` and `y` with their roots identified). -/
noncomputable def add (x y : Tree) : Tree :=
  Quotient.mk'' (MTree.node (MTree.children (Quotient.out x) ++
    MTree.children (Quotient.out y)))

/-- `x * y = ∑_{x' ∈ fam x, y' ∈ fam y} exp (x' + y')`, whose family of subtrees is
`{x' + y' : x' ∈ fam x, y' ∈ fam y}`. -/
noncomputable def mul (x y : Tree) : Tree :=
  Quotient.mk'' (MTree.node ((MTree.children (Quotient.out x)).flatMap (fun a =>
    (MTree.children (Quotient.out y)).map (fun b =>
      MTree.node (MTree.children a ++ MTree.children b)))))

/-- The family of subtrees of a tree. -/
noncomputable def fam (x : Tree) : Multiset Tree :=
  Multiset.ofList ((MTree.children (Quotient.out x)).map Quotient.mk'')

/-- The one-vertex tree. -/
noncomputable def zero : Tree := Quotient.mk'' (MTree.node [])

/-- The one-edge tree `exp 0`. -/
noncomputable def one : Tree := exp zero

noncomputable instance : Zero Tree := ⟨zero⟩
noncomputable instance : One Tree := ⟨one⟩
noncomputable instance : Add Tree := ⟨add⟩
noncomputable instance : Mul Tree := ⟨mul⟩

end Tree

end Work.ORHughesFree
