/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The family of a product of finite rooted trees

`Tree` is the quotient of the raw finite rooted trees `MTree` by the isomorphism relation
`Iso` (`Submission/Work/ORHughesFree/Tree.lean`).  The defining property of the multiplication
is `fam (x * y) = {a + b : a ∈ fam x, b ∈ fam y}`, i.e.
`fam (x * y) = (fam x).bind (fun a => (fam y).map (fun b => a + b))`.

The operations on `Tree` are defined through the representatives picked by `Quotient.out`, so
the proof consists in reducing everything to the explicit representatives
`MTree.node (children t)` and doing the bookkeeping of the double sum on multisets.
-/
import Mathlib
import Submission.Work.ORHughesFree.Tree
import Submission.Work.ORHughesFree.Tree.fam_exp

namespace Work.ORHughesFree.Tree

open Work.ORHughesFree

/-! ## `PermRel` and list append -/

/-- `PermRel` is invariant under appending a fixed list on the right. -/
private theorem permRel_append_right {l l' : List MTree} (h : PermRel l l') (m : List MTree) :
    PermRel (l ++ m) (l' ++ m) :=
  PermRel.rec (motive_1 := fun _ _ _ => True)
    (motive_2 := fun l l' _ => PermRel (l ++ m) (l' ++ m))
    (fun _ _ => trivial)
    (PermRel.refl m)
    (fun hx _ _ ih => PermRel.cons hx ih)
    (fun x y l => PermRel.swap x y (l ++ m))
    (fun l => PermRel.refl (l ++ m))
    (fun _ ih => PermRel.symm ih)
    (fun _ _ ih1 ih2 => PermRel.trans ih1 ih2)
    h

/-- `PermRel` is invariant under appending a fixed list on the left. -/
private theorem permRel_append_left {l l' : List MTree} (h : PermRel l l') (m : List MTree) :
    PermRel (m ++ l) (m ++ l') := by
  induction m with
  | nil => exact h
  | cons x xs ih => exact PermRel.cons (Iso.refl x) ih

/-- `PermRel` is a congruence for `List.append`. -/
private theorem permRel_append {a a' b b' : List MTree} (ha : PermRel a a') (hb : PermRel b b') :
    PermRel (a ++ b) (a' ++ b') :=
  (permRel_append_right ha b).trans (permRel_append_left hb a')

/-! ## Explicit representatives -/

/-- `Quotient.mk''` as a function `MTree → Tree`, so that the setoid is pinned down. -/
noncomputable def mkT (a : MTree) : Tree := Quotient.mk'' a

/-- The `Quotient.out` representative of `mkT a` is isomorphic to `a`. -/
theorem iso_out_mkT (a : MTree) : Iso (Quotient.out (mkT a)) a :=
  Quotient.exact (show (Quotient.mk'' (Quotient.out (mkT a)) : Tree) = Quotient.mk'' a from
    Quotient.out_eq (mkT a))

/-- The children of `Quotient.out (mkT a)` are `PermRel`-equivalent to those of `a`. -/
theorem permRel_children_out_mkT (a : MTree) :
    PermRel (MTree.children (Quotient.out (mkT a))) (MTree.children a) :=
  PermRel.of_iso_children (iso_out_mkT a)

/-- Addition computed on explicit representatives: `mkT a + mkT b` is the node whose children
are the concatenation of the children of `a` and of `b`. -/
theorem add_mkT (a b : MTree) :
    mkT a + mkT b = mkT (MTree.node (MTree.children a ++ MTree.children b)) := by
  have hperm : PermRel
      (MTree.children (Quotient.out (mkT a)) ++ MTree.children (Quotient.out (mkT b)))
      (MTree.children a ++ MTree.children b) :=
    permRel_append (permRel_children_out_mkT a) (permRel_children_out_mkT b)
  show (Quotient.mk'' _ : Tree) = _
  exact Quotient.sound (Iso.node hperm)

/-- The family of a tree given by an explicit representative. -/
theorem fam_mkT (a : MTree) :
    fam (mkT a) = Multiset.ofList ((MTree.children a).map mkT) :=
  PermRel.multiset_map_mk _ _ (permRel_children_out_mkT a)

/-- Passing `mkT` through the `flatMap` defining the double sum. -/
private theorem map_flatMap_mkT (l l' : List MTree) :
    ((l.flatMap (fun a => l'.map (fun b =>
        MTree.node (MTree.children a ++ MTree.children b)))).map mkT)
      = l.flatMap (fun a => l'.map (fun b =>
          mkT (MTree.node (MTree.children a ++ MTree.children b)))) := by
  rw [List.map_flatMap]
  simp only [List.map_map]
  rfl

/-! ## The double sum on multisets -/

/-- The core multiset identity: the double sum `∑_{a ∈ l} ∑_{b ∈ l'} {a + b}` of `Tree` elements
is the union of the `Tree`s represented by `MTree.node (children a ++ children b)`, i.e. the
multiset of children of the raw product of the two representatives. -/
private theorem fam_bind (l l' : List MTree) :
    (Multiset.ofList (l.map mkT)).bind (fun a => (Multiset.ofList (l'.map mkT)).map
        (fun b => a + b)) =
      Multiset.ofList (l.flatMap (fun a => l'.map (fun b =>
        mkT (MTree.node (MTree.children a ++ MTree.children b))))) := by
  have hinner : ∀ a : MTree,
      (Multiset.ofList (l'.map mkT)).map (fun b => mkT a + b) =
        Multiset.ofList (l'.map (fun b =>
          mkT (MTree.node (MTree.children a ++ MTree.children b)))) := by
    intro a
    rw [show Multiset.ofList (l'.map mkT) = (Multiset.ofList l').map mkT from
      (Multiset.map_coe mkT l').symm]
    rw [Multiset.map_map]
    rw [Multiset.map_coe]
    rw [List.map_congr_left (l := l') (f := (fun b => mkT a + b) ∘ mkT)
      (g := fun b => mkT (MTree.node (MTree.children a ++ MTree.children b)))
      (fun b _ => add_mkT a b)]
  have hfun : (fun a : MTree => (Multiset.ofList (l'.map mkT)).map (fun b => mkT a + b))
      = (fun a : MTree => Multiset.ofList (l'.map (fun b =>
          mkT (MTree.node (MTree.children a ++ MTree.children b))))) := funext hinner
  rw [show Multiset.ofList (l.map mkT) = (Multiset.ofList l).map mkT from
    (Multiset.map_coe mkT l).symm]
  rw [Multiset.bind_map]
  rw [hfun]
  exact Multiset.coe_bind l _

/-! ## The main theorem -/

theorem fam_mul (x y : Work.ORHughesFree.Tree) :
    Work.ORHughesFree.Tree.fam (x * y) =
      (Work.ORHughesFree.Tree.fam x).bind
        (fun a => (Work.ORHughesFree.Tree.fam y).map (fun b => a + b)) := by
  have hx : fam x = Multiset.ofList ((MTree.children (Quotient.out x)).map mkT) := rfl
  have hy : fam y = Multiset.ofList ((MTree.children (Quotient.out y)).map mkT) := rfl
  have hxy : fam (x * y) = Multiset.ofList
      ((MTree.children (Quotient.out x)).flatMap (fun a =>
        (MTree.children (Quotient.out y)).map (fun b =>
          mkT (MTree.node (MTree.children a ++ MTree.children b))))) := by
    rw [show x * y = mkT (MTree.node ((MTree.children (Quotient.out x)).flatMap (fun a =>
        (MTree.children (Quotient.out y)).map (fun b =>
          MTree.node (MTree.children a ++ MTree.children b))))) from rfl]
    rw [fam_mkT]
    exact congrArg Multiset.ofList (map_flatMap_mkT _ _)
  rw [hxy, hx, hy]
  exact (fam_bind _ _).symm

end Work.ORHughesFree.Tree
