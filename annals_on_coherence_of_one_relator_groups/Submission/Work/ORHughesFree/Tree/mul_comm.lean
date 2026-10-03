import Mathlib
import Submission.Work.ORHughesFree.Tree

set_option autoImplicit false
set_option linter.unusedVariables false

/-!
# Commutativity of the multiplication on `Tree`

`Tree` is the type of finite rooted trees up to isomorphism (`Submission.Work.ORHughesFree.Tree`).
On it, `x * y = ∑_{x' ∈ fam x, y' ∈ fam y} exp (x' + y')` is defined on the representatives
selected by `Quotient.out`.  This file proves that `*` is commutative.

The mathematical content is the reindexing of the double sum
`∑_{a ∈ l} ∑_{b ∈ l'} P a b` into `∑_{b ∈ l'} ∑_{a ∈ l} P a b`, together with the fact that
the individual summands `exp (a + b)` and `exp (b + a)` are isomorphic.  Both are proved at the
level of the raw trees: `perm_flatMap_swap` is the pure list permutation, and the compatibility of
`PermRel` with `map`/`flatMap`/`++` supplies the isomorphism of summands.
-/

namespace Work.ORHughesFree

/-- `PermRel` is coarser than `List.Perm`: equal lists are equivalent as multisets of isomorphic
trees. -/
theorem PermRel.of_perm {l l' : List MTree} (h : List.Perm l l') : PermRel l l' := by
  induction h with
  | nil => exact PermRel.nil
  | cons x _ ih => exact PermRel.cons (Iso.refl x) ih
  | swap x y l => exact PermRel.symm (PermRel.swap x y l)
  | trans _ _ ih1 ih2 => exact PermRel.trans ih1 ih2

/-- Appending a fixed list on the right preserves `PermRel`. -/
theorem PermRel.appendRight {u u' : List MTree} (h : PermRel u u') (t : List MTree) :
    PermRel (u ++ t) (u' ++ t) :=
  PermRel.recOn h
    (motive_1 := fun _ _ _ => True)
    (motive_2 := fun u u' _ => PermRel (u ++ t) (u' ++ t))
    (fun {l} {l'} _ _ => trivial)
    (PermRel.refl t)
    (fun {x} {y} {l} {l'} a a1 _ ih => PermRel.cons a ih)
    (fun x y l => PermRel.swap x y (l ++ t))
    (fun l => PermRel.refl (l ++ t))
    (fun _ ih => PermRel.symm ih)
    (fun _ _ ih1 ih2 => PermRel.trans ih1 ih2)

/-- Appending a fixed list on the left preserves `PermRel`. -/
theorem PermRel.appendLeft (u : List MTree) {v v' : List MTree} (h : PermRel v v') :
    PermRel (u ++ v) (u ++ v') := by
  induction u with
  | nil => exact h
  | cons x xs ih => exact PermRel.cons (Iso.refl x) ih

/-- A pointwise `Iso` congruence for `List.map`. -/
theorem PermRel.map_congr {f g : MTree → MTree} (h : ∀ a, Iso (f a) (g a)) :
    ∀ l : List MTree, PermRel (l.map f) (l.map g) := by
  intro l
  induction l with
  | nil => exact PermRel.nil
  | cons x xs ih =>
      simp only [List.map_cons]
      exact PermRel.cons (h x) ih

/-- A pointwise `PermRel` congruence for `List.flatMap`. -/
theorem PermRel.flatMap_congr {f g : MTree → List MTree} (h : ∀ a, PermRel (f a) (g a)) :
    ∀ l : List MTree, PermRel (l.flatMap f) (l.flatMap g) := by
  intro l
  induction l with
  | nil => exact PermRel.nil
  | cons x xs ih =>
      simp only [List.flatMap_cons]
      exact PermRel.trans (PermRel.appendLeft (f x) ih)
        (PermRel.appendRight (h x) (xs.flatMap g))

/-- `flatMap` of the constantly empty list is empty. -/
theorem flatMap_nil_aux : ∀ l : List MTree, l.flatMap (fun _ => ([] : List MTree)) = []
  | [] => rfl
  | x :: xs => by simp [List.flatMap_cons, flatMap_nil_aux xs]

/-- Rotating the middle block of an appended triple is a permutation. -/
theorem perm_middle (A B X : List MTree) : List.Perm (A ++ (B ++ X)) (B ++ (A ++ X)) := by
  rw [← List.append_assoc, ← List.append_assoc]
  exact List.Perm.append_right X List.perm_append_comm

/-- `List.Perm ((L.map a) ++ (L.flatMap C)) (L.flatMap (fun b => a b :: C b))`. -/
theorem perm_map_flatMap (a : MTree → MTree) (C : MTree → List MTree) :
    ∀ L : List MTree, List.Perm ((L.map a) ++ (L.flatMap C)) (L.flatMap (fun b => a b :: C b))
  | [] => by simp
  | b :: bs => by
      have ih := perm_map_flatMap a C bs
      simp only [List.map_cons, List.flatMap_cons]
      refine List.Perm.cons (a b) ?_
      exact List.Perm.trans (perm_middle (bs.map a) (C b) (bs.flatMap C))
        (List.Perm.append_left (C b) ih)

/-- The double sum `∑_{a ∈ l} ∑_{b ∈ l'} P a b` viewed `a`-major is a permutation of the same
sum viewed `b`-major. -/
theorem perm_flatMap_swap (P : MTree → MTree → MTree) (l l' : List MTree) :
    List.Perm (l.flatMap (fun a => l'.map (fun b => P a b)))
              (l'.flatMap (fun b => l.map (fun a => P a b))) := by
  induction l generalizing l' with
  | nil => simpa using (List.Perm.nil : List.Perm ([] : List MTree) [])
  | cons x xs ih =>
      simp only [List.flatMap_cons, List.map_cons]
      exact List.Perm.trans (List.Perm.append_left (l'.map (fun b => P x b)) (ih l'))
        (perm_map_flatMap (fun b => P x b) (fun b => xs.map (fun a => P a b)) l')

/-- The two summands `exp (a + b)` and `exp (b + a)` are isomorphic. -/
theorem iso_node_swap (a b : MTree) :
    Iso (MTree.node (MTree.children a ++ MTree.children b))
        (MTree.node (MTree.children b ++ MTree.children a)) :=
  Iso.node (PermRel.of_perm List.perm_append_comm)

end Work.ORHughesFree

namespace Work.ORHughesFree.Tree

theorem mul_comm (x y : Tree) : x * y = y * x := by
  show mul x y = mul y x
  unfold mul
  refine Quotient.sound (Iso.node ?_)
  exact PermRel.trans
    (PermRel.of_perm (perm_flatMap_swap
      (fun a b => MTree.node (MTree.children a ++ MTree.children b))
      (MTree.children (Quotient.out x)) (MTree.children (Quotient.out y))))
    (PermRel.flatMap_congr
      (f := fun b => (MTree.children (Quotient.out x)).map
        (fun a => MTree.node (MTree.children a ++ MTree.children b)))
      (g := fun b => (MTree.children (Quotient.out x)).map
        (fun a => MTree.node (MTree.children b ++ MTree.children a)))
      (fun b => PermRel.map_congr (fun a => iso_node_swap a b)
        (MTree.children (Quotient.out x)))
      (MTree.children (Quotient.out y)))

end Work.ORHughesFree.Tree
