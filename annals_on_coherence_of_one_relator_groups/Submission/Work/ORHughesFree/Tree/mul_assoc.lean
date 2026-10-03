import Mathlib
import Submission.Work.ORHughesFree.Tree

/-!
# Associativity of the multiplication of finite rooted trees

`Tree` (`Submission/Work/ORHughesFree/Tree.lean`) is the type of finite rooted trees up to
isomorphism, i.e. the initial algebra of the multiset functor `X ↦ Multiset X`: it is the quotient
of the raw trees `MTree` (a node with a `List` of children) by the relation `Iso` of having the
same multiset of children, recursively.  The operations are defined on the representatives chosen
by `Quotient.out`:

* `x + y` identifies the roots, so its children are `children x ++ children y`;
* `x * y = ∑_{a ∈ fam x, b ∈ fam y} exp (a + b)`, whose children are the raw trees
  `MTree.node (children a ++ children b)` for `a` a child of `x` and `b` a child of `y`;
* `fam x` is the multiset of children of `x` (as a multiset of `Tree`s).

The proof below is organised around the family map `fam`, which is injective --- two trees are
equal iff their families are equal (`eq_of_fam_eq`) --- and satisfies the two recursion rules

* `fam_add : fam (x + y) = fam x + fam y`,
* `fam_mul_aux : fam (x * y) = (fam x).bind (fun a => (fam y).map (fun b => a + b))`.

Associativity of `*` is then the associativity of `Multiset.bind` (`Multiset.bind_assoc`) together
with the associativity of `+` on the individual summands, `add_assoc`, which itself follows from
the associativity of the addition of multisets.

The technical heart is the passage between `PermRel`-related lists of raw trees and multisets of
`Tree`-classes: `PermRel l l'` holds exactly when the multisets of classes of `l` and `l'` agree
(`map_mk_permRel` and its converse `permRel_of_map_mk`).  This lets one replace `Quotient.out t`
by any `Iso`-equivalent raw tree and compute with `Multiset.map`, `Multiset.bind` and the coercion
from lists.  All auxiliary material is private, so this file depends only on the basic definitions
of `Tree`.
-/

namespace Work.ORHughesFree


private abbrev mkT : MTree → Tree := Quotient.mk''

private theorem mtree_node_children (t : MTree) : MTree.node (MTree.children t) = t := by
  cases t with
  | node l => rfl

private theorem permRel_append_right {l l' : List MTree} (h : PermRel l l') (m : List MTree) :
    PermRel (l ++ m) (l' ++ m) :=
  PermRel.rec (motive_1 := fun _ _ _ => True)
    (motive_2 := fun l l' _ => PermRel (l ++ m) (l' ++ m))
    (fun _ _ => trivial)
    (PermRel.refl m)
    (fun hx _hl _ ih => PermRel.cons hx ih)
    (fun x y l => PermRel.swap x y (l ++ m))
    (fun l => PermRel.refl (l ++ m))
    (fun _ ih => PermRel.symm ih)
    (fun _ _ ih1 ih2 => PermRel.trans ih1 ih2)
    h

private theorem permRel_append_left (m : List MTree) {l l' : List MTree} (h : PermRel l l') :
    PermRel (m ++ l) (m ++ l') := by
  induction m with
  | nil => exact h
  | cons a m ih => exact PermRel.cons (Iso.refl a) ih

private theorem permRel_append {l l' m m' : List MTree} (h1 : PermRel l l') (h2 : PermRel m m') :
    PermRel (l ++ m) (l' ++ m') :=
  (permRel_append_right h1 m).trans (permRel_append_left l' h2)

private theorem permRel_of_perm {l l' : List MTree} (h : List.Perm l l') : PermRel l l' := by
  induction h with
  | nil => exact PermRel.nil
  | cons x _ ih => exact PermRel.cons (Iso.refl x) ih
  | swap x y l => exact PermRel.symm (PermRel.swap x y l)
  | trans _ _ ih1 ih2 => exact PermRel.trans ih1 ih2

private theorem perm_middle (A B X : List MTree) : List.Perm (A ++ (B ++ X)) (B ++ (A ++ X)) := by
  rw [← List.append_assoc, ← List.append_assoc]
  exact List.Perm.append_right X List.perm_append_comm

private theorem map_mk_permRel (l l' : List MTree) (h : PermRel l l') :
    Multiset.map mkT (l : Multiset MTree) = Multiset.map mkT (l' : Multiset MTree) :=
  PermRel.rec (motive_1 := fun a a' _ => mkT a = mkT a')
    (motive_2 := fun l l' _ => Multiset.map mkT (l : Multiset MTree) =
      Multiset.map mkT (l' : Multiset MTree))
    (fun hrel _ => Quotient.sound (Iso.node hrel))
    rfl
    (fun hx hl hmk hih => by
      rw [← Multiset.cons_coe, ← Multiset.cons_coe, Multiset.map_cons, Multiset.map_cons, hmk, hih])
    (fun x y l => by
      rw [← Multiset.cons_coe, ← Multiset.cons_coe, ← Multiset.cons_coe, ← Multiset.cons_coe,
        Multiset.map_cons, Multiset.map_cons, Multiset.map_cons, Multiset.map_cons,
        Multiset.cons_swap])
    (fun l => rfl)
    (fun _ ih => ih.symm)
    (fun _ _ ih1 ih2 => ih1.trans ih2)
    h

private theorem permRel_of_map_mk {l l' : List MTree}
    (h : Multiset.map mkT (l : Multiset MTree) = Multiset.map mkT (l' : Multiset MTree)) :
    PermRel l l' := by
  induction l generalizing l' with
  | nil =>
      have hnil : l' = [] := by
        have h1 : Multiset.map mkT (l' : Multiset MTree) = 0 := by simpa using h.symm
        exact (Multiset.coe_eq_zero l').mp (Multiset.map_eq_zero.mp h1)
      subst hnil
      exact PermRel.nil
  | cons x l ih =>
      have hx : mkT x ∈ Multiset.map mkT (l' : Multiset MTree) := by
        rw [← h, ← Multiset.cons_coe, Multiset.map_cons]
        exact Multiset.mem_cons_self _ _
      obtain ⟨y, hy, hyx⟩ := Multiset.mem_map.mp hx
      obtain ⟨s, t, rfl⟩ := List.mem_iff_append.mp (Multiset.mem_coe.mp hy)
      have hsplit : Multiset.map mkT ((s ++ y :: t : List MTree) : Multiset MTree) =
          mkT y ::ₘ Multiset.map mkT ((s ++ t : List MTree) : Multiset MTree) := by
        have hp : (((s ++ y :: t) : List MTree) : Multiset MTree) =
            (((y :: (s ++ t)) : List MTree) : Multiset MTree) := by
          rw [Multiset.coe_eq_coe]
          exact (perm_middle [y] s t).symm
        rw [hp, ← Multiset.cons_coe, Multiset.map_cons]
      have h3 : mkT x ::ₘ Multiset.map mkT (l : Multiset MTree) =
          mkT y ::ₘ Multiset.map mkT ((s ++ t : List MTree) : Multiset MTree) := by
        rw [← Multiset.map_cons, Multiset.cons_coe, ← hsplit]
        exact h
      rw [hyx] at h3
      refine PermRel.trans (PermRel.cons (Quotient.exact hyx.symm)
        (ih (l' := s ++ t) ((Multiset.cons_inj_right _).mp h3))) ?_
      exact permRel_of_perm (perm_middle [y] s t)

namespace Tree

private def cls (l : List MTree) : Multiset Tree := Multiset.map mkT (l : Multiset MTree)

private theorem fam_eq_cls (x : Tree) : fam x = cls (MTree.children (Quotient.out x)) := rfl

private theorem cls_eq_of_permRel {l l' : List MTree} (h : PermRel l l') : cls l = cls l' :=
  map_mk_permRel l l' h

private theorem permRel_of_cls_eq {l l' : List MTree} (h : cls l = cls l') : PermRel l l' :=
  permRel_of_map_mk h

private theorem add_eq_mk (a b : MTree) :
    mkT (MTree.node (MTree.children a ++ MTree.children b)) = mkT a + mkT b := by
  show (Quotient.mk'' (MTree.node (MTree.children a ++ MTree.children b)) : Tree) =
    Quotient.mk'' (MTree.node (MTree.children (Quotient.out (Quotient.mk'' a : Tree)) ++
      MTree.children (Quotient.out (Quotient.mk'' b : Tree))))
  exact Quotient.sound (Iso.node (permRel_append
    (PermRel.of_iso_children (Iso.symm (Quotient.mk_out' a)))
    (PermRel.of_iso_children (Iso.symm (Quotient.mk_out' b)))))

theorem iso_out_node (x : Tree) :
    Iso (Quotient.out x) (MTree.node (MTree.children (Quotient.out x))) := by
  cases Quotient.out x with
  | node l => exact Iso.refl _

theorem add_eq_mk' (x y : Tree) (a b : MTree) (ha : Iso (Quotient.out x) a)
    (hb : Iso (Quotient.out y) b) :
    x + y = Quotient.mk'' (MTree.node (MTree.children a ++ MTree.children b)) := by
  show (Quotient.mk'' (MTree.node (MTree.children (Quotient.out x) ++
    MTree.children (Quotient.out y))) : Tree) = _
  exact Quotient.sound (Iso.node (permRel_append (PermRel.of_iso_children ha)
    (PermRel.of_iso_children hb)))

private theorem cls_add (A B : List MTree) : cls (A ++ B) = cls A + cls B := by
  show Multiset.map mkT ((A ++ B : List MTree) : Multiset MTree) =
    Multiset.map mkT (A : Multiset MTree) + Multiset.map mkT (B : Multiset MTree)
  rw [← Multiset.coe_add, Multiset.map_add]

private theorem fam_add (x y : Tree) : fam (x + y) = fam x + fam y := by
  have hiso : Iso (Quotient.out (x + y))
      (MTree.node (MTree.children (Quotient.out x) ++ MTree.children (Quotient.out y))) :=
    Quotient.exact (show (⟦Quotient.out (x + y)⟧ : Quotient isoSetoid) =
      ⟦MTree.node (MTree.children (Quotient.out x) ++
        MTree.children (Quotient.out y))⟧ from by
      rw [show (⟦Quotient.out (x + y)⟧ : Quotient isoSetoid) = x + y from
        Quotient.out_eq (x + y)]
      rfl)
  have hperm : PermRel (MTree.children (Quotient.out (x + y)))
      (MTree.children (MTree.node (MTree.children (Quotient.out x) ++
        MTree.children (Quotient.out y)))) :=
    PermRel.of_iso_children hiso
  have h : cls (MTree.children (Quotient.out x) ++ MTree.children (Quotient.out y)) =
      fam x + fam y := by
    rw [cls_add, ← fam_eq_cls x, ← fam_eq_cls y]
  exact (fam_eq_cls _).trans ((cls_eq_of_permRel hperm).trans h)

private theorem eq_of_fam_eq {x y : Tree} (h : fam x = fam y) : x = y := by
  have hperm : PermRel (MTree.children (Quotient.out x)) (MTree.children (Quotient.out y)) :=
    permRel_of_cls_eq (by rw [← fam_eq_cls x, ← fam_eq_cls y]; exact h)
  have hA : x = Quotient.mk'' (MTree.node (MTree.children (Quotient.out x))) := by
    rw [mtree_node_children (Quotient.out x)]
    exact (Quotient.out_eq x).symm
  have hB : (Quotient.mk'' (MTree.node (MTree.children (Quotient.out y))) : Tree) = y := by
    rw [mtree_node_children (Quotient.out y)]
    exact Quotient.out_eq y
  exact hA.trans ((Quotient.sound (Iso.node hperm)).trans hB)

private theorem cls_flatMap_add (l l' : List MTree) :
    cls (l.flatMap (fun a => l'.map (fun b =>
        MTree.node (MTree.children a ++ MTree.children b)))) =
      (cls l).bind (fun u => (cls l').map (fun v => u + v)) := by
  show Multiset.map mkT (((l.flatMap (fun a => l'.map (fun b =>
      MTree.node (MTree.children a ++ MTree.children b)))) : List MTree) : Multiset MTree) =
    (Multiset.map mkT (l : Multiset MTree)).bind (fun u =>
      (Multiset.map mkT (l' : Multiset MTree)).map (fun v => u + v))
  have h1 : Multiset.map mkT (((l.flatMap (fun a => l'.map (fun b =>
        MTree.node (MTree.children a ++ MTree.children b)))) : List MTree) : Multiset MTree) =
      Multiset.map mkT ((l : Multiset MTree).bind (fun a =>
        Multiset.map (fun b => MTree.node (MTree.children a ++ MTree.children b))
          (l' : Multiset MTree))) := by
    congr 1
    rw [← Multiset.coe_bind]
    exact Multiset.bind_congr (fun a _ => (Multiset.map_coe _ l').symm)
  have h2 : Multiset.map mkT ((l : Multiset MTree).bind (fun a =>
        Multiset.map (fun b => MTree.node (MTree.children a ++ MTree.children b))
          (l' : Multiset MTree))) =
      (l : Multiset MTree).bind (fun a => Multiset.map
        (fun b => mkT (MTree.node (MTree.children a ++ MTree.children b)))
        (l' : Multiset MTree)) := by
    rw [Multiset.map_bind]
    exact Multiset.bind_congr (fun a _ => Multiset.map_map _ _ _)
  have h3 : (Multiset.map mkT (l : Multiset MTree)).bind (fun u =>
        (Multiset.map mkT (l' : Multiset MTree)).map (fun v => u + v)) =
      (l : Multiset MTree).bind (fun a => Multiset.map
        (fun b => mkT (MTree.node (MTree.children a ++ MTree.children b)))
        (l' : Multiset MTree)) := by
    rw [Multiset.bind_map]
    refine Multiset.bind_congr (fun a _ => ?_)
    calc Multiset.map (fun v => mkT a + v) (Multiset.map mkT (l' : Multiset MTree))
        = Multiset.map ((fun v => mkT a + v) ∘ mkT) (l' : Multiset MTree) :=
          Multiset.map_map _ _ _
      _ = Multiset.map (fun b => mkT (MTree.node (MTree.children a ++ MTree.children b)))
            (l' : Multiset MTree) :=
          Multiset.map_congr rfl (fun b _ => (add_eq_mk a b).symm)
  exact h1.trans (h2.trans h3.symm)

private theorem fam_mul_aux (x y : Tree) :
    fam (x * y) = (fam x).bind (fun a => (fam y).map (fun b => a + b)) := by
  have hiso : Iso (Quotient.out (x * y))
      (MTree.node ((MTree.children (Quotient.out x)).flatMap (fun a =>
        (MTree.children (Quotient.out y)).map (fun b =>
          MTree.node (MTree.children a ++ MTree.children b))))) :=
    Quotient.exact (show (⟦Quotient.out (x * y)⟧ : Quotient isoSetoid) =
      ⟦MTree.node ((MTree.children (Quotient.out x)).flatMap (fun a =>
        (MTree.children (Quotient.out y)).map (fun b =>
          MTree.node (MTree.children a ++ MTree.children b))))⟧ from by
      rw [show (⟦Quotient.out (x * y)⟧ : Quotient isoSetoid) = x * y from Quotient.out_eq (x * y)]
      rfl)
  have hperm : PermRel (MTree.children (Quotient.out (x * y)))
      (MTree.children (MTree.node ((MTree.children (Quotient.out x)).flatMap (fun a =>
        (MTree.children (Quotient.out y)).map (fun b =>
          MTree.node (MTree.children a ++ MTree.children b)))))) :=
    PermRel.of_iso_children hiso
  calc fam (x * y) = cls (MTree.children (Quotient.out (x * y))) := fam_eq_cls _
    _ = cls ((MTree.children (Quotient.out x)).flatMap (fun a =>
          (MTree.children (Quotient.out y)).map (fun b =>
            MTree.node (MTree.children a ++ MTree.children b)))) :=
        cls_eq_of_permRel hperm
    _ = (cls (MTree.children (Quotient.out x))).bind (fun u =>
          (cls (MTree.children (Quotient.out y))).map (fun v => u + v)) :=
        cls_flatMap_add _ _
    _ = (fam x).bind (fun a => (fam y).map (fun b => a + b)) := rfl

private theorem add_assoc (x y z : Tree) : x + y + z = x + (y + z) := by
  refine eq_of_fam_eq ?_
  rw [fam_add (x + y) z, fam_add x y, fam_add x (y + z), fam_add y z]
  exact Multiset.add_assoc _ _ _

theorem mul_assoc (x y z : Tree) : x * y * z = x * (y * z) := by
  have h1 : ((fam x).bind (fun a => (fam y).map (fun b => a + b))).bind
        (fun d => (fam z).map (fun c => d + c)) =
      (fam x).bind (fun a => (fam y).bind (fun b => (fam z).map (fun c => (a + b) + c))) := by
    calc ((fam x).bind (fun a => (fam y).map (fun b => a + b))).bind
            (fun d => (fam z).map (fun c => d + c))
        = (fam x).bind (fun a => ((fam y).map (fun b => a + b)).bind
            (fun d => (fam z).map (fun c => d + c))) := Multiset.bind_assoc
      _ = (fam x).bind (fun a => (fam y).bind
            (fun b => (fam z).map (fun c => (a + b) + c))) :=
          Multiset.bind_congr (fun a _ => Multiset.bind_map _ _ _)
  have h2 : (fam x).bind (fun a =>
        ((fam y).bind (fun b => (fam z).map (fun c => b + c))).map (fun e => a + e)) =
      (fam x).bind (fun a => (fam y).bind (fun b => (fam z).map (fun c => a + (b + c)))) := by
    calc (fam x).bind (fun a =>
            ((fam y).bind (fun b => (fam z).map (fun c => b + c))).map (fun e => a + e))
        = (fam x).bind (fun a => (fam y).bind (fun b =>
            ((fam z).map (fun c => b + c)).map (fun e => a + e))) :=
          Multiset.bind_congr (fun a _ => Multiset.map_bind _ _ _)
      _ = (fam x).bind (fun a => (fam y).bind
            (fun b => (fam z).map (fun c => a + (b + c)))) :=
          Multiset.bind_congr (fun a _ => Multiset.bind_congr
            (fun b _ => Multiset.map_map _ _ _))
  have h3 : (fam x).bind (fun a => (fam y).bind (fun b =>
        (fam z).map (fun c => (a + b) + c))) =
      (fam x).bind (fun a => (fam y).bind (fun b =>
        (fam z).map (fun c => a + (b + c)))) :=
    Multiset.bind_congr (fun a _ => Multiset.bind_congr
      (fun b _ => Multiset.map_congr rfl (fun c _ => add_assoc a b c)))
  refine eq_of_fam_eq ?_
  rw [fam_mul_aux (x * y) z, fam_mul_aux x y, fam_mul_aux x (y * z), fam_mul_aux y z]
  exact h1.trans (h3.trans h2.symm)

end Tree

end Work.ORHughesFree
