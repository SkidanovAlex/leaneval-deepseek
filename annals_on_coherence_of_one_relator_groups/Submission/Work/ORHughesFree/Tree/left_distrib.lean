/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Left distributivity of `*` over `+` on finite rooted trees

`Tree` is the type of finite rooted trees up to isomorphism (`Submission/Work/ORHughesFree/Tree.lean`).
The operations `+` and `*` are defined through representatives chosen by `Quotient.out`, so all
statements about them have to be reduced to statements about the explicit representatives
`MTree.node (children t)`.  This file develops the small amount of `PermRel`/`Iso` combinatorics
that this reduction needs and then proves `x * (y + z) = x * y + x * z`.
-/
import Mathlib
import Submission.Work.ORHughesFree.Tree

namespace Work.ORHughesFree.Tree

open Work.ORHughesFree

/-! ## Combinatorics of `PermRel` on lists of raw trees -/

/-- Induction principle for `PermRel`, which is a mutual inductive together with `Iso` and hence
is not handled by the `induction` tactic. -/
private theorem ld_permRel_induct {motive : (l l' : List MTree) → PermRel l l' → Prop}
    (hnil : motive [] [] PermRel.nil)
    (hcons : ∀ {x y : MTree} {l l' : List MTree} (hxy : Iso x y) (h : PermRel l l'),
      motive l l' h → motive (x :: l) (y :: l') (PermRel.cons hxy h))
    (hswap : ∀ (x y : MTree) (l : List MTree),
      motive (x :: y :: l) (y :: x :: l) (PermRel.swap x y l))
    (hrefl : ∀ l, motive l l (PermRel.refl l))
    (hsymm : ∀ {l l'} (h : PermRel l l'), motive l l' h → motive l' l (PermRel.symm h))
    (htrans : ∀ {l l' l''} (h : PermRel l l') (h' : PermRel l' l''),
      motive l l' h → motive l' l'' h' → motive l l'' (PermRel.trans h h')) :
    ∀ {l l'} (h : PermRel l l'), motive l l' h :=
  PermRel.rec (motive_1 := fun _ _ _ => True) (motive_2 := motive)
    (fun _ _ => trivial) hnil (fun hxy h _ ih => hcons hxy h ih) hswap hrefl hsymm htrans

private theorem ld_of_eq {l l' : List MTree} (h : l = l') : PermRel l l' := h ▸ PermRel.refl l

/-- `List.Perm` is contained in `PermRel`. -/
private theorem ld_of_perm {l l' : List MTree} (h : l.Perm l') : PermRel l l' := by
  induction h with
  | nil => exact PermRel.nil
  | cons _ _ ih => exact PermRel.cons (Iso.refl _) ih
  | swap a b c => exact PermRel.symm (PermRel.swap a b c)
  | trans _ _ ih1 ih2 => exact PermRel.trans ih1 ih2

private theorem ld_append_right {l l' : List MTree} (h : PermRel l l') (m : List MTree) :
    PermRel (l ++ m) (l' ++ m) := by
  refine ld_permRel_induct (motive := fun l l' _ => PermRel (l ++ m) (l' ++ m)) ?_ ?_ ?_ ?_ ?_ ?_ h
  · exact PermRel.refl m
  · intro x y l l' hxy h ih; exact PermRel.cons hxy ih
  · intro x y l; exact PermRel.swap x y (l ++ m)
  · intro l; exact PermRel.refl (l ++ m)
  · intro l l' h ih; exact PermRel.symm ih
  · intro l l' l'' h h' ih1 ih2; exact PermRel.trans ih1 ih2

private theorem ld_append_left {m m' : List MTree} (h : PermRel m m') (l : List MTree) :
    PermRel (l ++ m) (l ++ m') := by
  induction l with
  | nil => exact h
  | cons a l ih => exact PermRel.cons (Iso.refl a) ih

private theorem ld_append {l₁ l₂ l₁' l₂' : List MTree} (h₁ : PermRel l₁ l₁') (h₂ : PermRel l₂ l₂') :
    PermRel (l₁ ++ l₂) (l₁' ++ l₂') :=
  (ld_append_right h₁ l₂).trans (ld_append_left h₂ l₁')

private theorem ld_swap_blocks (A B : List MTree) : PermRel (A ++ B) (B ++ A) :=
  ld_of_perm List.perm_append_comm

/-- Two lists mapped by pointwise `Iso`-equivalent maps are `PermRel`-equivalent. -/
private theorem ld_map_pointwise {f f' : MTree → MTree} (h : ∀ a, Iso (f a) (f' a))
    (l : List MTree) : PermRel (l.map f) (l.map f') := by
  induction l with
  | nil => exact PermRel.nil
  | cons a l ih => exact PermRel.cons (h a) ih

private theorem ld_map {f : MTree → MTree} (hf : ∀ a b, Iso a b → Iso (f a) (f b))
    {l l' : List MTree} (h : PermRel l l') : PermRel (l.map f) (l'.map f) := by
  refine ld_permRel_induct (motive := fun l l' _ => PermRel (l.map f) (l'.map f)) ?_ ?_ ?_ ?_ ?_ ?_ h
  · exact PermRel.nil
  · intro x y l l' hxy h ih; exact PermRel.cons (hf x y hxy) ih
  · intro x y l; exact PermRel.swap (f x) (f y) (l.map f)
  · intro l; exact PermRel.refl (l.map f)
  · intro l l' h ih; exact PermRel.symm ih
  · intro l l' l'' h h' ih1 ih2; exact PermRel.trans ih1 ih2

/-- `flatMap` of pointwise `PermRel`-equivalent maps on a fixed list. -/
private theorem ld_flatMap_congr {f f' : MTree → List MTree} (h : ∀ a, PermRel (f a) (f' a))
    (l : List MTree) : PermRel (l.flatMap f) (l.flatMap f') := by
  induction l with
  | nil => exact PermRel.nil
  | cons a l ih => exact ld_append (h a) ih

/-- `flatMap` of a single map that turns `Iso` into `PermRel`. -/
private theorem ld_flatMap_hom {f : MTree → List MTree} (hf : ∀ a b, Iso a b → PermRel (f a) (f b)) :
    ∀ {l l' : List MTree}, PermRel l l' → PermRel (l.flatMap f) (l'.flatMap f) := by
  intro l l' h
  refine ld_permRel_induct (motive := fun l l' _ => PermRel (l.flatMap f) (l'.flatMap f))
    ?_ ?_ ?_ ?_ ?_ ?_ h
  · exact PermRel.nil
  · intro x y l l' hxy h ih; exact ld_append (hf x y hxy) ih
  · intro x y l
    have h3 : PermRel ((f x ++ f y) ++ l.flatMap f) ((f y ++ f x) ++ l.flatMap f) :=
      ld_append (ld_swap_blocks (f x) (f y)) (PermRel.refl _)
    simp only [List.append_assoc] at h3
    exact h3
  · intro l
    exact ld_flatMap_congr (fun a => hf a a (Iso.refl a)) l
  · intro l l' h ih; exact PermRel.symm ih
  · intro l l' l'' h h' ih1 ih2; exact PermRel.trans ih1 ih2

/-! ## List combinatorics -/

/-- `flatMap` of a pointwise appended pair of maps is a permutation of the appended `flatMap`s. -/
private theorem ld_flatMap_add_perm (l : List MTree) (f g : MTree → List MTree) :
    (l.flatMap (fun a => f a ++ g a)).Perm (l.flatMap f ++ l.flatMap g) := by
  induction l with
  | nil => exact List.Perm.refl _
  | cons a l ih =>
    rw [List.flatMap_cons, List.flatMap_cons, List.flatMap_cons]
    rw [← Multiset.coe_eq_coe] at ih ⊢
    simp only [← Multiset.coe_add] at ih ⊢
    rw [ih]
    ac_rfl

/-! ## The raw operations underlying `Tree.add` and `Tree.mul` -/

/-- Raw version of `Tree.add` on representatives. -/
private def ldAdd (t t' : MTree) : MTree := MTree.node (t.children ++ t'.children)

/-- Raw version of `Tree.mul` on representatives. -/
private def ldMul (t t' : MTree) : MTree :=
  MTree.node (t.children.flatMap (fun a =>
    t'.children.map (fun b => MTree.node (a.children ++ b.children))))

private theorem ldAdd_children (t t' : MTree) :
    (ldAdd t t').children = t.children ++ t'.children := rfl

private theorem ldMul_children (t t' : MTree) :
    (ldMul t t').children = t.children.flatMap (fun a =>
      t'.children.map (fun b => MTree.node (a.children ++ b.children))) := rfl

private theorem Iso_ldAdd {a a' b b' : MTree} (ha : Iso a a') (hb : Iso b b') :
    Iso (ldAdd a b) (ldAdd a' b') :=
  Iso.node (ld_append (PermRel.of_iso_children ha) (PermRel.of_iso_children hb))

private theorem Iso_ldMul_right {s t t' : MTree} (h : Iso t t') :
    Iso (ldMul s t) (ldMul s t') := by
  have hch : PermRel t.children t'.children := PermRel.of_iso_children h
  refine Iso.node (ld_flatMap_congr (l := s.children) ?_)
  intro a
  exact ld_map (f := fun b => MTree.node (a.children ++ b.children))
    (fun b b' hbb => Iso.node (ld_append (PermRel.refl a.children) (PermRel.of_iso_children hbb)))
    hch

private theorem Iso_ldMul_left {s s' t : MTree} (h : Iso s s') :
    Iso (ldMul s t) (ldMul s' t) := by
  refine Iso.node (ld_flatMap_hom
    (f := fun a => t.children.map (fun b => MTree.node (a.children ++ b.children))) ?_
    (PermRel.of_iso_children h))
  intro a b hab
  exact ld_map_pointwise
    (fun c => Iso.node (ld_append (PermRel.of_iso_children hab) (PermRel.refl c.children)))
    t.children

/-- The raw identity behind distributivity: `mul` is "linear" in its second argument. -/
private theorem ldPermRel_ldMul_ldAdd (s t t' : MTree) :
    PermRel (MTree.children (ldMul s (ldAdd t t')))
      (MTree.children (ldAdd (ldMul s t) (ldMul s t'))) := by
  simp only [ldMul_children, ldAdd_children, List.map_append]
  exact ld_of_perm (ld_flatMap_add_perm _ _ _)

private theorem Iso_ldMul_ldAdd (s t t' : MTree) :
    Iso (ldMul s (ldAdd t t')) (ldAdd (ldMul s t) (ldMul s t')) :=
  Iso.node (ldPermRel_ldMul_ldAdd s t t')

/-! ## Reducing `Tree` operations to raw operations -/

/-- `Quotient.mk''` as a function into `Tree`, so that the setoid is pinned down. -/
private def ldMk (t : MTree) : Tree := Quotient.mk'' t

private theorem ld_mul_eq_mk (x y : Tree) :
    x * y = ldMk (ldMul (Quotient.out x) (Quotient.out y)) := rfl

private theorem ld_add_eq_mk (x y : Tree) :
    x + y = ldMk (ldAdd (Quotient.out x) (Quotient.out y)) := rfl

/-! ## Left distributivity -/

theorem left_distrib (x y z : Tree) : x * (y + z) = x * y + x * z := by
  have hyz : Iso (Quotient.out (y + z)) (ldAdd (Quotient.out y) (Quotient.out z)) :=
    Quotient.exact (s := isoSetoid) (a := Quotient.out (y + z))
      (b := ldAdd (Quotient.out y) (Quotient.out z))
      (Eq.trans (Quotient.out_eq (y + z)) (ld_add_eq_mk y z))
  have hxy : Iso (Quotient.out (x * y)) (ldMul (Quotient.out x) (Quotient.out y)) :=
    Quotient.exact (s := isoSetoid) (a := Quotient.out (x * y))
      (b := ldMul (Quotient.out x) (Quotient.out y))
      (Eq.trans (Quotient.out_eq (x * y)) (ld_mul_eq_mk x y))
  have hxz : Iso (Quotient.out (x * z)) (ldMul (Quotient.out x) (Quotient.out z)) :=
    Quotient.exact (s := isoSetoid) (a := Quotient.out (x * z))
      (b := ldMul (Quotient.out x) (Quotient.out z))
      (Eq.trans (Quotient.out_eq (x * z)) (ld_mul_eq_mk x z))
  have h1 : x * (y + z) = ldMk (ldMul (Quotient.out x) (Quotient.out (y + z))) :=
    ld_mul_eq_mk x (y + z)
  have h2 : ldMk (ldMul (Quotient.out x) (Quotient.out (y + z)))
      = ldMk (ldMul (Quotient.out x) (ldAdd (Quotient.out y) (Quotient.out z))) :=
    Quotient.sound (Iso_ldMul_right hyz)
  have h3 : ldMk (ldMul (Quotient.out x) (ldAdd (Quotient.out y) (Quotient.out z)))
      = ldMk (ldAdd (ldMul (Quotient.out x) (Quotient.out y))
          (ldMul (Quotient.out x) (Quotient.out z))) :=
    Quotient.sound (Iso_ldMul_ldAdd (Quotient.out x) (Quotient.out y) (Quotient.out z))
  have h4 : ldMk (ldAdd (ldMul (Quotient.out x) (Quotient.out y))
        (ldMul (Quotient.out x) (Quotient.out z)))
      = ldMk (ldAdd (Quotient.out (x * y)) (Quotient.out (x * z))) :=
    Quotient.sound (Iso_ldAdd hxy.symm hxz.symm)
  have h5 : ldMk (ldAdd (Quotient.out (x * y)) (Quotient.out (x * z))) = x * y + x * z :=
    (ld_add_eq_mk (x * y) (x * z)).symm
  exact h1.trans (h2.trans (h3.trans (h4.trans h5)))

end Work.ORHughesFree.Tree
