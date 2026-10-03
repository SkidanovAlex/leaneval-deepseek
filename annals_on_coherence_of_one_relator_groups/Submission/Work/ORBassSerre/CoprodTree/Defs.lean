/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The Bass--Serre tree of a free product `A ∗ B`: the quiver

This file sets up the *quiver* model of the Bass--Serre tree of a free product of two groups
`A`, `B`: the vertices are the disjoint union of the left coset spaces of the two factors inside
`A ∗ B`, and the arrows are the group elements `g`, the arrow with label `g` joining the `A`-coset
of `g` to its `B`-coset.

## Main definitions

* `SubA A B`, `SubB A B` : the images of the two factors in `A ∗ B`;
* `cosetSetoid S` : the setoid of left cosets of a subgroup `S`;
* `Vertex A B` : `Quotient (cosetSetoid SubA) ⊕ Quotient (cosetSetoid SubB)`;
* `vA g`, `vB g` : the vertices of the cosets of `g`;
* `vtx g s` : the vertex `vA g` (if `s = true`) or `vB g`;
* `sideFactor A B s` : `SubA` if `s = true`, `SubB` if `s = false`;
* the `Quiver`, `Quiver.HasInvolutiveReverse`, `MulAction` and `Work.ORBassSerre.GraphAction`
  instances.

The tree property is proved in `Submission/Work/ORBassSerre/CoprodTree/Tree.lean`.
-/
import Mathlib
import Submission.Work.ORBassSerre.CoprodTree.NormalFormDefs
import Submission.Work.ORBassSerre.Action.Basic

set_option autoImplicit false
set_option linter.unusedVariables false

universe u v w

namespace Work.ORBassSerre.CoprodTree

open Monoid

/-! ## The two factors and their cosets -/

/-- The image of the first factor in the free product `A ∗ B`. -/
abbrev SubA (A : Type u) (B : Type v) [Group A] [Group B] : Subgroup (Monoid.Coprod A B) :=
  (Monoid.Coprod.inl : A →* Monoid.Coprod A B).range

/-- The image of the second factor in the free product `A ∗ B`. -/
abbrev SubB (A : Type u) (B : Type v) [Group A] [Group B] : Subgroup (Monoid.Coprod A B) :=
  (Monoid.Coprod.inr : B →* Monoid.Coprod A B).range

/-- The factor corresponding to a side: `SubA` on the `true` side, `SubB` on the `false` side. -/
def sideFactor (A : Type u) (B : Type v) [Group A] [Group B] (s : Bool) :
    Subgroup (Monoid.Coprod A B) :=
  bif s then SubA A B else SubB A B

variable {A : Type u} {B : Type v} [Group A] [Group B]

@[simp] theorem sideFactor_true : sideFactor A B true = SubA A B := rfl
@[simp] theorem sideFactor_false : sideFactor A B false = SubB A B := rfl

theorem inl_mem_SubA (a : A) :
    (Monoid.Coprod.inl a : Monoid.Coprod A B) ∈ SubA A B := ⟨a, rfl⟩
theorem inr_mem_SubB (b : B) :
    (Monoid.Coprod.inr b : Monoid.Coprod A B) ∈ SubB A B := ⟨b, rfl⟩

/-- The two factors intersect trivially in `A ∗ B`.  (This follows from the projection
`Monoid.Coprod.fst`.) -/
theorem SubA_inf_SubB : SubA A B ⊓ SubB A B = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  rintro x ⟨⟨a, rfl⟩, ⟨b, hb⟩⟩
  have h : (Monoid.Coprod.inl a : Monoid.Coprod A B) = Monoid.Coprod.inr b := hb.symm
  have h1 := congrArg Monoid.Coprod.fst h
  simp only [Monoid.Coprod.fst_apply_inl, Monoid.Coprod.fst_apply_inr] at h1
  subst h1
  simp

/-- Left cosets of a subgroup, as a setoid. -/
def cosetSetoid {H : Type w} [Group H] (S : Subgroup H) : Setoid H where
  r x y := x⁻¹ * y ∈ S
  iseqv :=
    ⟨fun x => by simp,
     fun {x y} h => by
       have := S.inv_mem h
       simpa [mul_inv_rev, inv_inv] using this,
     fun {x y z} h₁ h₂ => by
       have := S.mul_mem h₁ h₂
       simpa [mul_assoc] using this⟩

/-! ## The vertices and the quiver structure -/

/-- The vertex set of the Bass--Serre tree of `A ∗ B`: the left cosets of the two factors. -/
abbrev Vertex (A : Type u) (B : Type v) [Group A] [Group B] : Type (max u v) :=
  Quotient (cosetSetoid (SubA A B)) ⊕ Quotient (cosetSetoid (SubB A B))

/-- The vertex corresponding to the left coset `g · SubA`. -/
def vA (g : Monoid.Coprod A B) : Vertex A B := Sum.inl (Quotient.mk _ g)

/-- The vertex corresponding to the left coset `g · SubB`. -/
def vB (g : Monoid.Coprod A B) : Vertex A B := Sum.inr (Quotient.mk _ g)

@[simp] theorem vA_eq_vA_iff {g g' : Monoid.Coprod A B} :
    vA g = vA g' ↔ g⁻¹ * g' ∈ SubA A B := by
  rw [vA, vA, Sum.inl.inj_iff]
  exact Quotient.eq

@[simp] theorem vB_eq_vB_iff {g g' : Monoid.Coprod A B} :
    vB g = vB g' ↔ g⁻¹ * g' ∈ SubB A B := by
  rw [vB, vB, Sum.inr.inj_iff]
  exact Quotient.eq

theorem vA_ne_vB (g g' : Monoid.Coprod A B) : vA g ≠ vB g' := by
  intro h
  exact Sum.inl_ne_inr h

theorem vB_ne_vA (g g' : Monoid.Coprod A B) : vB g ≠ vA g' := by
  intro h
  exact Sum.inr_ne_inl h

theorem vA_mul_mem {g a : Monoid.Coprod A B} (ha : a ∈ SubA A B) : vA (g * a) = vA g := by
  rw [vA_eq_vA_iff]
  simpa using (SubA A B).inv_mem ha

theorem vB_mul_mem {g b : Monoid.Coprod A B} (hb : b ∈ SubB A B) : vB (g * b) = vB g := by
  rw [vB_eq_vB_iff]
  simpa using (SubB A B).inv_mem hb

/-- The vertex of the coset of `g` on the `s`-side. -/
def vtx (g : Monoid.Coprod A B) (s : Bool) : Vertex A B :=
  bif s then vA g else vB g

@[simp] theorem vtx_true (g : Monoid.Coprod A B) : vtx g true = vA g := rfl
@[simp] theorem vtx_false (g : Monoid.Coprod A B) : vtx g false = vB g := rfl

theorem vtx_eq_vtx_iff {g g' : Monoid.Coprod A B} {s s' : Bool} :
    vtx g s = vtx g' s' ↔ s = s' ∧ g⁻¹ * g' ∈ sideFactor A B s := by
  cases s <;> cases s' <;> simp [sideFactor, vA_ne_vB, vB_ne_vA]

theorem vtx_mul_mem {g a : Monoid.Coprod A B} {s : Bool} (ha : a ∈ sideFactor A B s) :
    vtx (g * a) s = vtx g s := by
  cases s
  · simp only [sideFactor_false] at ha
    simpa using vB_mul_mem (g := g) ha
  · simp only [sideFactor_true] at ha
    simpa using vA_mul_mem (g := g) ha

/-- Every vertex is of the form `vtx g s`. -/
theorem exists_vtx (x : Vertex A B) : ∃ (g : Monoid.Coprod A B) (s : Bool), x = vtx g s := by
  rcases x with c | c
  · obtain ⟨g, rfl⟩ := Quotient.exists_rep c
    exact ⟨g, true, rfl⟩
  · obtain ⟨g, rfl⟩ := Quotient.exists_rep c
    exact ⟨g, false, rfl⟩

/-! ## The quiver structure -/

/-- An arrow of the Bass--Serre tree: a group element `g`, joining the `A`-coset of `g` to the
`B`-coset of `g` (in one of the two directions). -/
abbrev Arrow (x y : Vertex A B) : Type (max u v) :=
  {g : Monoid.Coprod A B // (x = vA g ∧ y = vB g) ∨ (x = vB g ∧ y = vA g)}

instance instQuiver : Quiver (Vertex A B) := ⟨Arrow⟩

theorem arrow_label_eq {x y : Vertex A B} (e : x ⟶ y) :
    (x = vA e.1 ∧ y = vB e.1) ∨ (x = vB e.1 ∧ y = vA e.1) := e.2

/-- The reversed arrow. -/
def arrowReverse {x y : Vertex A B} (e : x ⟶ y) : y ⟶ x :=
  ⟨e.1, e.2.elim (fun h => Or.inr ⟨h.2, h.1⟩) (fun h => Or.inl ⟨h.2, h.1⟩)⟩

@[simp] theorem arrowReverse_val {x y : Vertex A B} (e : x ⟶ y) :
    (arrowReverse e).1 = e.1 := rfl

theorem arrowReverse_arrowReverse {x y : Vertex A B} (e : x ⟶ y) :
    arrowReverse (arrowReverse e) = e := Subtype.ext rfl

instance instHasReverse : Quiver.HasReverse (Vertex A B) where
  reverse' := arrowReverse

instance instHasInvolutiveReverse : Quiver.HasInvolutiveReverse (Vertex A B) :=
  { instHasReverse with inv' := fun e => arrowReverse_arrowReverse e }

/-- There is at most one arrow between two vertices of the tree. -/
theorem subsingleton_arrow (x y : Vertex A B) : Subsingleton (x ⟶ y) := by
  refine ⟨fun e e' => ?_⟩
  have hbot_of : ∀ {z : Monoid.Coprod A B}, z ∈ SubA A B → z ∈ SubB A B → z = 1 := by
    intro z h1 h2
    have hz : z ∈ (⊥ : Subgroup (Monoid.Coprod A B)) := by
      rw [← SubA_inf_SubB]; exact ⟨h1, h2⟩
    simpa using hz
  have key : e.1 = e'.1 := by
    rcases arrow_label_eq e with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
      rcases arrow_label_eq e' with ⟨h1', h2'⟩ | ⟨h1', h2'⟩
    · exact inv_mul_eq_one.mp
        (hbot_of (vA_eq_vA_iff.1 (h1.symm.trans h1')) (vB_eq_vB_iff.1 (h2.symm.trans h2')))
    · exact absurd (h1.symm.trans h1') (vA_ne_vB _ _)
    · exact absurd (h1.symm.trans h1') (vB_ne_vA _ _)
    · exact inv_mul_eq_one.mp
        (hbot_of (vA_eq_vA_iff.1 (h2.symm.trans h2')) (vB_eq_vB_iff.1 (h1.symm.trans h1')))
  exact Subtype.ext key

/-! ## The action of the free product on the tree -/

/-- The action of the free product on the left cosets of the first factor. -/
def smulQuotA (g : Monoid.Coprod A B) :
    Quotient (cosetSetoid (SubA A B)) → Quotient (cosetSetoid (SubA A B)) :=
  Quotient.map (fun h => g * h) (by
    intro a b hab
    have hab' : a⁻¹ * b ∈ SubA A B := hab
    show (g * a)⁻¹ * (g * b) ∈ SubA A B
    simpa [mul_inv_rev, mul_assoc] using hab')

/-- The action of the free product on the left cosets of the second factor. -/
def smulQuotB (g : Monoid.Coprod A B) :
    Quotient (cosetSetoid (SubB A B)) → Quotient (cosetSetoid (SubB A B)) :=
  Quotient.map (fun h => g * h) (by
    intro a b hab
    have hab' : a⁻¹ * b ∈ SubB A B := hab
    show (g * a)⁻¹ * (g * b) ∈ SubB A B
    simpa [mul_inv_rev, mul_assoc] using hab')

@[simp] theorem smulQuotA_mk (g h : Monoid.Coprod A B) :
    smulQuotA g (Quotient.mk _ h) = Quotient.mk _ (g * h) := rfl

@[simp] theorem smulQuotB_mk (g h : Monoid.Coprod A B) :
    smulQuotB g (Quotient.mk _ h) = Quotient.mk _ (g * h) := rfl

@[simp] theorem smulQuotA_one (x : Quotient (cosetSetoid (SubA A B))) : smulQuotA 1 x = x := by
  induction x using Quotient.inductionOn with
  | h a => rw [smulQuotA_mk]; exact Quotient.sound (by simp)

@[simp] theorem smulQuotB_one (x : Quotient (cosetSetoid (SubB A B))) : smulQuotB 1 x = x := by
  induction x using Quotient.inductionOn with
  | h a => rw [smulQuotB_mk]; exact Quotient.sound (by simp)

theorem smulQuotA_mul (g h : Monoid.Coprod A B) (x : Quotient (cosetSetoid (SubA A B))) :
    smulQuotA (g * h) x = smulQuotA g (smulQuotA h x) := by
  induction x using Quotient.inductionOn with
  | h a => rw [smulQuotA_mk, smulQuotA_mk, smulQuotA_mk]; exact Quotient.sound (by simp [mul_assoc])

theorem smulQuotB_mul (g h : Monoid.Coprod A B) (x : Quotient (cosetSetoid (SubB A B))) :
    smulQuotB (g * h) x = smulQuotB g (smulQuotB h x) := by
  induction x using Quotient.inductionOn with
  | h a => rw [smulQuotB_mk, smulQuotB_mk, smulQuotB_mk]; exact Quotient.sound (by simp [mul_assoc])

/-- The action of the free product on the vertex set. -/
def smulFun (g : Monoid.Coprod A B) : Vertex A B → Vertex A B :=
  Sum.elim (fun c => Sum.inl (smulQuotA g c)) (fun c => Sum.inr (smulQuotB g c))

@[simp] theorem smulFun_inl (g : Monoid.Coprod A B)
    (c : Quotient (cosetSetoid (SubA A B))) :
    smulFun g (Sum.inl c) = Sum.inl (smulQuotA g c) := rfl

@[simp] theorem smulFun_inr (g : Monoid.Coprod A B)
    (c : Quotient (cosetSetoid (SubB A B))) :
    smulFun g (Sum.inr c) = Sum.inr (smulQuotB g c) := rfl

instance instMulAction : MulAction (Monoid.Coprod A B) (Vertex A B) where
  smul := smulFun
  one_smul x := by
    rcases x with c | c
    · show smulFun 1 (Sum.inl c) = Sum.inl c
      rw [smulFun_inl, smulQuotA_one]
    · show smulFun 1 (Sum.inr c) = Sum.inr c
      rw [smulFun_inr, smulQuotB_one]
  mul_smul g h x := by
    rcases x with c | c
    · show smulFun (g * h) (Sum.inl c) = smulFun g (smulFun h (Sum.inl c))
      rw [smulFun_inl, smulFun_inl, smulFun_inl, smulQuotA_mul]
    · show smulFun (g * h) (Sum.inr c) = smulFun g (smulFun h (Sum.inr c))
      rw [smulFun_inr, smulFun_inr, smulFun_inr, smulQuotB_mul]

@[simp] theorem smul_vA (g h : Monoid.Coprod A B) : g • vA h = vA (g * h) := rfl
@[simp] theorem smul_vB (g h : Monoid.Coprod A B) : g • vB h = vB (g * h) := rfl

/-! ## The action on arrows -/

/-- The translate of an arrow. -/
def smulArrow (g : Monoid.Coprod A B) {x y : Vertex A B} (e : x ⟶ y) :
    (g • x) ⟶ (g • y) :=
  ⟨g * e.1, by
    rcases arrow_label_eq e with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl
        ⟨(congrArg (fun z => g • z) h1).trans (smul_vA g e.1),
         (congrArg (fun z => g • z) h2).trans (smul_vB g e.1)⟩
    · exact Or.inr
        ⟨(congrArg (fun z => g • z) h1).trans (smul_vB g e.1),
         (congrArg (fun z => g • z) h2).trans (smul_vA g e.1)⟩⟩

@[simp] theorem smulArrow_val (g : Monoid.Coprod A B) {x y : Vertex A B} (e : x ⟶ y) :
    (smulArrow g e).1 = g * e.1 := rfl

@[simp] theorem reverse_val {x y : Vertex A B} (e : x ⟶ y) : (Quiver.reverse e).1 = e.1 := rfl

theorem smulArrow_reverse (g : Monoid.Coprod A B) {x y : Vertex A B} (e : x ⟶ y) :
    smulArrow g (Quiver.reverse e) = Quiver.reverse (smulArrow g e) := by
  haveI := subsingleton_arrow (g • y) (g • x)
  exact Subsingleton.elim _ _

/-- Two `Quiver.Total`s with propositionally equal endpoints and equal arrow labels are equal. -/
theorem Total.ext' {a a' b b' : Vertex A B} (ha : a = a') (hb : b = b') (f : a ⟶ b)
    (f' : a' ⟶ b') (hl : f.1 = f'.1) : Quiver.Total.mk a b f = Quiver.Total.mk a' b' f' := by
  subst ha; subst hb
  exact congrArg (Quiver.Total.mk a b) (Subtype.ext hl)

instance instGraphAction : GraphAction (Monoid.Coprod A B) (Vertex A B) where
  smulTotal g e := Quiver.Total.mk (g • e.left) (g • e.right) (smulArrow g e.hom)
  smulTotal_one e := by
    cases e with
    | mk l r f =>
      refine Total.ext' (one_smul (Monoid.Coprod A B) l) (one_smul (Monoid.Coprod A B) r)
        _ _ (by simp)
  smulTotal_mul g h e := by
    cases e with
    | mk l r f =>
      refine Total.ext' (mul_smul g h l) (mul_smul g h r) _ _ (by simp [mul_assoc])
  smul_left g e := rfl
  smul_right g e := rfl
  smul_reverse g e := by
    cases e with
    | mk l r f =>
      refine Total.ext' rfl rfl _ _ (congrArg Subtype.val (smulArrow_reverse g f))

/-! ## The state of a path

A path in the tree started at a vertex `vtx g s` can be followed in the group: after the arrow
labelled `h` the "state" is `h`.  The steps between consecutive states lie in the factor of the
side at which they are taken. -/

/-- Following an arrow from the vertex `vA g` changes the state by an element of the first
factor. -/
theorem arrow_state {g : Monoid.Coprod A B} {y : Vertex A B} (e : vA g ⟶ y) :
    ∃ a ∈ SubA A B, e.1 = g * a ∧ y = vB (g * a) := by
  rcases arrow_label_eq e with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · refine ⟨g⁻¹ * e.1, vA_eq_vA_iff.1 h1, ?_, ?_⟩
    · show e.1 = g * (g⁻¹ * e.1)
      simp [mul_assoc]
    · exact h2.trans (congrArg vB (by show e.1 = g * (g⁻¹ * e.1); simp [mul_assoc]))
  · exact absurd h1 (vA_ne_vB _ _)

/-- Following an arrow from the vertex `vB g` changes the state by an element of the second
factor. -/
theorem arrow_state' {g : Monoid.Coprod A B} {y : Vertex A B} (e : vB g ⟶ y) :
    ∃ b ∈ SubB A B, e.1 = g * b ∧ y = vA (g * b) := by
  rcases arrow_label_eq e with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact absurd h1 (vB_ne_vA _ _)
  · refine ⟨g⁻¹ * e.1, vB_eq_vB_iff.1 h1, ?_, ?_⟩
    · show e.1 = g * (g⁻¹ * e.1)
      simp [mul_assoc]
    · exact h2.trans (congrArg vA (by show e.1 = g * (g⁻¹ * e.1); simp [mul_assoc]))

end Work.ORBassSerre.CoprodTree
