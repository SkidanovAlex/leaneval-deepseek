/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The Bass--Serre graph of `A ∗ B` is connected

The quiver `Work.ORBassSerre.CoprodTree.Vertex A B` (see `Defs.lean`) has as vertices the left
cosets of the two factors `SubA`, `SubB` of the free product `A ∗ B`, and as arrows the group
elements `g`, the arrow labelled `g` joining the `A`-coset of `g` to its `B`-coset.

This file proves that this quiver is *connected*: between any two vertices there is a
(directed) path.  The Bass--Serre tree itself is proved to be a tree elsewhere; connectedness is
the part of that statement needed for the applications.

## Strategy

Every vertex is the translate of one of the two base vertices `vA 1`, `vB 1` by an element of the
free product, but translating a path by a group element is not available for free, so we argue
directly at the group level.  Put

`reachA g := Quiver.Reachable (vA 1) (vA g)`.

The main point (`reachA_self`) is that `reachA g` holds for *every* `g`.  Since
`SubA ∪ SubB` generates `A ∗ B`, it suffices to check that the relation
`p g := ∀ h, reachA h → reachA (h * g)` holds on generators and is multiplicative:
* right multiplication by `s ∈ SubA` keeps the vertex `vA (h * s) = vA h` fixed;
* right multiplication by `s ∈ SubB` moves `vA h → vB h → vA (h * s)` along two genuine arrows
  (the second arrow has source `vB (h * s) = vB h` because `s ∈ SubB`).
Consequently `reachA g` holds for all `g ∈ Subgroup.closure (SubA ∪ SubB) = ⊤`, i.e. for all `g`.

Finishing: from `vA 1` one reaches `vA g` (`reachA_self`) and `vB g` (one further arrow), so every
vertex is reachable from the base vertex `vA 1`; reversing one path and concatenating gives a path
between any two vertices.
-/
import Mathlib
import Submission.Work.ORBassSerre.CoprodTree.Defs

namespace Work.ORBassSerre.CoprodTree

universe u v

section

variable {A : Type u} {B : Type v} [Group A] [Group B]

/-! ## Reachability from the base vertex `vA 1` -/

/-- `reachA g` holds when the vertex `vA g` can be reached from the base vertex `vA 1`. -/
def reachA (g : Monoid.Coprod A B) : Prop :=
  Quiver.Reachable (vA (1 : Monoid.Coprod A B)) (vA g)

/-- Reachability of `vA` depends only on the vertex, not on its label. -/
theorem reachA_congr {g g' : Monoid.Coprod A B} (h : vA g = vA g') : reachA g → reachA g' :=
  fun hg =>
    Eq.mp (congrArg (fun z => Quiver.Reachable (vA (1 : Monoid.Coprod A B)) z) h) hg

/-- Multiplying on the right by an element of the first factor does not move the vertex `vA`. -/
theorem reachA_mul_mem_SubA {g s : Monoid.Coprod A B} (hs : s ∈ SubA A B) (hg : reachA g) :
    reachA (g * s) :=
  reachA_congr (vA_mul_mem (g := g) hs).symm hg

/-- Multiplying on the right by an element of the second factor moves `vA g` to `vA (g * s)`
along the two arrows `vA g → vB g → vA (g * s)`. -/
theorem reachA_mul_mem_SubB {g s : Monoid.Coprod A B} (hs : s ∈ SubB A B) (hg : reachA g) :
    reachA (g * s) := by
  have h1 : Quiver.Reachable (vA g) (vB g) :=
    Quiver.Hom.reachable (⟨g, Or.inl ⟨rfl, rfl⟩⟩ : vA g ⟶ vB g)
  have h2 : Quiver.Reachable (vB g) (vA (g * s)) := by
    have e : vB (g * s) ⟶ vA (g * s) := ⟨g * s, Or.inr ⟨rfl, rfl⟩⟩
    have hv : vB (g * s) = vB g := vB_mul_mem (g := g) hs
    exact Eq.mp (congrArg (fun z => Quiver.Reachable z (vA (g * s))) hv)
      (Quiver.Hom.reachable e)
  exact Quiver.Reachable.trans hg (Quiver.Reachable.trans h1 h2)

/-- The two factors generate the free product, as a submonoid. -/
theorem submonoid_closure_SubA_union_SubB :
    Submonoid.closure ((SubA A B : Set (Monoid.Coprod A B)) ∪ (SubB A B : Set _)) = ⊤ := by
  have hS : (SubA A B : Set (Monoid.Coprod A B)) ∪ (SubB A B : Set _)
      = Set.range (Monoid.Coprod.inl : A →* Monoid.Coprod A B)
        ∪ Set.range (Monoid.Coprod.inr : B →* Monoid.Coprod A B) := by
    ext x
    simp [SubA, SubB]
  rw [hS]
  exact Monoid.Coprod.mclosure_range_inl_union_inr

/-- **Every** vertex of the `A`-side is reachable from the base vertex `vA 1`. -/
theorem reachA_self (g : Monoid.Coprod A B) : reachA g := by
  have hmem : g ∈ Submonoid.closure ((SubA A B : Set (Monoid.Coprod A B)) ∪ (SubB A B : Set _)) := by
    rw [submonoid_closure_SubA_union_SubB]
    exact Submonoid.mem_top g
  have key : ∀ h : Monoid.Coprod A B, reachA h → reachA (h * g) :=
    Submonoid.closure_induction
      (s := (SubA A B : Set (Monoid.Coprod A B)) ∪ (SubB A B : Set _))
      (motive := fun g _ => ∀ h : Monoid.Coprod A B, reachA h → reachA (h * g))
      (fun x hx h hh => by
        rcases hx with hx | hx
        · exact reachA_mul_mem_SubA hx hh
        · exact reachA_mul_mem_SubB hx hh)
      (fun h hh => by
        refine reachA_congr ?_ hh
        rw [mul_one])
      (fun x y _ _ ihx ihy h hh => by
        refine reachA_congr ?_ (ihy (h * x) (ihx h hh))
        rw [mul_assoc])
      hmem
  have h1 : reachA (1 : Monoid.Coprod A B) := Quiver.Reachable.refl _
  refine reachA_congr ?_ (key 1 h1)
  rw [one_mul]

/-! ## Every vertex is reachable from `vA 1`, and the graph is connected -/

/-- The reverse of a path. -/
def pathReverse : ∀ {x y : Vertex A B}, Quiver.Path x y → Quiver.Path y x
  | _, _, .nil => .nil
  | _, _, .cons p e => (Quiver.reverse e).toPath.comp (pathReverse p)

/-- Every vertex is reachable from the base vertex `vA 1`. -/
theorem reachable_vA_one (x : Vertex A B) :
    Nonempty (Quiver.Path (vA (1 : Monoid.Coprod A B)) x) := by
  obtain ⟨g, s, rfl⟩ := exists_vtx x
  cases s
  · obtain ⟨p⟩ := reachA_self g
    exact ⟨Quiver.Path.cons p ⟨g, Or.inl ⟨rfl, rfl⟩⟩⟩
  · exact reachA_self g

end

theorem connected_vertex {A : Type u} {B : Type v} [Group A] [Group B] (x y : Work.ORBassSerre.CoprodTree.Vertex A B) : Nonempty (Quiver.Path x y) := by
  obtain ⟨p⟩ := reachable_vA_one x
  obtain ⟨q⟩ := reachable_vA_one y
  exact ⟨(pathReverse p).comp q⟩

end Work.ORBassSerre.CoprodTree
