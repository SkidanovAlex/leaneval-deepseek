/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Adjunction spaces along a homeomorphism of closed subsets

Given topological spaces `X`, `Y`, closed subsets `s ⊆ X`, `t ⊆ Y` and an identification
`h : s ≃ₜ t`, the adjunction space is the quotient of the coproduct `X ⊕ Y` that identifies
each `x ∈ s` with `h x ∈ t` and nothing else.  This is the presentation of the gluing `~₃` of
the Ratcliffe--Tschantz construction: `X` is the hyperbolic piece `M̄`, `Y := Σ v, W v` the
filling pieces, `s` the union of the truncation tori and `t` the corresponding boundary of the
filling pieces.

The second piece may itself be a finite coproduct, `Y := Σ v, W v` (with each `W v` compact
Hausdorff and `t` the union of the parts `t v`), which is the multi-cusp situation of `M̂`; the
setoid, the closedness of its graph and the Hausdorffness of the quotient are insensitive to the
shape of `Y`.

This file contains the glue data and its setoid.  The main results about it are

* `Work.QuotientT2.glueData_isClosed_relGraph` (the graph is closed),
* `Work.QuotientT2.glueData_t2Space_quotient` (the quotient is Hausdorff),
* `Work.QuotientT2.isOpen_quotient_iff_pieces` (openness criterion, in `Basic`).
-/
import Mathlib
import Submission.Work.QuotientT2.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Set Topology Function

namespace Work.QuotientT2

universe u v

/-- Glue data for an adjunction space: a homeomorphism `h` between closed subsets `s ⊆ X` and
`t ⊆ Y`. -/
structure GlueData (X : Type u) (Y : Type v) [TopologicalSpace X] [TopologicalSpace Y] where
  /-- The closed subset of `X` along which we glue. -/
  s : Set X
  /-- The closed subset of `Y` along which we glue. -/
  t : Set Y
  /-- `s` is closed. -/
  s_closed : IsClosed s
  /-- `t` is closed. -/
  t_closed : IsClosed t
  /-- The identification `s ≃ₜ t`. -/
  h : s ≃ₜ t

namespace GlueData

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

/-- The relation on the coproduct `X ⊕ Y` identifying `x ∈ s` with `h x`, and nothing else. -/
def Rel (G : GlueData X Y) (a b : X ⊕ Y) : Prop :=
  (∃ x : G.s, a = Sum.inl (x : X) ∧ b = Sum.inr ((G.h x : G.t) : Y)) ∨
    (∃ y : G.t, a = Sum.inr (y : Y) ∧ b = Sum.inl ((G.h.symm y : G.s) : X)) ∨ a = b

variable (G : GlueData X Y)

theorem rel_iff (a b : X ⊕ Y) :
    G.Rel a b ↔ (∃ x : G.s, a = Sum.inl (x : X) ∧ b = Sum.inr ((G.h x : G.t) : Y)) ∨
      (∃ y : G.t, a = Sum.inr (y : Y) ∧ b = Sum.inl ((G.h.symm y : G.s) : X)) ∨ a = b :=
  Iff.rfl

/-- A point of `s` is identified with its image in `t`. -/
theorem rel_inl_inr (x : G.s) :
    G.Rel (Sum.inl (x : X)) (Sum.inr ((G.h x : G.t) : Y)) :=
  Or.inl ⟨x, rfl, rfl⟩

/-- The inverse identification. -/
theorem rel_inr_inl (y : G.t) :
    G.Rel (Sum.inr (y : Y)) (Sum.inl ((G.h.symm y : G.s) : X)) :=
  Or.inr (Or.inl ⟨y, rfl, rfl⟩)

theorem rel_refl (a : X ⊕ Y) : G.Rel a a := Or.inr (Or.inr rfl)

theorem rel_symm {a b : X ⊕ Y} (h : G.Rel a b) : G.Rel b a := by
  rcases h with ⟨x, rfl, rfl⟩ | ⟨y, rfl, rfl⟩ | rfl
  · exact Or.inr (Or.inl ⟨G.h x, rfl, by simp⟩)
  · exact Or.inl ⟨G.h.symm y, rfl, by simp⟩
  · exact Or.inr (Or.inr rfl)

theorem rel_trans {a b c : X ⊕ Y} (h1 : G.Rel a b) (h2 : G.Rel b c) : G.Rel a c := by
  rcases h1 with ⟨x, rfl, rfl⟩ | ⟨y, rfl, rfl⟩ | rfl
  · rcases h2 with ⟨z, h2, h3⟩ | ⟨z, h2, h3⟩ | rfl
    · exact absurd h2 (by simp)
    · have hz : (G.h x : G.t) = z := Subtype.ext (by simpa using h2)
      rw [← hz] at h3
      rw [h3]
      exact Or.inr (Or.inr (by rw [Homeomorph.symm_apply_apply]))
    · exact Or.inl ⟨x, rfl, rfl⟩
  · rcases h2 with ⟨z, h2, h3⟩ | ⟨z, h2, h3⟩ | rfl
    · have hz : z = (G.h.symm y : G.s) := (Subtype.ext (by simpa using h2)).symm
      rw [hz] at h3
      rw [h3]
      exact Or.inr (Or.inr (by rw [Homeomorph.apply_symm_apply]))
    · exact absurd h2 (by simp)
    · exact Or.inr (Or.inl ⟨y, rfl, rfl⟩)
  · exact h2

/-- The equivalence relation on `X ⊕ Y` defining the adjunction space. -/
def setoid (G : GlueData X Y) : Setoid (X ⊕ Y) where
  r := G.Rel
  iseqv := ⟨G.rel_refl, fun h => G.rel_symm h, fun h1 h2 => G.rel_trans h1 h2⟩

theorem setoid_iff {a b : X ⊕ Y} : G.setoid a b ↔ G.Rel a b := Iff.rfl

/-- On the piece `s` the relation is exactly the identification `h`. -/
theorem rel_inl_inl {x x' : X} : G.Rel (Sum.inl x) (Sum.inl x') ↔ x = x' := by
  constructor
  · rintro (⟨z, h1, h2⟩ | ⟨z, h1, h2⟩ | h)
    · exact absurd h2 (by simp)
    · exact absurd h1 (by simp)
    · simpa using h
  · intro h; rw [h]; exact G.rel_refl _

theorem rel_inr_inr {y y' : Y} : G.Rel (Sum.inr y) (Sum.inr y') ↔ y = y' := by
  constructor
  · rintro (⟨z, h1, h2⟩ | ⟨z, h1, h2⟩ | h)
    · exact absurd h1 (by simp)
    · exact absurd h2 (by simp)
    · simpa using h
  · intro h; rw [h]; exact G.rel_refl _

end GlueData

/-- Glue data from a homeomorphism between closed subsets. -/
def glueDataOfHomeomorph {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    {s : Set X} {t : Set Y} (hs : IsClosed s) (ht : IsClosed t) (h : s ≃ₜ t) : GlueData X Y :=
  ⟨s, t, hs, ht, h⟩

/-- The name used in the blueprint for `GlueData.setoid`: the relation of the adjunction space
along a homeomorphism of closed subsets. -/
def adjunctionSetoid {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (G : GlueData X Y) : Setoid (X ⊕ Y) :=
  G.setoid

end Work.QuotientT2
