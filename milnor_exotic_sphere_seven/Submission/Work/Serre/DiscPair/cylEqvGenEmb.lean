import Mathlib
import Submission.Work.Serre.DiscPair.cylPreimageDefs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The gluing equivalence of the restricted mapping cylinder is the one induced by `cylEmb`

For a continuous map `q : C(X, Γ')` and a set `S ⊆ Γ'`, the presenting disjoint union
`(↥(q ⁻¹' S) × I) ⊕ ↥S` of the mapping cylinder of the restricted map `qS q S : q ⁻¹' S → S`
sits inside the presenting disjoint union `(X × I) ⊕ Γ'` of the mapping cylinder of `q` along the
obvious map `cylEmb q S`.  This file shows that the gluing equivalences agree:

`EqvGen (cylRel (qS q S)) a b ↔ EqvGen (cylRel q) (cylEmb q S a) (cylEmb q S b)`.

The mathematical content is the following description of the equivalence classes of `cylRel f`
(the gluing relation identifies `(p, 1)` with `f p`): the class of a point `(p, t)` of the cylinder
with `t ≠ 1` is a singleton, while the class of `(p, 1)` (and of `f p`) is the set of all `(p', 1)`
and `f p'` with `f p' = f p`.  This "normal form" map is `cylCl f` below, which collapses
`(p, 1) ↦ f p` and fixes everything else; `eqvGen_cylRel_iff` says precisely that two points are
glued iff they have the same normal form.  The normal form of a point of the sub-cylinder
`(↥(q ⁻¹' S) × I) ⊕ ↥S` is the same whether it is computed in `cyl q` or in `cyl (qS q S)`
(lemma `cylEqvGenEmb_key`), because `q p ∈ S` for every `p ∈ q ⁻¹' S`; since `cylEmb q S` is
injective this gives the requested equivalence.
-/

open scoped Topology unitInterval

namespace Work.Serre.DiscPair

noncomputable section

variable {P Y : Type} [TopologicalSpace P] [TopologicalSpace Y]

/-- The **normal form** of a point of the presenting disjoint union of the mapping cylinder of `f`:
the top circle of the cylinder is pushed to the target, everything else is kept.  Two points of the
disjoint union are glued in `cyl f` exactly when their normal forms agree (`eqvGen_cylRel_iff`). -/
def cylCl (f : C(P, Y)) : (P × unitInterval) ⊕ Y → (P × unitInterval) ⊕ Y :=
  Sum.elim (fun z => if z.2 = 1 then Sum.inr (f z.1) else Sum.inl z) Sum.inr

@[simp] lemma cylCl_inl_one (f : C(P, Y)) (p : P) :
    cylCl f (Sum.inl (p, 1)) = Sum.inr (f p) := by
  show (if ((1 : unitInterval) = 1) then Sum.inr (f p) else Sum.inl (p, 1)) = Sum.inr (f p)
  rw [if_pos rfl]

@[simp] lemma cylCl_inl_of_ne (f : C(P, Y)) (p : P) {t : unitInterval} (ht : t ≠ 1) :
    cylCl f (Sum.inl (p, t)) = Sum.inl (p, t) := by
  show (if (t = 1) then Sum.inr (f p) else Sum.inl (p, t)) = Sum.inl (p, t)
  rw [if_neg ht]

@[simp] lemma cylCl_inr (f : C(P, Y)) (y : Y) : cylCl f (Sum.inr y) = Sum.inr y := rfl

/-- **The classes of the gluing relation are the fibres of the normal form**: two points of the
presenting disjoint union are glued in the mapping cylinder `cyl f` exactly when their normal forms
`cylCl f` agree. -/
theorem eqvGen_cylRel_iff (f : C(P, Y)) (u v : (P × unitInterval) ⊕ Y) :
    Relation.EqvGen (cylRel f) u v ↔ cylCl f u = cylCl f v := by
  constructor
  · intro h
    induction h with
    | rel a b hab =>
        obtain ⟨p, rfl, rfl⟩ := hab
        rw [cylCl_inl_one, cylCl_inr]
    | refl a => rfl
    | symm a b _ ih => exact ih.symm
    | trans a b c _ _ ih1 ih2 => exact ih1.trans ih2
  · intro h
    have key : ∀ w : (P × unitInterval) ⊕ Y, Relation.EqvGen (cylRel f) w (cylCl f w) := by
      intro w
      match w with
      | Sum.inl z =>
          obtain ⟨p, t⟩ := z
          by_cases ht : t = 1
          · subst ht
            rw [cylCl_inl_one]
            exact Relation.EqvGen.rel _ _ ⟨p, rfl, rfl⟩
          · rw [cylCl_inl_of_ne f p ht]
            exact Relation.EqvGen.refl _
      | Sum.inr y => exact Relation.EqvGen.refl _
    exact Relation.EqvGen.trans u (cylCl f u) v (key u) (h ▸ (key v).symm)

variable {X Γ' : Type} [TopologicalSpace X] [TopologicalSpace Γ']

/-- The normal form `cylCl q` of a point of the sub-cylinder of `cyl (qS q S)` coincides with the
normal form of its image in `cyl q` under `cylEmb`. -/
lemma cylEqvGenEmb_key (q : C(X, Γ')) (S : Set Γ') :
    ∀ a : (↥(q ⁻¹' S) × unitInterval) ⊕ ↥S,
      cylCl q (cylEmb q S a) = cylEmb q S (cylCl (qS q S) a) := by
  rintro (⟨⟨x, hx⟩, t⟩ | ⟨y, hy⟩)
  · by_cases ht : t = 1
    · subst ht
      rw [cylEmb_inl,
        show cylCl (qS q S) (Sum.inl ((⟨x, hx⟩ : ↥(q ⁻¹' S)), (1 : unitInterval)))
            = Sum.inr ((qS q S) ⟨x, hx⟩) from cylCl_inl_one _ _,
        qS_apply, cylEmb_inr,
        show cylCl q (Sum.inl ((x, (1 : unitInterval)) : X × unitInterval)) = Sum.inr (q x)
          from cylCl_inl_one _ _]
    · rw [cylEmb_inl,
        show cylCl (qS q S) (Sum.inl ((⟨x, hx⟩ : ↥(q ⁻¹' S)), t))
            = Sum.inl (⟨x, hx⟩, t) from cylCl_inl_of_ne _ _ ht,
        cylEmb_inl,
        show cylCl q (Sum.inl ((x, t) : X × unitInterval)) = Sum.inl (x, t)
          from cylCl_inl_of_ne _ _ ht]
  · rw [cylEmb_inr,
      show cylCl (qS q S) (Sum.inr (⟨y, hy⟩ : ↥S)) = Sum.inr ⟨y, hy⟩ from cylCl_inr _ _,
      cylEmb_inr,
      show cylCl q (Sum.inr y) = Sum.inr y from cylCl_inr _ _]

/-- The map on presenting disjoint unions induced by the restriction of `q` to `q ⁻¹' S` is
injective. -/
lemma cylEmb_injective (q : C(X, Γ')) (S : Set Γ') :
    Function.Injective (cylEmb q S) := by
  rintro (⟨⟨x, hx⟩, t⟩ | ⟨y, hy⟩) (⟨⟨x', hx'⟩, t'⟩ | ⟨y', hy'⟩) h
  · simp only [cylEmb_inl, Sum.inl.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl
  · simp only [cylEmb_inl, cylEmb_inr] at h
    exact absurd h Sum.inl_ne_inr
  · simp only [cylEmb_inl, cylEmb_inr] at h
    exact absurd h Sum.inr_ne_inl
  · simp only [cylEmb_inr, Sum.inr.injEq] at h
    obtain rfl := h
    rfl

theorem cylEqvGenEmb {X Γ' : Type} [TopologicalSpace X] [TopologicalSpace Γ']
    (q : C(X, Γ')) (S : Set Γ') (a b : (↥(q ⁻¹' S) × unitInterval) ⊕ ↥S) :
    Relation.EqvGen (Work.Serre.cylRel (Work.Serre.DiscPair.qS q S)) a b ↔
      Relation.EqvGen (Work.Serre.cylRel q) (Work.Serre.DiscPair.cylEmb q S a)
        (Work.Serre.DiscPair.cylEmb q S b) := by
  rw [eqvGen_cylRel_iff (qS q S) a b, eqvGen_cylRel_iff q (cylEmb q S a) (cylEmb q S b),
    cylEqvGenEmb_key q S a, cylEqvGenEmb_key q S b]
  exact ⟨fun h => congrArg (cylEmb q S) h, fun h => cylEmb_injective q S h⟩

end

end Work.Serre.DiscPair
