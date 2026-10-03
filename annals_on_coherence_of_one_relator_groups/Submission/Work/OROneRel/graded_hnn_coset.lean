import Mathlib
import Submission.Work.ORBassSerre.Action.Basic

/-!
# The Bass--Serre graph of the pair `(H, t)`

Given a group `G`, a subgroup `H ≤ G` and an element `t : G`, the *coset graph* of the pair has
vertex set the left cosets `G ⧸ H` and (undirected) edges the pairs `{gH, gtH}`.  This file sets up

* the quiver structure on `G ⧸ H` (arrows are edges with a chosen direction, labels are
  proof-irrelevant, so there is at most one arrow between two vertices),
* the action of `G` on the cosets and on the arrows (a `GraphAction`),
* the fundamental edge `baseC ⟶ t⁻¹ • baseC`,

for which `Work.ORBassSerre.Action.Structure.hnn_reduced_word_ne_one` is applicable as soon as the
graph is a tree and the action is without inversions.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.OROneRel
namespace GradedHNN

universe u

variable {G : Type u} [Group G]

#check @QuotientGroup.leftRel
#check @QuotientGroup.eq
#check @QuotientGroup.leftRel_apply

/-- The vertex set of the coset graph: the left cosets of `H` (the parameter `t` only serves to
carry the quiver structure in the type). -/
abbrev Coset (H : Subgroup G) (_t : G) : Type u := G ⧸ H

/-- The coset of an element. -/
abbrev cmk (H : Subgroup G) (_t : G) (g : G) : Coset H _t := QuotientGroup.mk g

theorem cmk_eq_iff (H : Subgroup G) (t : G) {a b : G} :
    cmk H t a = cmk H t b ↔ a⁻¹ * b ∈ H :=
  QuotientGroup.eq

theorem cmk_mul_mem (H : Subgroup G) (t : G) (g : G) {h : G} (hh : h ∈ H) :
    cmk H t (g * h) = cmk H t g := by
  rw [cmk_eq_iff]
  have h1 : (g * h)⁻¹ * g = h⁻¹ := by group
  rw [h1]
  exact H.inv_mem hh

/-- The adjacency relation: `x` and `y` are joined when `{x,y} = {gH, gtH}` for some `g`. -/
def adjC (H : Subgroup G) (t : G) (x y : Coset H t) : Prop :=
  ∃ g : G, (x = cmk H t g ∧ y = cmk H t (g * t)) ∨ (y = cmk H t g ∧ x = cmk H t (g * t))

theorem adjC_symm (H : Subgroup G) (t : G) {x y : Coset H t} (h : adjC H t x y) :
    adjC H t y x := by
  obtain ⟨g, h | h⟩ := h
  · exact ⟨g, Or.inr h⟩
  · exact ⟨g, Or.inl h⟩

/-- The quiver structure: arrows are the directed edges, with proof-irrelevant labels. -/
@[reducible] instance instQuiverCoset (H : Subgroup G) (t : G) : Quiver (Coset H t) :=
  ⟨fun x y => PLift (adjC H t x y)⟩

instance instSubsingletonHomCoset (H : Subgroup G) (t : G) (x y : Coset H t) :
    Subsingleton (x ⟶ y) :=
  ⟨fun a b => Subsingleton.elim (α := PLift (adjC H t x y))
    (show PLift (adjC H t x y) from a) (show PLift (adjC H t x y) from b)⟩

instance instHasReverseCoset (H : Subgroup G) (t : G) : Quiver.HasReverse (Coset H t) where
  reverse' := fun {_ _} e => ⟨adjC_symm H t e.down⟩

instance instHasInvolutiveReverseCoset (H : Subgroup G) (t : G) :
    Quiver.HasInvolutiveReverse (Coset H t) where
  inv' := fun {_ _} e => Subsingleton.elim _ _

/-- Two `Quiver.Total`s with equal endpoints are equal (labels are proof-irrelevant). -/
theorem total_ext_coset (H : Subgroup G) (t : G) {a a' b b' : Coset H t} (ha : a = a') (hb : b = b')
    (f : a ⟶ b) (f' : a' ⟶ b') : Quiver.Total.mk a b f = Quiver.Total.mk a' b' f' := by
  subst ha; subst hb
  exact congrArg (Quiver.Total.mk a b) (Subsingleton.elim f f')

/-- The base vertex: the coset `H`. -/
abbrev baseC (H : Subgroup G) (t : G) : Coset H t := cmk H t 1

theorem smul_cmk (H : Subgroup G) (t : G) (g x : G) : g • cmk H t x = cmk H t (g * x) := rfl

/-- The action of `G` on the coset graph preserves adjacency. -/
theorem smul_adjC (H : Subgroup G) (t : G) (g : G) {x y : Coset H t} (h : adjC H t x y) :
    adjC H t (g • x) (g • y) := by
  obtain ⟨a, h | h⟩ := h
  · refine ⟨g * a, Or.inl ⟨?_, ?_⟩⟩
    · rw [h.1, smul_cmk]
    · rw [h.2, smul_cmk, mul_assoc]
  · refine ⟨g * a, Or.inr ⟨?_, ?_⟩⟩
    · rw [h.1, smul_cmk]
    · rw [h.2, smul_cmk, mul_assoc]

theorem smul_adjC_iff (H : Subgroup G) (t : G) (g : G) {x y : Coset H t} :
    adjC H t x y ↔ adjC H t (g • x) (g • y) := by
  constructor
  · exact smul_adjC H t g
  · intro h
    have := smul_adjC H t g⁻¹ h
    simpa only [inv_smul_smul] using this

/-- The translate of an arrow. -/
def smulArrowC (H : Subgroup G) (t : G) (g : G) {x y : Coset H t} (e : x ⟶ y) :
    (g • x) ⟶ (g • y) :=
  ⟨(smul_adjC_iff H t g).mp e.down⟩

instance instGraphActionCoset (H : Subgroup G) (t : G) :
    Work.ORBassSerre.GraphAction G (Coset H t) where
  smulTotal g e := Quiver.Total.mk (g • e.left) (g • e.right) (smulArrowC H t g e.hom)
  smulTotal_one e := by
    cases e with
    | mk l r f => exact total_ext_coset H t (one_smul G l) (one_smul G r) _ _
  smulTotal_mul g g' e := by
    cases e with
    | mk l r f => exact total_ext_coset H t (mul_smul g g' l) (mul_smul g g' r) _ _
  smul_left g e := rfl
  smul_right g e := rfl
  smul_reverse g e := by
    cases e with
    | mk l r f => exact total_ext_coset H t rfl rfl _ _

/-- The fundamental edge `baseC ⟶ t⁻¹ • baseC`, as an arrow. -/
def edgeArrowC (H : Subgroup G) (t : G) : baseC H t ⟶ t⁻¹ • baseC H t :=
  ⟨t⁻¹, Or.inr ⟨by
    show t⁻¹ • baseC H t = cmk H t t⁻¹
    rw [show t⁻¹ • baseC H t = cmk H t (t⁻¹ * 1) from rfl, mul_one], by
    show cmk H t 1 = cmk H t (t⁻¹ * t)
    rw [cmk_eq_iff]
    rw [show (1 : G)⁻¹ * (t⁻¹ * t) = 1 from by group]
    exact H.one_mem⟩⟩

/-- The fundamental edge `baseC ⟶ t⁻¹ • baseC`, as an element of `Quiver.Total`. -/
def edgeC (H : Subgroup G) (t : G) : Quiver.Total (Coset H t) :=
  Quiver.Total.mk (baseC H t) (t⁻¹ • baseC H t) (edgeArrowC H t)

end GradedHNN
end Work.OROneRel
