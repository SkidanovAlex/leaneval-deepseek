/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Quotients by relations with closed graph

* `Work.QuotientT2.relGraph r` : the graph `{(x, y) | r x y}` of a setoid relation.
* `isClosed_class_of_isClosed_relGraph` : classes are closed when the graph is.
* `isClosed_saturation` : if `X` is compact Hausdorff, the saturation of a closed set is closed.
* `isClosedMap_quotient_mk_of_isClosed_relGraph` : the quotient map is closed.
* `t2_quotient_of_closed` : the quotient of a **compact Hausdorff** space by a relation with
  closed graph is Hausdorff.
* Openness/closedness criteria for the quotient topology on a coproduct of pieces.

The intended application (Ratcliffe--Tschantz) is that the quotient of a compact polytope by
finitely many identifications along closed facets is Hausdorff: the graph of the relation is then
a finite union of graphs of continuous maps on closed sets.
-/
import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Set Topology Function

namespace Work.QuotientT2

universe u v w

section Graph

variable {X : Type u} [TopologicalSpace X]

/-- The graph of the relation of a setoid `r`, as a subset of `X × X`. -/
def relGraph (r : Setoid X) : Set (X × X) := {p | r p.1 p.2}

@[simp] theorem mem_relGraph {r : Setoid X} {x y : X} : (x, y) ∈ relGraph r ↔ r x y := Iff.rfl

variable {r : Setoid X}

/-- A set is open in the quotient iff its preimage is open. -/
theorem isOpen_quotient_iff_preimage {s : Set (Quotient r)} :
    IsOpen s ↔ IsOpen (Quotient.mk r ⁻¹' s) :=
  isOpen_coinduced (f := Quotient.mk r)

/-- A set is closed in the quotient iff its preimage is closed. -/
theorem isClosed_quotient_iff_preimage {s : Set (Quotient r)} :
    IsClosed s ↔ IsClosed (Quotient.mk r ⁻¹' s) :=
  isClosed_coinduced (f := Quotient.mk r)

/-- A map out of a quotient is continuous iff its composite with the quotient map is. -/
theorem continuous_quotient_iff {Y : Type v} [TopologicalSpace Y] {f : Quotient r → Y} :
    Continuous f ↔ Continuous (f ∘ Quotient.mk r) :=
  isQuotientMap_quotient_mk'.continuous_iff


/-- An equivalence class of a relation with closed graph is closed. -/
theorem isClosed_class_of_isClosed_relGraph (hr : IsClosed (relGraph r)) (x : X) :
    IsClosed {y | r y x} :=
  hr.preimage (continuous_id.prodMk continuous_const)

/-- The `r`-class of `x` is the fibre of the quotient map. -/
theorem preimage_singleton_quotient_mk (x : X) :
    Quotient.mk r ⁻¹' {Quotient.mk r x} = {y | r y x} := by
  ext y
  simp [Quotient.eq]

/-- The class of `x`, as a closed set, when the graph of `r` is closed. -/
theorem isClosed_preimage_singleton_quotient_mk (hr : IsClosed (relGraph r)) (x : X) :
    IsClosed (Quotient.mk r ⁻¹' {Quotient.mk r x}) := by
  rw [preimage_singleton_quotient_mk]
  exact isClosed_class_of_isClosed_relGraph hr x

/-- The saturation of a set, as a set of representatives. -/
def saturation (r : Setoid X) (s : Set X) : Set X := {x | ∃ y ∈ s, r x y}

@[simp] theorem mem_saturation {s : Set X} {x : X} :
    x ∈ saturation r s ↔ ∃ y ∈ s, r x y := Iff.rfl

theorem self_subset_saturation (s : Set X) : s ⊆ saturation r s :=
  fun x hx => ⟨x, hx, r.refl x⟩

theorem preimage_image_quotient_mk (s : Set X) :
    Quotient.mk r ⁻¹' (Quotient.mk r '' s) = saturation r s := by
  ext x
  constructor
  · rintro ⟨y, hy, hxy⟩
    exact ⟨y, hy, r.symm (Quotient.exact hxy)⟩
  · rintro ⟨y, hy, hxy⟩
    exact ⟨y, hy, Quotient.sound (r.symm hxy)⟩

/-- The saturation of `s` is the preimage of the image of `s` in the quotient. -/
theorem saturation_eq_preimage (s : Set X) :
    saturation r s = Quotient.mk r ⁻¹' (Quotient.mk r '' s) :=
  (preimage_image_quotient_mk s).symm

/-- If `X` is compact Hausdorff and the graph of `r` is closed, the saturation of a closed set
is closed.  (The saturation is the image of the closed set `relGraph r ∩ (univ × s)` under the
first projection.) -/
theorem isClosed_saturation [CompactSpace X] [T2Space X] (hr : IsClosed (relGraph r))
    {s : Set X} (hs : IsClosed s) : IsClosed (saturation r s) := by
  have hK : IsCompact (relGraph r ∩ ((Set.univ : Set X) ×ˢ s)) :=
    (hr.inter (isClosed_univ.prod hs)).isCompact
  have h2 : IsClosed (Prod.fst '' (relGraph r ∩ ((Set.univ : Set X) ×ˢ s))) :=
    (hK.image continuous_fst).isClosed
  convert h2 using 1
  ext x
  constructor
  · rintro ⟨y, hy, hxy⟩
    exact ⟨(x, y), ⟨hxy, trivial, hy⟩, rfl⟩
  · rintro ⟨p, ⟨hp, -, hp2⟩, rfl⟩
    exact ⟨p.2, hp2, hp⟩

/-- The image of a set in the quotient is open iff its saturation is open.  (A *saturated* open
set therefore has an open image, without any openness property of the quotient map.) -/
theorem isOpen_image_quotient_mk_iff {s : Set X} :
    IsOpen (Quotient.mk r '' s) ↔ IsOpen (saturation r s) := by
  rw [isOpen_quotient_iff_preimage, preimage_image_quotient_mk]

/-- The image of a saturated open set is open in the quotient. -/
theorem isOpen_image_quotient_mk_of_saturation_eq {s : Set X} (hs : IsOpen s)
    (h : saturation r s = s) : IsOpen (Quotient.mk r '' s) := by
  rw [isOpen_image_quotient_mk_iff, h]
  exact hs

/-- The image of a set in the quotient is closed iff its saturation is closed. -/
theorem isClosed_image_quotient_mk_iff {s : Set X} :
    IsClosed (Quotient.mk r '' s) ↔ IsClosed (saturation r s) := by
  rw [isClosed_quotient_iff_preimage, preimage_image_quotient_mk]

/-- **The quotient map of a compact Hausdorff space by a relation with closed graph is closed.** -/
theorem isClosedMap_quotient_mk_of_isClosed_relGraph [CompactSpace X] [T2Space X]
    (hr : IsClosed (relGraph r)) : IsClosedMap (Quotient.mk r) := by
  intro s hs
  rw [isClosed_quotient_iff_preimage, preimage_image_quotient_mk]
  exact isClosed_saturation hr hs

/-- **A compact Hausdorff space modulo a relation with closed graph is Hausdorff.**

The two classes are first separated by open sets one of which does not meet the graph, and then
the closedness of the quotient map is used. -/
theorem t2_quotient_of_closed [CompactSpace X] [T2Space X]
    (hr : IsClosed {p : X × X | r p.1 p.2}) : T2Space (Quotient r) where
  t2 := by
    intro a b hab
    obtain ⟨x, rfl⟩ := Quotient.exists_rep a
    obtain ⟨y, rfl⟩ := Quotient.exists_rep b
    have hxy : ¬ r x y := fun h => hab (Quotient.sound h)
    have hK : IsClosed {z | r z x} := isClosed_class_of_isClosed_relGraph hr x
    have hL : IsClosed {z | r z y} := isClosed_class_of_isClosed_relGraph hr y
    have hdisj : Disjoint {z | r z x} {z | r z y} := by
      rw [Set.disjoint_left]
      exact fun z hz1 hz2 => hxy (r.trans (r.symm hz1) hz2)
    obtain ⟨u, v, hu, hv, hKu, hLv, huv⟩ := normal_separation hK hL hdisj
    have hcle : IsClosedMap (Quotient.mk r) := isClosedMap_quotient_mk_of_isClosed_relGraph hr
    have hu' : IsClosed (uᶜ) := isClosed_compl_iff.mpr hu
    have hv' : IsClosed (vᶜ) := isClosed_compl_iff.mpr hv
    refine ⟨(Quotient.mk r '' uᶜ)ᶜ, (Quotient.mk r '' vᶜ)ᶜ,
      isOpen_compl_iff.mpr (hcle uᶜ hu'), isOpen_compl_iff.mpr (hcle vᶜ hv'), ?_, ?_, ?_⟩
    · rw [mem_compl_iff, mem_image]
      rintro ⟨w, hw, hwx⟩
      exact hw (hKu (Quotient.exact hwx))
    · rw [mem_compl_iff, mem_image]
      rintro ⟨w, hw, hwy⟩
      exact hw (hLv (Quotient.exact hwy))
    · rw [Set.disjoint_left]
      intro z hz1 hz2
      obtain ⟨w, rfl⟩ := Quotient.exists_rep z
      have hwu : w ∈ u := by
        by_contra hw
        exact hz1 ⟨w, hw, rfl⟩
      have hwv : w ∈ v := by
        by_contra hw
        exact hz2 ⟨w, hw, rfl⟩
      exact Set.disjoint_left.mp huv hwu hwv

/-- The contract form of `t2_quotient_of_closed`, with the graph written out. -/
theorem t2Space_quotient_of_isClosed_relGraph [CompactSpace X] [T2Space X] (r : Setoid X)
    (hr : IsClosed (relGraph r)) : T2Space (Quotient r) :=
  t2_quotient_of_closed (r := r) hr

/-- The quotient of a compact Hausdorff space by a closed-graph relation is T₁ (points closed). -/
theorem t1Space_quotient_of_isClosed_relGraph [CompactSpace X] [T2Space X] (r : Setoid X)
    (hr : IsClosed (relGraph r)) : T1Space (Quotient r) := by
  have := t2_quotient_of_closed (r := r) hr
  infer_instance

/-- The name used in the blueprint: the quotient map of a compact Hausdorff space by a
relation with closed graph is closed. -/
alias isClosedMap_quotient_mk_of_closed := isClosedMap_quotient_mk_of_isClosed_relGraph

end Graph

section Topology

variable {X : Type u} [TopologicalSpace X] {r : Setoid X}

variable {Y : Type v}

/-- **Openness criterion for a quotient of a two-piece coproduct**: a set is open iff its
preimages in the two pieces are open. -/
theorem isOpen_quotient_iff_sum [TopologicalSpace Y] (r : Setoid (X ⊕ Y))
    {s : Set (Quotient r)} :
    IsOpen s ↔ IsOpen {x : X | Quotient.mk r (Sum.inl x) ∈ s} ∧
      IsOpen {y : Y | Quotient.mk r (Sum.inr y) ∈ s} := by
  rw [isOpen_quotient_iff_preimage, isOpen_sum_iff]
  rfl

/-- **Closedness criterion for a quotient of a two-piece coproduct.** -/
theorem isClosed_quotient_iff_sum [TopologicalSpace Y] (r : Setoid (X ⊕ Y))
    {s : Set (Quotient r)} :
    IsClosed s ↔ IsClosed {x : X | Quotient.mk r (Sum.inl x) ∈ s} ∧
      IsClosed {y : Y | Quotient.mk r (Sum.inr y) ∈ s} := by
  rw [isClosed_quotient_iff_preimage, isClosed_sum_iff]
  rfl

/-- **Openness criterion for a quotient of a two-piece coproduct** (`isOpen_quotient_iff_sum`
under the name used in the blueprint). -/
theorem isOpen_quotient_iff_pieces [TopologicalSpace Y] (r : Setoid (X ⊕ Y))
    {U : Set (Quotient r)} :
    IsOpen U ↔ IsOpen {x : X | Quotient.mk r (Sum.inl x) ∈ U} ∧
      IsOpen {y : Y | Quotient.mk r (Sum.inr y) ∈ U} :=
  isOpen_quotient_iff_sum r

/-- **Closedness criterion for a quotient of a two-piece coproduct**, under the name used in
the blueprint. -/
theorem isClosed_quotient_iff_pieces [TopologicalSpace Y] (r : Setoid (X ⊕ Y))
    {U : Set (Quotient r)} :
    IsClosed U ↔ IsClosed {x : X | Quotient.mk r (Sum.inl x) ∈ U} ∧
      IsClosed {y : Y | Quotient.mk r (Sum.inr y) ∈ U} :=
  isClosed_quotient_iff_sum r

/-- Continuity out of a quotient of a two-piece coproduct. -/
theorem continuous_quotient_iff_sum {Z : Type v} [TopologicalSpace Y] [TopologicalSpace Z]
    (r : Setoid (X ⊕ Y)) {f : Quotient r → Z} :
    Continuous f ↔ Continuous (fun x : X => f (Quotient.mk r (Sum.inl x))) ∧
      Continuous (fun y : Y => f (Quotient.mk r (Sum.inr y))) := by
  rw [continuous_quotient_iff, continuous_sum_dom]
  rfl

end Topology

section Sigma

variable {ι : Type u} {X : ι → Type v} [∀ i, TopologicalSpace (X i)] {r : Setoid (Sigma X)}

/-- **Openness criterion for a quotient of a coproduct of pieces.** -/
theorem isOpen_quotient_iff_sigma {s : Set (Quotient r)} :
    IsOpen s ↔ ∀ i, IsOpen {x : X i | Quotient.mk r ⟨i, x⟩ ∈ s} := by
  rw [isOpen_quotient_iff_preimage, isOpen_sigma_iff]
  rfl

/-- **Closedness criterion for a quotient of a coproduct of pieces.** -/
theorem isClosed_quotient_iff_sigma {s : Set (Quotient r)} :
    IsClosed s ↔ ∀ i, IsClosed {x : X i | Quotient.mk r ⟨i, x⟩ ∈ s} := by
  rw [isClosed_quotient_iff_preimage, isClosed_sigma_iff]
  rfl

end Sigma

section PartialGraph

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

/-- **The graph of a continuous map is closed** (target Hausdorff). -/
theorem isClosed_graph_of_continuous' [T2Space Y] (f : X → Y) (hf : Continuous f) :
    IsClosed {p : X × Y | f p.1 = p.2} :=
  isClosed_eq (hf.comp continuous_fst) continuous_snd

/-- **The graph of a continuous map defined on a closed subset is closed** (target Hausdorff).

This is the basic geometric input for "glue along a homeomorphism of closed subsets": the set of
pairs `(x, f x)` with `x ∈ s` is closed in `X × Y` as soon as `s` is closed and `f : s → Y` is
continuous. -/
theorem isClosed_graph_of_continuous [T2Space Y] {s : Set X} (hs : IsClosed s) (f : s → Y)
    (hf : Continuous f) :
    IsClosed {p : X × Y | ∃ hx : p.1 ∈ s, f ⟨p.1, hx⟩ = p.2} := by
  have h1 : IsClosed {q : s × Y | f q.1 = q.2} :=
    isClosed_eq (hf.comp continuous_fst) continuous_snd
  have hemb : IsEmbedding (Prod.map (Subtype.val : s → X) (id : Y → Y)) :=
    (hs.isClosedEmbedding_subtypeVal.isEmbedding).prodMap IsEmbedding.id
  have hrange : range (Prod.map (Subtype.val : s → X) (id : Y → Y)) =
      (s : Set X) ×ˢ (Set.univ : Set Y) := by
    ext p
    constructor
    · rintro ⟨q, rfl⟩
      exact ⟨q.1.2, trivial⟩
    · rintro ⟨h1', -⟩
      exact ⟨(⟨p.1, h1'⟩, p.2), rfl⟩
  have he : IsClosedEmbedding (Prod.map (Subtype.val : s → X) (id : Y → Y)) :=
    ⟨hemb, hrange ▸ hs.prod isClosed_univ⟩
  have himg : (Prod.map (Subtype.val : s → X) (id : Y → Y)) '' {q : s × Y | f q.1 = q.2} =
      {p : X × Y | ∃ hx : p.1 ∈ s, f ⟨p.1, hx⟩ = p.2} := by
    ext p
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact ⟨q.1.2, hq⟩
    · rintro ⟨hx, hfx⟩
      exact ⟨(⟨p.1, hx⟩, p.2), hfx, rfl⟩
  rw [← himg]
  exact he.isClosed_iff_image_isClosed.mp h1

end PartialGraph

end Work.QuotientT2
