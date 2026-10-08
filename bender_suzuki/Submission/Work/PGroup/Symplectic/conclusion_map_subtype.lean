import Mathlib
import Submission.Work.PGroup.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Transport of the central-product/extraspecial decomposition from `↥P` to `P`

This file proves `Work.PGroup.Symplectic.conclusion_map_subtype`: the structural statements of the
intrinsic form of P. Hall's theorem on `p`-groups of symplectic type (a central-product
decomposition with a cyclic factor and an extraspecial factor of exponent dividing `p`, see
`Submission/Work/PGroup/Symplectic/Main.lean`) transport from the subgroup `↥P` of the ambient
group `G` to `G` itself, along the inclusion `P.subtype : ↥P →* G`.

The mathematical content is that the map `X ↦ X.map P.subtype` identifies the subgroup lattice of
`↥P` with the interval `{X : Subgroup G // X ≤ P}`, and respects the group-theoretic structure:
the centre `Z(X)`, the Frattini subgroup `Φ(X)`, commutators, the property of being commutative,
being a `p`-group, being elementary abelian, being special/extraspecial, and the exponent of the
group `↥X`.  All of this is proved in the auxiliary namespace
`Work.PGroup.Symplectic.ConclusionMapSubtype`.
-/

open scoped Classical Pointwise
open Subgroup

namespace Work.PGroup.Symplectic

namespace ConclusionMapSubtype

variable {G : Type*} [Group G] {P : Subgroup G}

/-- The canonical isomorphism `↥X ≃* ↥(X.map P.subtype)` for a subgroup `X` of `↥P` is the
identity on underlying elements. -/
theorem subtype_comp_equivMapOfInjective (X : Subgroup ↥P) :
    (X.map P.subtype).subtype.comp (Subgroup.equivMapOfInjective X P.subtype
        P.subtype_injective) = P.subtype.comp X.subtype := by
  ext x
  exact Subgroup.coe_equivMapOfInjective_apply X P.subtype P.subtype_injective x

/-- `X` is commutative as a subgroup of `↥P` iff its image in `G` is commutative. -/
theorem isMulCommutative_map_subtype_iff (X : Subgroup ↥P) :
    IsMulCommutative ↥(X.map P.subtype) ↔ IsMulCommutative ↥X := by
  let φ := Subgroup.equivMapOfInjective X P.subtype P.subtype_injective
  constructor
  · intro h
    rw [isMulCommutative_iff] at h ⊢
    intro a b
    exact φ.injective (by rw [φ.map_mul, φ.map_mul, h])
  · intro h
    rw [isMulCommutative_iff] at h ⊢
    intro a b
    obtain ⟨a', rfl⟩ := φ.surjective a
    obtain ⟨b', rfl⟩ := φ.surjective b
    rw [← φ.map_mul, ← φ.map_mul, h]

/-- `X` is a `p`-group iff its image in `G` is. -/
theorem isPGroup_map_subtype_iff (p : ℕ) (X : Subgroup ↥P) :
    IsPGroup p ↥(X.map P.subtype) ↔ IsPGroup p ↥X := by
  let φ := Subgroup.equivMapOfInjective X P.subtype P.subtype_injective
  rw [isPGroup_iff_pow_pow_eq_one, isPGroup_iff_pow_pow_eq_one]
  constructor
  · intro h g
    obtain ⟨k, hk⟩ := h (φ g)
    exact ⟨k, φ.injective (by rw [map_pow, hk, φ.map_one])⟩
  · intro h g
    obtain ⟨g', rfl⟩ := φ.surjective g
    obtain ⟨k, hk⟩ := h g'
    exact ⟨k, by rw [← map_pow, hk, φ.map_one]⟩

/-- `X` is elementary abelian of exponent `p` iff its image in `G` is. -/
theorem isElementaryAbelian_map_subtype_iff (p : ℕ) (X : Subgroup ↥P) :
    Work.PGroup.IsElementaryAbelian p (X.map P.subtype) ↔
      Work.PGroup.IsElementaryAbelian p X := by
  let φ := Subgroup.equivMapOfInjective X P.subtype P.subtype_injective
  constructor
  · intro h
    exact ⟨(isMulCommutative_map_subtype_iff X).mp h.1,
      fun x => φ.injective (by rw [map_pow, h.2 (φ x), φ.map_one])⟩
  · intro h
    exact ⟨(isMulCommutative_map_subtype_iff X).mpr h.1,
      fun x => by obtain ⟨y, rfl⟩ := φ.surjective x; rw [← map_pow, h.2 y, φ.map_one]⟩

/-- The Frattini subgroup is preserved by an isomorphism of groups. -/
theorem map_frattini_of_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H) :
    Subgroup.map (e : G →* H) (frattini G) = frattini H := by
  refine le_antisymm ?_ ?_
  · exact (Subgroup.map_mono (f := (e : G →* H))
      (frattini_le_comap_frattini_of_surjective e.surjective)).trans_eq
      (by rw [Subgroup.map_comap_eq, MonoidHom.range_eq_top.mpr e.surjective, top_inf_eq])
  · have h2 : Subgroup.map (e.symm : H →* G) (frattini H) ≤ frattini G :=
      (Subgroup.map_mono (f := (e.symm : H →* G))
        (frattini_le_comap_frattini_of_surjective e.symm.surjective)).trans_eq
        (by rw [Subgroup.map_comap_eq, MonoidHom.range_eq_top.mpr e.symm.surjective, top_inf_eq])
    have h3 := Subgroup.map_mono (f := (e : G →* H)) h2
    have hcomp : (e : G →* H).comp (e.symm : H →* G) = MonoidHom.id H := by
      ext x; exact e.apply_symm_apply x
    rwa [Subgroup.map_map, hcomp, Subgroup.map_id] at h3

/-- The centre commutes with the image along `P.subtype`. -/
theorem centerIn_map_subtype (X : Subgroup ↥P) :
    Work.PGroup.centerIn (X.map P.subtype) = (Work.PGroup.centerIn X).map P.subtype := by
  let φ := Subgroup.equivMapOfInjective X P.subtype P.subtype_injective
  rw [Work.PGroup.centerIn, Work.PGroup.centerIn, ← Subgroup.map_center_eq φ,
    Subgroup.map_map, Subgroup.map_map, subtype_comp_equivMapOfInjective X]

/-- The Frattini subgroup commutes with the image along `P.subtype`. -/
theorem frattiniIn_map_subtype (X : Subgroup ↥P) :
    Work.PGroup.frattiniIn (X.map P.subtype) = (Work.PGroup.frattiniIn X).map P.subtype := by
  let φ := Subgroup.equivMapOfInjective X P.subtype P.subtype_injective
  rw [Work.PGroup.frattiniIn, Work.PGroup.frattiniIn, ← map_frattini_of_mulEquiv φ,
    Subgroup.map_map, Subgroup.map_map, subtype_comp_equivMapOfInjective X]

/-- Being special is preserved by the image along `P.subtype`. -/
theorem isSpecial_map_subtype {p : ℕ} (X : Subgroup ↥P) (h : Work.PGroup.IsSpecial p X) :
    Work.PGroup.IsSpecial p (X.map P.subtype) := by
  rcases h with hea | ⟨hp, hnab, hcen, hfr, hcea⟩
  · exact Or.inl ((isElementaryAbelian_map_subtype_iff p X).mpr hea)
  · refine Or.inr ⟨(isPGroup_map_subtype_iff p X).mpr hp, ?_, ?_, ?_, ?_⟩
    · rw [isMulCommutative_map_subtype_iff X]; exact hnab
    · rw [centerIn_map_subtype, ← Subgroup.map_commutator, hcen]
    · rw [centerIn_map_subtype, frattiniIn_map_subtype, hfr]
    · rw [centerIn_map_subtype]
      exact (isElementaryAbelian_map_subtype_iff p (Work.PGroup.centerIn X)).mpr hcea

/-- Being extraspecial is preserved by the image along `P.subtype`. -/
theorem isExtraspecial_map_subtype {p : ℕ} (X : Subgroup ↥P)
    (h : Work.PGroup.IsExtraspecial p X) :
    Work.PGroup.IsExtraspecial p (X.map P.subtype) := by
  refine ⟨?_, isSpecial_map_subtype X h.2.1, ?_⟩
  · rw [isMulCommutative_map_subtype_iff X]; exact h.1
  · rw [centerIn_map_subtype, Subgroup.card_map_of_injective P.subtype_injective]
    exact h.2.2

/-- A central-product decomposition of `⊤` in `↥P` maps to one of `P` in `G`. -/
theorem isCentralProduct_map_subtype (A B : Subgroup ↥P)
    (h : Work.PGroup.IsCentralProduct (⊤ : Subgroup ↥P) A B) :
    Work.PGroup.IsCentralProduct P (A.map P.subtype) (B.map P.subtype) := by
  refine ⟨Subgroup.map_subtype_le A, Subgroup.map_subtype_le B, ?_, ?_, ?_, ?_⟩
  · rw [← Subgroup.map_sup, h.2.2.1, Subgroup.map_top, Subgroup.range_subtype]
  · rw [← Subgroup.map_commutator, h.2.2.2.1, Subgroup.map_bot]
  · rw [← Subgroup.map_inf A B P.subtype P.subtype_injective, centerIn_map_subtype]
    exact Subgroup.map_mono h.2.2.2.2.1
  · rw [← Subgroup.map_inf A B P.subtype P.subtype_injective, centerIn_map_subtype]
    exact Subgroup.map_mono h.2.2.2.2.2

/-- A cyclic subgroup of `↥P` maps to a cyclic subgroup of `G`. -/
theorem map_zpowers (a : ↥P) :
    (Subgroup.zpowers a).map P.subtype = Subgroup.zpowers (a : G) := by
  rw [Subgroup.zpowers_eq_closure, MonoidHom.map_closure, Set.image_singleton,
    ← Subgroup.zpowers_eq_closure]
  congr 1

/-- The exponent of the group `↥X` equals that of `↥(X.map P.subtype)`. -/
theorem exponent_map_subtype (X : Subgroup ↥P) :
    Monoid.exponent ↥(X.map P.subtype) = Monoid.exponent ↥X :=
  (Monoid.exponent_eq_of_mulEquiv
    (Subgroup.equivMapOfInjective X P.subtype P.subtype_injective)).symm

end ConclusionMapSubtype

theorem conclusion_map_subtype {G : Type*} [Group G] (P : Subgroup G) [Finite P] {p : ℕ}
    (h : ∃ Cc E : Subgroup ↥P, Work.PGroup.IsCentralProduct (⊤ : Subgroup ↥P) Cc E ∧
      (∃ a : ↥P, Cc = Subgroup.zpowers a) ∧ Work.PGroup.IsExtraspecial p E ∧
      Monoid.exponent ↥E ∣ p) :
    ∃ Cc E : Subgroup G, Work.PGroup.IsCentralProduct P Cc E ∧
      (∃ a : G, Cc = Subgroup.zpowers a) ∧ Work.PGroup.IsExtraspecial p E ∧
      Monoid.exponent ↥E ∣ p := by
  obtain ⟨Cc0, E0, hcp, ⟨a, ha⟩, hex, hdvd⟩ := h
  refine ⟨Cc0.map P.subtype, E0.map P.subtype,
    ConclusionMapSubtype.isCentralProduct_map_subtype Cc0 E0 hcp,
    ⟨(a : G), ?_⟩, ConclusionMapSubtype.isExtraspecial_map_subtype E0 hex, ?_⟩
  · rw [ha]; exact ConclusionMapSubtype.map_zpowers a
  · rw [ConclusionMapSubtype.exponent_map_subtype E0]; exact hdvd

end Work.PGroup.Symplectic
