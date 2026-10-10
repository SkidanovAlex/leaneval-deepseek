import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PicardGroup
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Hilbert90
import Submission.Commons.GroupTheory.Hom.card_range_mul_card_ker_add
import Submission.Commons.NumberTheory.NumberField.Completion.natCard_quotient_units_range_norm_eq_card_of_abelian_of_prime_power
import Submission.Commons.RepresentationTheory.GroupCohomology.H2_inflation_restriction_exact_of_subsingleton_H1
import Submission.Commons.RepresentationTheory.GroupCohomology.natCard_groupCohomology_res_mulEquiv
import Submission.Commons.RepresentationTheory.GroupCohomology.natCard_groupCohomology_two_units_of_cyclic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000

namespace Commons.NumberTheory.NumberField.Completion

open CategoryTheory Representation

namespace NatCardP9

/-! ## Invariance of group cohomology under a group isomorphism -/

open CategoryTheory groupCohomology in
/-- The pullback of a representation along a group isomorphism: `Subsingleton` form. -/
theorem subsingleton_groupCohomology_res_mulEquiv {k G G' : Type} [CommRing k] [Group G]
    [Group G'] (e : G ≃* G') (A : Rep.{0,0,0} k G') (n : ℕ) :
    Subsingleton (groupCohomology (Rep.res e.toMonoidHom A) n) ↔
      Subsingleton (groupCohomology A n) := by
  have h : Nonempty (groupCohomology (Rep.res e.toMonoidHom A) n ≃ₗ[k] groupCohomology A n) :=
    ⟨CategoryTheory.Iso.toLinearEquiv
      (groupCohomology.mapIso (G := G) (H := G') (A := A) (B := Rep.res e.toMonoidHom A) e
        (LinearEquiv.refl k A.V) ?_ n)⟩
  · obtain ⟨ee⟩ := h
    exact ee.toEquiv.subsingleton_congr
  · intro g
    rfl

open CategoryTheory groupCohomology in
/-- An isomorphism of representations induces an isomorphism on cohomology, hence equal `Nat.card`. -/
theorem natCard_groupCohomology_iso {k G : Type} [CommRing k] [Group G]
    {A B' : Rep.{0,0,0} k G} (e : A ≅ B') (n : ℕ) :
    Nat.card (groupCohomology A n) = Nat.card (groupCohomology B' n) :=
  Nat.card_congr ((groupCohomology.functor k G n).mapIso e).toLinearEquiv.toEquiv

/-! ## Galois correspondence for units -/

open CategoryTheory Representation in
/-- A unit of `E` is fixed by all of `H` iff it comes from the fixed field. -/
theorem mem_invariants_iff {B E : Type} [Field B] [Field E] [Algebra B E]
    [FiniteDimensional B E] [IsGalois B E] (H : Subgroup (E ≃ₐ[B] E)) (x : Eˣ) :
    (∀ h : H, (h : E ≃ₐ[B] E) • x = x) ↔
      x ∈ (Units.map (algebraMap ↥(IntermediateField.fixedField H) E).toMonoidHom).range := by
  set B₁ := IntermediateField.fixedField H with hB₁
  constructor
  · intro hx
    have hfix : ∀ h : H, (h : E ≃ₐ[B] E) (x : E) = (x : E) := by
      intro h
      have := congrArg (fun u : Eˣ => (u : E)) (hx h)
      simpa using this
    have hmem : (x : E) ∈ B₁ := by
      rw [IntermediateField.mem_fixedField_iff]
      intro σ hσ
      exact hfix ⟨σ, hσ⟩
    refine ⟨Units.mk0 ⟨(x : E), hmem⟩ ?_, ?_⟩
    · exact fun h0 => Units.ne_zero x (Subtype.ext_iff.mp h0)
    · apply Units.ext
      rfl
  · rintro ⟨y, rfl⟩ h
    apply Units.ext
    have hy : (h : E ≃ₐ[B] E) (algebraMap ↥B₁ E (y : ↥B₁)) = algebraMap ↥B₁ E (y : ↥B₁) := by
      have hmem : (h : E ≃ₐ[B] E) ∈ IntermediateField.fixingSubgroup B₁ := by
        rw [hB₁, IntermediateField.fixingSubgroup_fixedField]; exact h.2
      exact (IntermediateField.mem_fixingSubgroup_iff B₁ _).mp hmem (y : ↥B₁) (y : ↥B₁).2
    simpa [Units.coe_smul, Units.coe_map] using hy

open CategoryTheory Representation in
/-- Bridge to the `Rep` language: the `H`-fixed elements of the units representation are exactly
the units of the fixed field `E^H`. -/
theorem mem_invariants_iff_repr {B E : Type} [Field B] [Field E] [Algebra B E]
    [FiniteDimensional B E] [IsGalois B E] (H : Subgroup (E ≃ₐ[B] E))
    (u : (Rep.ofAlgebraAutOnUnits B E).V) :
    (∀ h : H, (Rep.ofAlgebraAutOnUnits B E).ρ (H.subtype h) u = u) ↔
      ∃ y : (IntermediateField.fixedField H)ˣ,
        u = Additive.ofMul
          (Units.map (algebraMap (IntermediateField.fixedField H) E).toMonoidHom y) := by
  set B₁ := IntermediateField.fixedField H with hB₁
  constructor
  · intro hu
    have hfix : ∀ h : H, (h : E ≃ₐ[B] E) • (Additive.toMul u : Eˣ) = (Additive.toMul u : Eˣ) := by
      intro h
      have h3 : Additive.toMul ((Rep.ofAlgebraAutOnUnits B E).ρ (H.subtype h) u) =
          Additive.toMul u := congrArg Additive.toMul (hu h)
      rwa [show Additive.toMul ((Rep.ofAlgebraAutOnUnits B E).ρ (H.subtype h) u) =
        (h : E ≃ₐ[B] E) • (Additive.toMul u : Eˣ) from rfl] at h3
    obtain ⟨y, hy⟩ := (mem_invariants_iff H (Additive.toMul u)).mp hfix
    refine ⟨y, ?_⟩
    rw [hy]
    rfl
  · rintro ⟨y, rfl⟩ h
    apply Additive.ofMul.injective
    show ((Rep.ofAlgebraAutOnUnits B E).ρ (H.subtype h))
        (Additive.ofMul (Units.map (algebraMap ↥B₁ E).toMonoidHom y)) =
      Additive.ofMul (Units.map (algebraMap ↥B₁ E).toMonoidHom y)
    rw [show ((Rep.ofAlgebraAutOnUnits B E).ρ (H.subtype h))
        (Additive.ofMul (Units.map (algebraMap ↥B₁ E).toMonoidHom y)) =
      Additive.ofMul ((h : E ≃ₐ[B] E) •
        ((Units.map (algebraMap ↥B₁ E).toMonoidHom y) : Eˣ)) from rfl]
    congr 1
    have hmem : (h : E ≃ₐ[B] E) ∈ IntermediateField.fixingSubgroup B₁ := by
      rw [hB₁, IntermediateField.fixingSubgroup_fixedField]; exact h.2
    have hy : (h : E ≃ₐ[B] E) (algebraMap ↥B₁ E (y : ↥B₁)) = algebraMap ↥B₁ E (y : ↥B₁) :=
      (IntermediateField.mem_fixingSubgroup_iff B₁ _).mp hmem (y : ↥B₁) (y : ↥B₁).2
    apply Units.ext
    simpa [Units.coe_map] using hy


open CategoryTheory Representation in
/-- A single `Exists`-statement for a fixed vector of the units representation. -/
theorem exists_of_fixed {B E : Type} [Field B] [Field E] [Algebra B E]
    [FiniteDimensional B E] [IsGalois B E] (H : Subgroup (E ≃ₐ[B] E))
    (x : Representation.invariants ((Rep.ofAlgebraAutOnUnits B E).ρ.comp H.subtype)) :
    ∃ y : (IntermediateField.fixedField H)ˣ,
      x.1 = Additive.ofMul
        (Units.map (algebraMap (IntermediateField.fixedField H) E).toMonoidHom y) :=
  (mem_invariants_iff_repr H x.1).mp fun h =>
    (Representation.mem_invariants
      (ρ := (Rep.ofAlgebraAutOnUnits B E).ρ.comp H.subtype) x.1).mp x.2 h

open CategoryTheory Representation in
/-- The fixed vector corresponding to a unit of the fixed field. -/
def fixedOfUnit {B E : Type} [Field B] [Field E] [Algebra B E]
    [FiniteDimensional B E] [IsGalois B E] (H : Subgroup (E ≃ₐ[B] E))
    (y : (IntermediateField.fixedField H)ˣ) :
    Representation.invariants ((Rep.ofAlgebraAutOnUnits B E).ρ.comp H.subtype) :=
  ⟨Additive.ofMul (Units.map (algebraMap (IntermediateField.fixedField H) E).toMonoidHom y),
    (mem_invariants_iff_repr H _).mpr ⟨y, rfl⟩⟩

open CategoryTheory Representation in
/-- **The module identification.**  The `H`-invariants of the units representation of `E/B` are
the units of the fixed field `E^H`. -/
noncomputable def unitsInvEquiv {B E : Type} [Field B] [Field E] [Algebra B E]
    [FiniteDimensional B E] [IsGalois B E] (H : Subgroup (E ≃ₐ[B] E)) :
    Representation.invariants ((Rep.ofAlgebraAutOnUnits B E).ρ.comp H.subtype) ≃
      Additive (IntermediateField.fixedField H)ˣ where
  toFun x := Classical.choose (exists_of_fixed H x)
  invFun y := fixedOfUnit H y
  left_inv x := by
    apply Subtype.ext
    exact (Classical.choose_spec (exists_of_fixed H x)).symm
  right_inv y := by
    have h := Classical.choose_spec (exists_of_fixed H (fixedOfUnit H y))
    have h2 := congrArg Additive.toMul h
    change (Units.map (algebraMap (IntermediateField.fixedField H) E).toMonoidHom) y =
      (Units.map (algebraMap (IntermediateField.fixedField H) E).toMonoidHom)
        (Classical.choose (exists_of_fixed H (fixedOfUnit H y))) at h2
    exact Units.map_injective (f := (algebraMap (IntermediateField.fixedField H) E).toMonoidHom)
      (RingHom.injective _) h2.symm

open CategoryTheory Representation in
/-- Additivity of `unitsInvEquiv`. -/
theorem unitsInvEquiv_map_add {B E : Type} [Field B] [Field E] [Algebra B E]
    [FiniteDimensional B E] [IsGalois B E] (H : Subgroup (E ≃ₐ[B] E))
    (x y : Representation.invariants ((Rep.ofAlgebraAutOnUnits B E).ρ.comp H.subtype)) :
    unitsInvEquiv H (x + y) = unitsInvEquiv H x + unitsInvEquiv H y := by
  have hx := Classical.choose_spec (exists_of_fixed H x)
  have hy := Classical.choose_spec (exists_of_fixed H y)
  have hxy := Classical.choose_spec (exists_of_fixed H (x + y))
  rw [show unitsInvEquiv H (x + y) = Classical.choose (exists_of_fixed H (x + y)) from rfl,
    show unitsInvEquiv H x = Classical.choose (exists_of_fixed H x) from rfl,
    show unitsInvEquiv H y = Classical.choose (exists_of_fixed H y) from rfl]
  change (Classical.choose (exists_of_fixed H (x + y)) :
      (IntermediateField.fixedField H)ˣ) =
    Classical.choose (exists_of_fixed H x) * Classical.choose (exists_of_fixed H y)
  apply Units.map_injective (f := (algebraMap (IntermediateField.fixedField H) E).toMonoidHom)
    (RingHom.injective _)
  simp only [map_mul]
  have key : Additive.ofMul ((Units.map (algebraMap (IntermediateField.fixedField H) E).toMonoidHom)
        (Classical.choose (exists_of_fixed H (x + y))))
      = Additive.ofMul ((Units.map (algebraMap (IntermediateField.fixedField H) E).toMonoidHom)
          (Classical.choose (exists_of_fixed H x)))
        + Additive.ofMul ((Units.map (algebraMap (IntermediateField.fixedField H) E).toMonoidHom)
          (Classical.choose (exists_of_fixed H y))) := by
    rw [← hxy, ← hx, ← hy]
    rfl
  have key2 := congrArg Additive.toMul key
  simpa using key2

open CategoryTheory Representation in
/-- The `AddEquiv` underlying the module identification. -/
noncomputable def unitsInvAddEquiv {B E : Type} [Field B] [Field E] [Algebra B E]
    [FiniteDimensional B E] [IsGalois B E] (H : Subgroup (E ≃ₐ[B] E)) :
    Representation.invariants ((Rep.ofAlgebraAutOnUnits B E).ρ.comp H.subtype) ≃+
      Additive (IntermediateField.fixedField H)ˣ where
  toFun := unitsInvEquiv H
  invFun := (unitsInvEquiv H).symm
  left_inv := (unitsInvEquiv H).left_inv
  right_inv := (unitsInvEquiv H).right_inv
  map_add' := unitsInvEquiv_map_add H

open CategoryTheory Representation in
/-- **The `ℤ`-linear module identification.** -/
noncomputable def unitsInvLinearEquiv {B E : Type} [Field B] [Field E] [Algebra B E]
    [FiniteDimensional B E] [IsGalois B E] (H : Subgroup (E ≃ₐ[B] E)) :
    Representation.invariants ((Rep.ofAlgebraAutOnUnits B E).ρ.comp H.subtype) ≃ₗ[ℤ]
      Additive (IntermediateField.fixedField H)ˣ :=
  (unitsInvAddEquiv H).toLinearEquiv fun c x => by
    change unitsInvEquiv H (c • x) = c • unitsInvEquiv H x
    exact AddMonoidHom.map_zsmul (unitsInvAddEquiv H).toAddMonoidHom c x

open CategoryTheory Representation in
/-- `unitsInvLinearEquiv` is the unique unit of the fixed field mapping to a given invariant unit
of `Eˣ`. -/
theorem units_map_unitsInvLinearEquiv {B E : Type} [Field B] [Field E] [Algebra B E]
    [FiniteDimensional B E] [IsGalois B E] (H : Subgroup (E ≃ₐ[B] E))
    (z : Representation.invariants ((Rep.ofAlgebraAutOnUnits B E).ρ.comp H.subtype)) :
    Units.map (algebraMap (IntermediateField.fixedField H) E).toMonoidHom
        (unitsInvLinearEquiv H z) = Additive.toMul z.1 := by
  have h := Classical.choose_spec (exists_of_fixed H z)
  rw [show unitsInvLinearEquiv H z = Classical.choose (exists_of_fixed H z) from rfl]
  exact (congrArg Additive.toMul h).symm

open CategoryTheory Representation in
/-- `algebraMap B₁ E` commutes with the Galois action, for `B₁ ⊆ E` normal over `B`. -/
theorem units_map_smul_restrictNormal {B E : Type} [Field B] [Field E] [Algebra B E]
    [FiniteDimensional B E] [IsGalois B E] (B₁ : IntermediateField B E) [Normal B ↥B₁]
    (g : E ≃ₐ[B] E) (w : B₁ˣ) :
    Units.map (algebraMap B₁ E).toMonoidHom
        (Units.map (AlgEquiv.restrictNormalHom B₁ g).toRingEquiv.toMonoidHom w)
      = Units.map g.toRingEquiv.toMonoidHom
          (Units.map (algebraMap B₁ E).toMonoidHom w) := by
  apply Units.ext
  simp only [Units.coe_map]
  exact AlgEquiv.restrictNormal_commutes g B₁ (w : ↥B₁)

open CategoryTheory Representation in
theorem unitsInvLinearEquiv_equivariant {B E : Type} [Field B] [Field E] [Algebra B E]
    [FiniteDimensional B E] [IsGalois B E] (H : Subgroup (E ≃ₐ[B] E)) [H.Normal]
    (g : (E ≃ₐ[B] E) ⧸ H)
    (x : Representation.invariants ((Rep.ofAlgebraAutOnUnits B E).ρ.comp H.subtype)) :
    unitsInvLinearEquiv H (((Rep.ofAlgebraAutOnUnits B E).quotientToInvariants H).ρ g x)
      = (Rep.res (IsGalois.normalAutEquivQuotient H).toMonoidHom
          (Rep.ofAlgebraAutOnUnits B ↥(IntermediateField.fixedField H))).ρ g
        (unitsInvLinearEquiv H x) := by
  let B₁ := IntermediateField.fixedField H
  haveI : Normal B ↥B₁ := by
    haveI : IsGalois B ↥B₁ := IsGalois.of_fixedField_normal_subgroup H
    infer_instance
  obtain ⟨g', rfl⟩ := QuotientGroup.mk_surjective g
  apply Units.map_injective (f := (algebraMap ↥B₁ E).toMonoidHom) (RingHom.injective _)
  rw [units_map_unitsInvLinearEquiv H
    (((Rep.ofAlgebraAutOnUnits B E).quotientToInvariants H).ρ (QuotientGroup.mk g') x)]
  rw [show (Rep.res (IsGalois.normalAutEquivQuotient H).toMonoidHom
        (Rep.ofAlgebraAutOnUnits B ↥B₁)).ρ (QuotientGroup.mk g')
      = (Rep.ofAlgebraAutOnUnits B ↥B₁).ρ (AlgEquiv.restrictNormalHom ↥B₁ g') from rfl]
  change Additive.toMul (((Rep.ofAlgebraAutOnUnits B E).quotientToInvariants H).ρ
        (QuotientGroup.mk g') x).1
      = Units.map (algebraMap ↥B₁ E).toMonoidHom
          (Additive.ofMul (Units.map (AlgEquiv.restrictNormalHom ↥B₁ g').toRingEquiv.toMonoidHom
            (Additive.toMul (unitsInvLinearEquiv H x))))
  rw [show Units.map (algebraMap ↥B₁ E).toMonoidHom
        (Additive.ofMul (Units.map (AlgEquiv.restrictNormalHom ↥B₁ g').toRingEquiv.toMonoidHom
          (Additive.toMul (unitsInvLinearEquiv H x))))
      = Units.map (algebraMap ↥B₁ E).toMonoidHom
          (Units.map (AlgEquiv.restrictNormalHom ↥B₁ g').toRingEquiv.toMonoidHom
            (Additive.toMul (unitsInvLinearEquiv H x))) from rfl]
  rw [show ((((Rep.ofAlgebraAutOnUnits B E).quotientToInvariants H).ρ
        (QuotientGroup.mk g') x).1) = (Rep.ofAlgebraAutOnUnits B E).ρ g' x.1 from rfl]
  rw [units_map_smul_restrictNormal B₁ g' (Additive.toMul (unitsInvLinearEquiv H x))]
  rw [show Units.map (algebraMap ↥B₁ E).toMonoidHom (Additive.toMul (unitsInvLinearEquiv H x))
      = Units.map (algebraMap ↥B₁ E).toMonoidHom (unitsInvLinearEquiv H x) from rfl]
  rw [units_map_unitsInvLinearEquiv H x]
  rfl

open CategoryTheory Representation in
/-- **`G ⧸ H`-side identification**: the cohomology of the invariants `A^H` is the cohomology of
the units of the fixed field `E^H`. -/
theorem natCard_groupCohomology_two_quotientToInvariants_units {B E : Type} [Field B] [Field E]
    [Algebra B E] [FiniteDimensional B E] [IsGalois B E] (H : Subgroup (E ≃ₐ[B] E)) [H.Normal] :
    Nat.card (groupCohomology ((Rep.ofAlgebraAutOnUnits B E).quotientToInvariants H) 2) =
      Nat.card (groupCohomology (Rep.ofAlgebraAutOnUnits B ↥(IntermediateField.fixedField H)) 2) := by
  haveI : Normal B ↥(IntermediateField.fixedField H) := by
    haveI : IsGalois B ↥(IntermediateField.fixedField H) := IsGalois.of_fixedField_normal_subgroup H
    infer_instance
  have hiso : (Rep.ofAlgebraAutOnUnits B E).quotientToInvariants H ≅
      Rep.res (IsGalois.normalAutEquivQuotient H).toMonoidHom
        (Rep.ofAlgebraAutOnUnits B ↥(IntermediateField.fixedField H)) :=
    { hom := Rep.ofHom ⟨(unitsInvLinearEquiv H).toLinearMap, fun g => by
        apply LinearMap.ext; intro x
        exact unitsInvLinearEquiv_equivariant H g x⟩
      inv := Rep.ofHom ⟨(unitsInvLinearEquiv H).symm.toLinearMap, fun g => by
        apply LinearMap.ext; intro y
        show (unitsInvLinearEquiv H).symm
            ((Rep.res (IsGalois.normalAutEquivQuotient H).toMonoidHom
              (Rep.ofAlgebraAutOnUnits B ↥(IntermediateField.fixedField H))).ρ g y)
          = ((Rep.ofAlgebraAutOnUnits B E).quotientToInvariants H).ρ g
              ((unitsInvLinearEquiv H).symm y)
        conv_lhs => rw [show y = (unitsInvLinearEquiv H) ((unitsInvLinearEquiv H).symm y) from
          (LinearEquiv.apply_symm_apply (unitsInvLinearEquiv H) y).symm]
        rw [(unitsInvLinearEquiv_equivariant H g ((unitsInvLinearEquiv H).symm y)).symm]
        rw [LinearEquiv.symm_apply_apply]⟩
      hom_inv_id := by
        apply Rep.hom_ext
        apply Representation.IntertwiningMap.ext
        apply LinearMap.ext
        intro x
        rw [Rep.hom_comp_toLinearMap]
        simp only [Rep.hom_ofHom, LinearMap.comp_apply]
        exact LinearEquiv.symm_apply_apply (unitsInvLinearEquiv H) x
      inv_hom_id := by
        apply Rep.hom_ext
        apply Representation.IntertwiningMap.ext
        apply LinearMap.ext
        intro x
        rw [Rep.hom_comp_toLinearMap]
        simp only [Rep.hom_ofHom, LinearMap.comp_apply]
        exact LinearEquiv.apply_symm_apply (unitsInvLinearEquiv H) x }
  rw [natCard_groupCohomology_iso hiso 2]
  exact Commons.RepresentationTheory.GroupCohomology.natCard_groupCohomology_res_mulEquiv
    (IsGalois.normalAutEquivQuotient H)
    (Rep.ofAlgebraAutOnUnits B ↥(IntermediateField.fixedField H)) 2

/-! ## The `H`-side identification -/

open CategoryTheory Representation in
/-- `subgroupEquivAlgEquiv` is the identity on underlying functions. -/
theorem subgroupEquivAlgEquiv_apply_coe {B E : Type} [Field B] [Field E] [Algebra B E]
    [FiniteDimensional B E] [IsGalois B E] (H : Subgroup (E ≃ₐ[B] E)) (h : H) :
    ⇑((IntermediateField.subgroupEquivAlgEquiv H) h) = ⇑(h : E ≃ₐ[B] E) := rfl

set_option backward.isDefEq.respectTransparency false in
open CategoryTheory Representation in
/-- **Restricting the units representation** of `E/B` to `H` is the units representation of
`E/E^H`, read through the group isomorphism `H ≃* Gal(E/E^H)`. -/
theorem res_subtype_eq_res_subgroupEquivAlgEquiv {B E : Type} [Field B] [Field E] [Algebra B E]
    [FiniteDimensional B E] [IsGalois B E] (H : Subgroup (E ≃ₐ[B] E)) :
    Rep.res H.subtype (Rep.ofAlgebraAutOnUnits B E) =
      Rep.res (IntermediateField.subgroupEquivAlgEquiv H).toMonoidHom
        (Rep.ofAlgebraAutOnUnits ↥(IntermediateField.fixedField H) E) := by
  set B₁ := IntermediateField.fixedField H with hB₁
  set e := IntermediateField.subgroupEquivAlgEquiv H with he
  have hρ : ((Rep.ofAlgebraAutOnUnits B E).ρ.comp H.subtype) =
      ((Rep.ofAlgebraAutOnUnits B₁ E).ρ.comp e.toMonoidHom) := by
    apply MonoidHom.ext; intro h
    apply LinearMap.ext; intro u
    show (Rep.ofAlgebraAutOnUnits B E).ρ (H.subtype h) u =
      (Rep.ofAlgebraAutOnUnits B₁ E).ρ (e.toMonoidHom h) u
    show Additive.ofMul ((h : E ≃ₐ[B] E) • (Additive.toMul u : Eˣ)) =
      Additive.ofMul ((e h : E ≃ₐ[B₁] E) • (Additive.toMul u : Eˣ))
    congr 1
  exact congrArg (fun r => Rep.of (k := ℤ) (G := H) (X := Additive Eˣ) r) hρ

open CategoryTheory Representation in
/-- **`H`-side identification**: the cohomology of the restricted representation is the cohomology
of the units of the extension `E / E^H`. -/
theorem natCard_groupCohomology_two_res_units {B E : Type} [Field B] [Field E] [Algebra B E]
    [FiniteDimensional B E] [IsGalois B E] (H : Subgroup (E ≃ₐ[B] E)) :
    Nat.card (groupCohomology (Rep.res H.subtype (Rep.ofAlgebraAutOnUnits B E)) 2) =
      Nat.card (groupCohomology (Rep.ofAlgebraAutOnUnits ↥(IntermediateField.fixedField H) E) 2) := by
  rw [res_subtype_eq_res_subgroupEquivAlgEquiv H]
  exact Commons.RepresentationTheory.GroupCohomology.natCard_groupCohomology_res_mulEquiv
    (IntermediateField.subgroupEquivAlgEquiv H)
    (Rep.ofAlgebraAutOnUnits ↥(IntermediateField.fixedField H) E) 2

open CategoryTheory Representation in
/-- Cardinal identity for a linear map: `Nat.card M = Nat.card (range f) * Nat.card (ker f)`. -/
theorem card_range_mul_card_ker_linear {R M N : Type} [Ring R] [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N] (f : M →ₗ[R] N) :
    Nat.card (LinearMap.range f) * Nat.card (LinearMap.ker f) = Nat.card M := by
  have h := Commons.GroupTheory.Hom.card_range_mul_card_ker_add f.toAddMonoidHom
  rw [show (f.toAddMonoidHom.range : AddSubgroup N) = (LinearMap.range f).toAddSubgroup from by
        ext x; rfl,
      show (f.toAddMonoidHom.ker : AddSubgroup M) = (LinearMap.ker f).toAddSubgroup from by
        ext x; rfl] at h
  exact h

open CategoryTheory Representation in
/-- A linear map with finite range and finite kernel has finite domain. -/
theorem finite_of_finite_range_ker {R M N : Type} [Ring R] [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N] (f : M →ₗ[R] N) (hr : Finite (LinearMap.range f))
    (hk : Finite (LinearMap.ker f)) : Finite M := by
  have hne : Nat.card M ≠ 0 := by
    rw [← card_range_mul_card_ker_linear f]
    exact Nat.mul_ne_zero (Nat.card_ne_zero.mpr ⟨inferInstance, hr⟩)
      (Nat.card_ne_zero.mpr ⟨inferInstance, hk⟩)
  exact (Nat.card_ne_zero.mp hne).2

end NatCardP9


private theorem p9_key {K : Type} [Field K] [NumberField K]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    ∀ n : ℕ, ∀ {B E : Type} [Field B] [Field E]
      [instAlgB : Algebra (Q.adicCompletion K) B] [Algebra B E]
      [instAlgE : Algebra (Q.adicCompletion K) E]
      [IsScalarTower (Q.adicCompletion K) B E]
      [instFdB : FiniteDimensional (Q.adicCompletion K) B] [FiniteDimensional B E]
      [IsGalois B E],
      (∀ a b : E ≃ₐ[B] E, a * b = b * a) → Nat.card (E ≃ₐ[B] E) = n →
      Finite (groupCohomology (Rep.ofAlgebraAutOnUnits B E) 2) ∧
        Nat.card (groupCohomology (Rep.ofAlgebraAutOnUnits B E) 2) ≤ Module.finrank B E := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro B E _ _ _ _ _ _ _ _ _ hcomm hdeg
    by_cases hcyc : IsCyclic (E ≃ₐ[B] E)
    · -- ### cyclic case
      have hunits : Nat.card (groupCohomology (Rep.ofAlgebraAutOnUnits B E) 2) =
          Nat.card (Bˣ ⧸ MonoidHom.range (Units.map (Algebra.norm B : E →* B))) :=
        Commons.RepresentationTheory.GroupCohomology.natCard_groupCohomology_two_units_of_cyclic B E
      haveI hidx : (MonoidHom.range (Units.map (Algebra.norm B : E →* B))).FiniteIndex :=
        Commons.NumberTheory.NumberField.Completion.finiteIndex_range_norm_units_of_finiteDimensional
          (Q := Q)
      have hfin : Finite (groupCohomology (Rep.ofAlgebraAutOnUnits B E) 2) := by
        have hne : Nat.card (groupCohomology (Rep.ofAlgebraAutOnUnits B E) 2) ≠ 0 := by
          rw [hunits]
          exact Nat.card_ne_zero.mpr ⟨inferInstance, Subgroup.finite_quotient_of_finiteIndex⟩
        exact (Nat.card_ne_zero.mp hne).2
      refine ⟨hfin, ?_⟩
      rw [hunits]
      refine le_trans (Commons.NumberTheory.NumberField.Completion.natCard_quotient_units_range_norm_le_card_of_abelian_local_base (Q := Q) hcomm) ?_
      exact le_of_eq (IsGalois.card_aut_eq_finrank B E)
    · -- ### non-cyclic abelian case
      haveI : IsMulCommutative (E ≃ₐ[B] E) := IsMulCommutative.of_comm hcomm
      haveI : Nontrivial (E ≃ₐ[B] E) := by
        rw [← not_subsingleton_iff_nontrivial]
        intro hsub
        haveI : Subsingleton (E ≃ₐ[B] E) := hsub
        exact hcyc inferInstance
      haveI : Finite (E ≃ₐ[B] E) := inferInstance
      obtain ⟨H, hHlt, hHcyc⟩ := exists_maximal_subgroup_quotient_cyclic (E ≃ₐ[B] E)
      haveI hHnorm : H.Normal := Subgroup.normal_of_isMulCommutative H
      let C : IntermediateField B E := IntermediateField.fixedField H
      haveI hCgalB : IsGalois B ↥C := IsGalois.of_fixedField_normal_subgroup H
      haveI hCfdB : FiniteDimensional B ↥C := inferInstance
      haveI hIsGaloisCE : IsGalois ↥C E := inferInstance
      haveI hCcyc : IsCyclic (↥C ≃ₐ[B] ↥C) :=
        (IsGalois.normalAutEquivQuotient H).isCyclic.mp hHcyc
      letI instAlgC : Algebra (Q.adicCompletion K) ↥C :=
        ((algebraMap B ↥C).comp (algebraMap (Q.adicCompletion K) B)).toAlgebra
      haveI instSTBC : IsScalarTower (Q.adicCompletion K) B ↥C :=
        IsScalarTower.of_algebraMap_eq (fun x => rfl)
      letI instModC : Module (Q.adicCompletion K) ↥C := instAlgC.toModule
      haveI instFdC : Module.Finite (Q.adicCompletion K) ↥C :=
        Module.Finite.trans (R := Q.adicCompletion K) B ↥C
      haveI instFdC' : FiniteDimensional (Q.adicCompletion K) ↥C := instFdC
      haveI instSTCE : IsScalarTower (Q.adicCompletion K) ↥C E :=
        IsScalarTower.of_algebraMap_eq (fun x => by
          rw [IsScalarTower.algebraMap_apply (Q.adicCompletion K) B E,
              IsScalarTower.algebraMap_apply B ↥C E]
          congr 1)
      have hcommC : ∀ a b : ↥C ≃ₐ[B] ↥C, a * b = b * a := by
        intro a b
        have key : ∀ p q : (E ≃ₐ[B] E) ⧸ H, p * q = q * p := by
          intro p q
          obtain ⟨p', rfl⟩ := QuotientGroup.mk_surjective p
          obtain ⟨q', rfl⟩ := QuotientGroup.mk_surjective q
          rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hcomm p' q']
        obtain ⟨a', rfl⟩ := (IsGalois.normalAutEquivQuotient H).surjective a
        obtain ⟨b', rfl⟩ := (IsGalois.normalAutEquivQuotient H).surjective b
        rw [← map_mul, ← map_mul, key a' b']
      have hcommE : ∀ a b : E ≃ₐ[↥C] E, a * b = b * a := by
        intro a b
        have h := hcomm (a.restrictScalars B) (b.restrictScalars B)
        apply AlgEquiv.ext; intro x
        have hx := congr_fun (congrArg (fun g : E ≃ₐ[B] E => (g : E → E)) h) x
        simpa [AlgEquiv.mul_apply] using hx
      -- ### factor `Y = H²(B, E^H)`, cyclic Galois group
      have hYunits : Nat.card (groupCohomology (Rep.ofAlgebraAutOnUnits B ↥C) 2) =
          Nat.card (Bˣ ⧸ MonoidHom.range (Units.map (Algebra.norm B : ↥C →* B))) :=
        Commons.RepresentationTheory.GroupCohomology.natCard_groupCohomology_two_units_of_cyclic B ↥C
      haveI hYidx : (MonoidHom.range (Units.map (Algebra.norm B : ↥C →* B))).FiniteIndex :=
        Commons.NumberTheory.NumberField.Completion.finiteIndex_range_norm_units_of_finiteDimensional
          (Q := Q)
      have hYfin : Finite (groupCohomology (Rep.ofAlgebraAutOnUnits B ↥C) 2) := by
        have hne : Nat.card (groupCohomology (Rep.ofAlgebraAutOnUnits B ↥C) 2) ≠ 0 := by
          rw [hYunits]
          exact Nat.card_ne_zero.mpr ⟨inferInstance, Subgroup.finite_quotient_of_finiteIndex⟩
        exact (Nat.card_ne_zero.mp hne).2
      have hYle : Nat.card (groupCohomology (Rep.ofAlgebraAutOnUnits B ↥C) 2) ≤
          Module.finrank B ↥C := by
        rw [hYunits]
        refine le_trans (Commons.NumberTheory.NumberField.Completion.natCard_quotient_units_range_norm_le_card_of_abelian_local_base (Q := Q) hcommC) ?_
        exact le_of_eq (IsGalois.card_aut_eq_finrank B ↥C)
      -- ### factor `Z = H²(E^H, E)`, by the induction hypothesis
      have hcardE : Nat.card (E ≃ₐ[↥C] E) = Nat.card H := by
        rw [IsGalois.card_aut_eq_finrank ↥C E, IntermediateField.finrank_fixedField_eq_card H]
      haveI : Nontrivial ((E ≃ₐ[B] E) ⧸ H) := by
        rw [← not_subsingleton_iff_nontrivial]
        intro hsub
        haveI : Subsingleton ((E ≃ₐ[B] E) ⧸ H) := hsub
        have hGal : H = ⊤ := by
          rw [eq_top_iff]
          intro x
          have hh1 : (QuotientGroup.mk x : (E ≃ₐ[B] E) ⧸ H) = 1 := Subsingleton.elim _ _
          rw [QuotientGroup.eq_one_iff] at hh1
          simpa using hh1
        exact absurd hGal (ne_of_lt hHlt)
      have h1lt : 1 < Nat.card ((E ≃ₐ[B] E) ⧸ H) := by
        haveI : Fintype ((E ≃ₐ[B] E) ⧸ H) := Fintype.ofFinite _
        rw [Nat.card_eq_fintype_card]
        exact Fintype.one_lt_card
      have hHltG : Nat.card H < Nat.card (E ≃ₐ[B] E) := by
        rw [← Subgroup.card_mul_index H, Subgroup.index_eq_card]
        calc Nat.card H = Nat.card H * 1 := (Nat.mul_one _).symm
          _ < Nat.card H * Nat.card ((E ≃ₐ[B] E) ⧸ H) :=
                Nat.mul_lt_mul_of_pos_left h1lt Nat.card_pos
      have hltE : Nat.card (E ≃ₐ[↥C] E) < n := by rw [hcardE, ← hdeg]; exact hHltG
      obtain ⟨hZfin, hZle⟩ :=
        ih (Nat.card (E ≃ₐ[↥C] E)) hltE hcommE rfl (instAlgB := instAlgC) (instFdB := instFdC')
      -- ### the two identifications
      have hYeq : Nat.card (groupCohomology
            ((Rep.ofAlgebraAutOnUnits B E).quotientToInvariants H) 2) =
          Nat.card (groupCohomology (Rep.ofAlgebraAutOnUnits B ↥C) 2) :=
        NatCardP9.natCard_groupCohomology_two_quotientToInvariants_units H
      have hZeq : Nat.card (groupCohomology
            (Rep.res H.subtype (Rep.ofAlgebraAutOnUnits B E)) 2) =
          Nat.card (groupCohomology (Rep.ofAlgebraAutOnUnits ↥C E) 2) :=
        NatCardP9.natCard_groupCohomology_two_res_units H
      haveI hYfin' : Finite
          (groupCohomology ((Rep.ofAlgebraAutOnUnits B E).quotientToInvariants H) 2) := by
        have hne : Nat.card
            (groupCohomology ((Rep.ofAlgebraAutOnUnits B E).quotientToInvariants H) 2) ≠ 0 := by
          rw [hYeq]
          exact Nat.card_ne_zero.mpr ⟨inferInstance, hYfin⟩
        exact (Nat.card_ne_zero.mp hne).2
      haveI hZfin' : Finite
          (groupCohomology (Rep.res H.subtype (Rep.ofAlgebraAutOnUnits B E)) 2) := by
        have hne : Nat.card
            (groupCohomology (Rep.res H.subtype (Rep.ofAlgebraAutOnUnits B E)) 2) ≠ 0 := by
          rw [hZeq]
          exact Nat.card_ne_zero.mpr ⟨inferInstance, hZfin⟩
        exact (Nat.card_ne_zero.mp hne).2
      haveI h1sub : Subsingleton
          (groupCohomology (Rep.res H.subtype (Rep.ofAlgebraAutOnUnits B E)) 1) := by
        rw [NatCardP9.res_subtype_eq_res_subgroupEquivAlgEquiv H]
        exact (NatCardP9.subsingleton_groupCohomology_res_mulEquiv
          (IntermediateField.subgroupEquivAlgEquiv H)
          (Rep.ofAlgebraAutOnUnits ↥C E) 1).mpr inferInstance
      -- ### exactness and the cardinal arithmetic
      let i : groupCohomology ((Rep.ofAlgebraAutOnUnits B E).quotientToInvariants H) 2 →ₗ[ℤ]
          groupCohomology (Rep.ofAlgebraAutOnUnits B E) 2 :=
        ModuleCat.Hom.hom ((groupCohomology.infNatTrans ℤ H 2).app (Rep.ofAlgebraAutOnUnits B E))
      let r : groupCohomology (Rep.ofAlgebraAutOnUnits B E) 2 →ₗ[ℤ]
          groupCohomology (Rep.res H.subtype (Rep.ofAlgebraAutOnUnits B E)) 2 :=
        ModuleCat.Hom.hom ((groupCohomology.resNatTrans ℤ (G := H) (H := E ≃ₐ[B] E) H.subtype 2).app
          (Rep.ofAlgebraAutOnUnits B E))
      have hexact : LinearMap.range i = LinearMap.ker r :=
        Commons.RepresentationTheory.GroupCohomology.H2_inflation_restriction_exact_of_subsingleton_H1
          H (Rep.ofAlgebraAutOnUnits B E) h1sub
      have hsurjrange : Function.Surjective
          (fun w : groupCohomology ((Rep.ofAlgebraAutOnUnits B E).quotientToInvariants H) 2 =>
            (⟨i w, ⟨w, rfl⟩⟩ : LinearMap.range i)) := by
        intro y
        obtain ⟨w, hw⟩ := y.2
        exact ⟨w, Subtype.ext hw⟩
      have hkerle : Nat.card (LinearMap.ker r) ≤ Nat.card
          (groupCohomology ((Rep.ofAlgebraAutOnUnits B E).quotientToInvariants H) 2) := by
        rw [← hexact]
        exact Nat.card_le_card_of_surjective _ hsurjrange
      have hrangele : Nat.card (LinearMap.range r) ≤
          Nat.card (groupCohomology (Rep.res H.subtype (Rep.ofAlgebraAutOnUnits B E)) 2) :=
        Nat.card_le_card_of_injective (fun x : LinearMap.range r => (x : _)) Subtype.val_injective
      have hbound : Nat.card (groupCohomology (Rep.ofAlgebraAutOnUnits B E) 2) ≤
          Nat.card (groupCohomology ((Rep.ofAlgebraAutOnUnits B E).quotientToInvariants H) 2) *
          Nat.card (groupCohomology (Rep.res H.subtype (Rep.ofAlgebraAutOnUnits B E)) 2) :=
        calc Nat.card (groupCohomology (Rep.ofAlgebraAutOnUnits B E) 2)
            = Nat.card (LinearMap.range r) * Nat.card (LinearMap.ker r) :=
              (NatCardP9.card_range_mul_card_ker_linear r).symm
          _ ≤ Nat.card (groupCohomology (Rep.res H.subtype (Rep.ofAlgebraAutOnUnits B E)) 2) *
              Nat.card (groupCohomology ((Rep.ofAlgebraAutOnUnits B E).quotientToInvariants H) 2) :=
              Nat.mul_le_mul hrangele hkerle
          _ = Nat.card (groupCohomology ((Rep.ofAlgebraAutOnUnits B E).quotientToInvariants H) 2) *
              Nat.card (groupCohomology (Rep.res H.subtype (Rep.ofAlgebraAutOnUnits B E)) 2) :=
              Nat.mul_comm _ _
      have hXfin : Finite (groupCohomology (Rep.ofAlgebraAutOnUnits B E) 2) :=
        NatCardP9.finite_of_finite_range_ker r
          (Finite.of_injective
            (fun x : LinearMap.range r =>
              (x : groupCohomology (Rep.res H.subtype (Rep.ofAlgebraAutOnUnits B E)) 2))
            Subtype.val_injective)
          (by
            rw [← hexact]
            exact Finite.of_surjective _ hsurjrange)
      refine ⟨hXfin, ?_⟩
      calc Nat.card (groupCohomology (Rep.ofAlgebraAutOnUnits B E) 2)
          ≤ Nat.card (groupCohomology ((Rep.ofAlgebraAutOnUnits B E).quotientToInvariants H) 2) *
              Nat.card (groupCohomology (Rep.res H.subtype (Rep.ofAlgebraAutOnUnits B E)) 2) :=
            hbound
        _ = Nat.card (groupCohomology (Rep.ofAlgebraAutOnUnits B ↥C) 2) *
              Nat.card (groupCohomology (Rep.ofAlgebraAutOnUnits ↥C E) 2) := by rw [hYeq, hZeq]
        _ ≤ Module.finrank B ↥C * Module.finrank ↥C E := Nat.mul_le_mul hYle hZle
        _ = Module.finrank B E := Module.finrank_mul_finrank B ↥C E

theorem natCard_groupCohomology_two_units_le_finrank_of_abelian
    {K : Type} [Field K] [NumberField K]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    {B E : Type} [Field B] [Field E]
    [Algebra (Q.adicCompletion K) B] [Algebra B E] [Algebra (Q.adicCompletion K) E]
    [IsScalarTower (Q.adicCompletion K) B E]
    [FiniteDimensional (Q.adicCompletion K) B] [FiniteDimensional B E]
    [IsGalois B E]
    (hcomm : ∀ a b : E ≃ₐ[B] E, a * b = b * a) :
    Nat.card (groupCohomology (Rep.ofAlgebraAutOnUnits B E) 2) ≤ Module.finrank B E :=
  (p9_key Q (Nat.card (E ≃ₐ[B] E)) hcomm rfl).2

end Commons.NumberTheory.NumberField.Completion
