import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.Topology.Algebra.OpenSubgroup

/-!
# Isomorphisms of absolute Galois groups and the Galois correspondence

Reference: J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*,
2nd ed., Chapter XII, §12.2: the machinery converting an isomorphism
`ϕ : G(k̄₁|k₁) ≃ G(k̄₂|k₂)` of profinite groups into data on *finite* extensions.

Given a homeomorphic group isomorphism `ϕ : Gal(K₁/k₁) ≃* Gal(K₂/k₂)` of
(possibly infinite) Galois groups, `ϕ` maps the Krull-open subgroups of
`Gal(K₁/k₁)` onto the Krull-open subgroups of `Gal(K₂/k₂)` — because it is an
open map by hypothesis.  By the fundamental theorem of infinite Galois theory
(`InfiniteGalois.isOpen_iff_finite`) the open subgroups are exactly the fixing
subgroups of the finite intermediate fields, so `ϕ` induces a bijection

  {finite intermediate fields of `K₁/k₁`} → {finite intermediate fields of `K₂/k₂`},

and corresponding fields have isomorphic Galois groups, hence the same degree
over the base field.

This is the correspondence underlying CoNF (12.2.4): an isomorphism of absolute
Galois groups transports all finite Galois-theoretic data.
-/

namespace Submission.NeukirchUchida

open scoped Pointwise
open IntermediateField

variable {k₁ k₂ K₁ K₂ : Type*} [Field k₁] [Field k₂] [Field K₁] [Field K₂]
  [Algebra k₁ K₁] [Algebra k₂ K₂] [IsGalois k₁ K₁] [IsGalois k₂ K₂]

/-- **The image of a finite subextension is a finite subextension.**  A
homeomorphic group isomorphism `ϕ : Gal(K₁/k₁) ≃* Gal(K₂/k₂)` carries the
fixing subgroup of a finite intermediate field `L₁` to the fixing subgroup of a
finite intermediate field `L₂`; explicitly one may take `L₂` to be the fixed
field of the image subgroup. -/
theorem exists_finite_fixingSubgroup_map (ϕ : Gal(K₁/k₁) ≃* Gal(K₂/k₂)) (hϕ : IsHomeomorph ϕ)
    (L₁ : IntermediateField k₁ K₁) [FiniteDimensional k₁ L₁] :
    ∃ L₂ : IntermediateField k₂ K₂, FiniteDimensional k₂ L₂ ∧
      (L₁.fixingSubgroup).map ϕ.toMonoidHom = L₂.fixingSubgroup := by
  set N : Subgroup Gal(K₂/k₂) := (L₁.fixingSubgroup).map ϕ.toMonoidHom with hN
  have hopen : IsOpen (N : Set Gal(K₂/k₂)) := by
    rw [hN, Subgroup.coe_map]
    exact hϕ.isOpenMap _ ((InfiniteGalois.isOpen_iff_finite L₁).mpr
      (inferInstance : FiniteDimensional k₁ L₁))
  have hclosed : IsClosed (N : Set Gal(K₂/k₂)) := Subgroup.isClosed_of_isOpen N hopen
  refine ⟨IntermediateField.fixedField N, ?_, ?_⟩
  · refine (InfiniteGalois.isOpen_iff_finite (IntermediateField.fixedField N)).mp ?_
    rw [InfiniteGalois.fixingSubgroup_fixedField ⟨N, hclosed⟩]
    exact hopen
  · exact (InfiniteGalois.fixingSubgroup_fixedField ⟨N, hclosed⟩).symm

/-- **Corresponding finite quotients.**  If `ϕ` maps the fixing subgroup of
`L₁` onto the fixing subgroup of `L₂`, it induces an isomorphism on the
corresponding finite quotients of the absolute Galois groups. -/
noncomputable def quotientFixingSubgroupMulEquiv (ϕ : Gal(K₁/k₁) ≃* Gal(K₂/k₂))
    {L₁ : IntermediateField k₁ K₁} {L₂ : IntermediateField k₂ K₂}
    [h₁N : L₁.fixingSubgroup.Normal] [h₂N : L₂.fixingSubgroup.Normal]
    (h : Subgroup.map (ϕ : Gal(K₁/k₁) →* Gal(K₂/k₂)) L₁.fixingSubgroup = L₂.fixingSubgroup) :
    Gal(K₁/k₁) ⧸ L₁.fixingSubgroup ≃* Gal(K₂/k₂) ⧸ L₂.fixingSubgroup :=
  QuotientGroup.congr _ _ ϕ h

/-- **Corresponding finite Galois groups.**  A homeomorphic isomorphism `ϕ` of
absolute Galois groups induces an isomorphism `Gal(L₁/k₁) ≃* Gal(L₂/k₂)` of the
Galois groups of corresponding finite Galois extensions. -/
noncomputable def galoisGroupMulEquiv (ϕ : Gal(K₁/k₁) ≃* Gal(K₂/k₂))
    {L₁ : IntermediateField k₁ K₁} [FiniteDimensional k₁ L₁] [IsGalois k₁ L₁]
    {L₂ : IntermediateField k₂ K₂} [FiniteDimensional k₂ L₂] [IsGalois k₂ L₂]
    (h : Subgroup.map (ϕ : Gal(K₁/k₁) →* Gal(K₂/k₂)) L₁.fixingSubgroup = L₂.fixingSubgroup) :
    Gal(L₁/k₁) ≃* Gal(L₂/k₂) := by
  have hN₁ : L₁.fixingSubgroup.Normal :=
    (InfiniteGalois.normal_iff_isGalois L₁).mpr (inferInstance : IsGalois k₁ L₁)
  have hN₂ : L₂.fixingSubgroup.Normal :=
    (InfiniteGalois.normal_iff_isGalois L₂).mpr (inferInstance : IsGalois k₂ L₂)
  haveI := hN₁
  haveI := hN₂
  exact
    (QuotientGroup.quotientKerEquivOfSurjective
        (AlgEquiv.restrictNormalHom (F := k₁) (K₁ := K₁) L₁)
        (AlgEquiv.restrictNormalHom_surjective (F := k₁) (E := K₁))).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq
          (IntermediateField.restrictNormalHom_ker L₁)).trans
        ((QuotientGroup.congr _ _ ϕ h).trans
          ((QuotientGroup.quotientMulEquivOfEq
              (IntermediateField.restrictNormalHom_ker L₂).symm).trans
            (QuotientGroup.quotientKerEquivOfSurjective
              (AlgEquiv.restrictNormalHom (F := k₂) (K₁ := K₂) L₂)
              (AlgEquiv.restrictNormalHom_surjective (F := k₂) (E := K₂))))))

/-- The corresponding finite extensions have the same degree over the base
field: an isomorphism of Galois groups preserves the field degree. -/
theorem finrank_eq_of_galoisGroupMulEquiv {L₁ : IntermediateField k₁ K₁}
    {L₂ : IntermediateField k₂ K₂} [FiniteDimensional k₁ L₁] [IsGalois k₁ L₁]
    [FiniteDimensional k₂ L₂] [IsGalois k₂ L₂] (e : Gal(L₁/k₁) ≃* Gal(L₂/k₂)) :
    Module.finrank k₁ L₁ = Module.finrank k₂ L₂ := by
  rw [← IsGalois.card_aut_eq_finrank k₁ L₁, ← IsGalois.card_aut_eq_finrank k₂ L₂]
  exact Nat.card_congr e.toEquiv

/-- **Correspondence of finite Galois extensions.**  A homeomorphic isomorphism
`ϕ` of absolute Galois groups induces an isomorphism between the Galois groups
of corresponding finite Galois extensions: for every finite Galois `L₁/k₁` there
is a finite Galois `L₂/k₂` with `Gal(L₁/k₁) ≃* Gal(L₂/k₂)` and
`[L₁ : k₁] = [L₂ : k₂]`. -/
theorem exists_finite_galois_with_mulEquiv (ϕ : Gal(K₁/k₁) ≃* Gal(K₂/k₂))
    (hϕ : IsHomeomorph ϕ) (L₁ : IntermediateField k₁ K₁) [FiniteDimensional k₁ L₁]
    [IsGalois k₁ L₁] :
    ∃ L₂ : IntermediateField k₂ K₂, FiniteDimensional k₂ L₂ ∧ IsGalois k₂ L₂ ∧
      Nonempty (Gal(L₁/k₁) ≃* Gal(L₂/k₂)) ∧
      Module.finrank k₁ L₁ = Module.finrank k₂ L₂ := by
  obtain ⟨L₂, hfin, hmap⟩ := exists_finite_fixingSubgroup_map ϕ hϕ L₁
  haveI := hfin
  have hN₁ : L₁.fixingSubgroup.Normal :=
    (InfiniteGalois.normal_iff_isGalois L₁).mpr (inferInstance : IsGalois k₁ L₁)
  have hN₂ : L₂.fixingSubgroup.Normal := by
    rw [← hmap]
    exact hN₁.map (ϕ : Gal(K₁/k₁) →* Gal(K₂/k₂)) ϕ.surjective
  haveI := hN₂
  haveI : IsGalois k₂ L₂ := (InfiniteGalois.normal_iff_isGalois L₂).mp hN₂
  have hmap' : Subgroup.map (ϕ : Gal(K₁/k₁) →* Gal(K₂/k₂)) L₁.fixingSubgroup
      = L₂.fixingSubgroup := hmap
  exact ⟨L₂, hfin, inferInstance, ⟨galoisGroupMulEquiv ϕ hmap'⟩,
    finrank_eq_of_galoisGroupMulEquiv (galoisGroupMulEquiv ϕ hmap')⟩

end Submission.NeukirchUchida
