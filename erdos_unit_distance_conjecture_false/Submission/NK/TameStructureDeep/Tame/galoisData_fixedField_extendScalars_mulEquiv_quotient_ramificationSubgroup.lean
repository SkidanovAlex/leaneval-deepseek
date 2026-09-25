import Mathlib
import Submission.NK.Ramification.Defs
import Submission.NK.RamificationDeep.UnitMap
import Submission.NK.RamificationDeep.RamificationDeterminesSubfields
import Submission.NK.RamificationDeep.isCyclic_quotient_ramificationSubgroup

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

namespace NK.TameStructureDeep.Tame

open scoped Pointwise
open IntermediateField

/-! ## The Galois correspondence bookkeeping for a pair of nested subgroups

The main theorem below computes the Galois group of the relative extension `L/F`, where `F` and
`L` are the fixed fields of two subgroups `H1 ≤ H0` of a finite Galois group `Gal(M/κ)` with
`H1` normal in `H0`.  This file packages the standard Galois correspondence in exactly the form
needed for the inertia/wild-inertia pair: the relative Galois group is `H0 ⧸ H1`, and the
quotient is transported to the quotient of the ramification subgroups inside the decomposition
subgroup via the injective inclusion `G_i ↪ Gal(M/κ)`. -/

/-- **The image of `H1.subgroupOf H0` under the canonical isomorphism `↥H0 ≃* ↥(H0.map f)`.**  For
an injective homomorphism `f` the two ways of forming "`H1` inside `H0`" — first restricting to
`H0` and then mapping along `f`, or first mapping and then restricting — agree. -/
theorem galoisData_map_equivMapOfInjective_subgroupOf {G N : Type*} [Group G] [Group N]
    (f : G →* N) (hf : Function.Injective f) (H0 H1 : Subgroup G) :
    Subgroup.map (Subgroup.equivMapOfInjective H0 f hf : ↥H0 →* ↥(H0.map f))
        (H1.subgroupOf H0) = (H1.map f).subgroupOf (H0.map f) := by
  ext x
  constructor
  · intro hx
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_map]
    refine ⟨y, ?_, ?_⟩
    · rwa [Subgroup.mem_subgroupOf] at hy
    · have := congrArg Subtype.val hyx
      simpa using this
  · intro hx
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_map] at hx
    obtain ⟨w, hw1, hw2⟩ := hx
    obtain ⟨v, hv0, hvx⟩ := Subgroup.mem_map.mp x.2
    have hvw : v = w := hf (by rw [hvx, hw2])
    rw [Subgroup.mem_map]
    refine ⟨⟨w, hvw ▸ hv0⟩, ?_, ?_⟩
    · rwa [Subgroup.mem_subgroupOf]
    · apply Subtype.ext
      simp [hw2]

/-- **Quotients are compatible with injective maps.**  For an injective homomorphism `f` and
nested subgroups `H1 ≤ H0`, the canonical isomorphism `↥H0 ≃* ↥(H0.map f)` identifies
`H1.subgroupOf H0` with `(H1.map f).subgroupOf (H0.map f)`, hence induces an isomorphism of the
quotients. -/
noncomputable def galoisData_quotientMulEquivOfInjective {G N : Type*} [Group G] [Group N]
    (f : G →* N) (hf : Function.Injective f) (H0 H1 : Subgroup G)
    [(H1.subgroupOf H0).Normal] [((H1.map f).subgroupOf (H0.map f)).Normal] :
    (H0 ⧸ H1.subgroupOf H0) ≃* (H0.map f ⧸ (H1.map f).subgroupOf (H0.map f)) :=
  QuotientGroup.congr _ _ (Subgroup.equivMapOfInjective H0 f hf)
    (galoisData_map_equivMapOfInjective_subgroupOf f hf H0 H1)

/-- Normality is insensitive to replacing subgroups by equal subgroups: if `A = H0` and
`B = H1` and `H1` is normal in `H0`, then `B` is normal in `A`. -/
theorem galoisData_subgroupOf_normal_congr {G : Type*} [Group G] {A B H0 H1 : Subgroup G}
    (hA : A = H0) (hB : B = H1) (h : (H1.subgroupOf H0).Normal) :
    (B.subgroupOf A).Normal :=
  hA.symm ▸ (hB.symm ▸ h)

/-- **`subgroupOf` commutes with the canonical isomorphism of equal subgroups.**  For `A = H0` and
`B = H1`, the subgroup `B.subgroupOf A` of `↥A` is carried by the identity-like isomorphism
`↥A ≃* ↥H0` to `H1.subgroupOf H0`. -/
theorem galoisData_map_subgroupCongr_subgroupOf {G : Type*} [Group G] {A B H0 H1 : Subgroup G}
    (hA : A = H0) (hB : B = H1) :
    Subgroup.map (↑(MulEquiv.subgroupCongr hA)) (B.subgroupOf A) = H1.subgroupOf H0 := by
  refine le_antisymm ?_ ?_
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    rw [Subgroup.mem_subgroupOf] at hy ⊢
    rw [← hB]
    simpa using hy
  · intro x hx
    rw [Subgroup.mem_subgroupOf] at hx
    rw [Subgroup.mem_map]
    refine ⟨⟨(x : G), hA ▸ x.2⟩, ?_, ?_⟩
    · rw [Subgroup.mem_subgroupOf]
      rwa [hB]
    · apply Subtype.ext
      simp

/-- **Change of base for fixing subgroups.**  For intermediate fields `U ≤ V` of a Galois
extension `M/κ`, the fixing subgroup of `V` inside `Gal(M/U)` is the image of the fixing subgroup
of `V` inside `Gal(M/κ)` under `IntermediateField.fixingSubgroupEquiv U`. -/
theorem galoisData_map_fixingSubgroupEquiv_subgroupOf {κ M : Type*} [Field κ] [Field M]
    [Algebra κ M] [IsGalois κ M] {U V : IntermediateField κ M} (h : U ≤ V) :
    Subgroup.map (↑(IntermediateField.fixingSubgroupEquiv U))
      (V.fixingSubgroup.subgroupOf U.fixingSubgroup) =
      (IntermediateField.extendScalars h).fixingSubgroup := by
  ext f
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨g, hg, rfl⟩
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    exact hg ⟨x, hx⟩
  · intro hf
    refine ⟨(IntermediateField.fixingSubgroupEquiv U).symm f, ?_, rfl⟩
    intro x
    show ((IntermediateField.fixingSubgroupEquiv U).symm f : Gal(M/κ)) x = x
    exact (IntermediateField.mem_fixingSubgroup_iff _ f).mp hf x x.2

/-- **The Galois group of an intermediate Galois subextension as a quotient.**  If `K'/κ` is
Galois and `E` is an intermediate field which is Galois over `κ`, restriction of automorphisms
induces an isomorphism `Gal(K'/κ) ⧸ E.fixingSubgroup ≃* Gal(E/κ)`. -/
theorem galoisData_quotient_fixingSubgroup_mulEquiv_gal {κ K' : Type*} [Field κ] [Field K']
    [Algebra κ K'] [IsGalois κ K'] (E : IntermediateField κ K') [IsGalois κ ↥E] :
    Nonempty (Gal(K'/κ) ⧸ E.fixingSubgroup ≃* Gal(↥E/κ)) := by
  haveI : Normal κ ↥E := IsGalois.to_normal
  have hker : (AlgEquiv.restrictNormalHom (F := κ) (K₁ := K') ↥E).ker = E.fixingSubgroup :=
    IntermediateField.restrictNormalHom_ker E
  refine ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (AlgEquiv.restrictNormalHom (F := κ) (K₁ := K') ↥E)
      (AlgEquiv.restrictNormalHom_surjective (F := κ) (K₁ := ↥E) K'))⟩

/-- **The Galois data of a nested pair of subgroups of a finite Galois group.**  Let `M/κ` be a
finite Galois extension and let `H1 ≤ H0 ≤ Gal(M/κ)` with `H1` normal in `H0`.  Then, writing
`F = M^{H0}` and `L = M^{H1}` for the fixed fields, the extension `L/F` is finite and Galois with
Galois group `H0 ⧸ H1.subgroupOf H0`. -/
theorem galoisDataAux_of_subgroups {κ M : Type*} [Field κ] [Field M] [Algebra κ M]
    [FiniteDimensional κ M] [IsGalois κ M] {H0 H1 : Subgroup (M ≃ₐ[κ] M)} (h10 : H1 ≤ H0)
    (hn : (H1.subgroupOf H0).Normal) :
    let F : IntermediateField κ M := IntermediateField.fixedField H0
    let L : IntermediateField κ M := IntermediateField.fixedField H1
    (hFL : F ≤ L) → FiniteDimensional ↥F ↥(IntermediateField.extendScalars hFL) ∧
      IsGalois ↥F ↥(IntermediateField.extendScalars hFL) ∧
      Nonempty ((↥(IntermediateField.extendScalars hFL) ≃ₐ[↥F] ↥(IntermediateField.extendScalars hFL)) ≃*
        (H0 ⧸ H1.subgroupOf H0)) := by
  intro F L hFL
  -- the Galois correspondence: the fixing subgroups of `F` and `L` are `H0` and `H1`
  have hH0 : F.fixingSubgroup = H0 := IntermediateField.fixingSubgroup_fixedField H0
  have hH1 : L.fixingSubgroup = H1 := IntermediateField.fixingSubgroup_fixedField H1
  -- finiteness of the relative extension
  haveI hFfd : FiniteDimensional ↥F M := IntermediateField.finiteDimensional_right F
  have hfd : FiniteDimensional ↥F ↥(IntermediateField.extendScalars hFL) :=
    IntermediateField.finiteDimensional_left (K := ↥F) (L := M) (IntermediateField.extendScalars hFL)
  -- the fixing subgroup of `L` over `F` is the image of `H1.subgroupOf H0`
  have hmap : Subgroup.map (↑(IntermediateField.fixingSubgroupEquiv F))
      (L.fixingSubgroup.subgroupOf F.fixingSubgroup) =
      (IntermediateField.extendScalars hFL).fixingSubgroup :=
    galoisData_map_fixingSubgroupEquiv_subgroupOf hFL
  -- hence it is normal, being the image of the normal subgroup `H1.subgroupOf H0`
  have hHn : (IntermediateField.extendScalars hFL).fixingSubgroup.Normal := by
    rw [← hmap]
    refine Subgroup.Normal.map ?_ _ (IntermediateField.fixingSubgroupEquiv F).surjective
    rw [hH1, hH0]
    exact hn
  haveI hHnI : (IntermediateField.extendScalars hFL).fixingSubgroup.Normal := hHn
  -- so `L/F` is Galois
  have heq : IntermediateField.fixedField ((IntermediateField.extendScalars hFL).fixingSubgroup)
      = IntermediateField.extendScalars hFL :=
    IsGalois.fixedField_fixingSubgroup (IntermediateField.extendScalars hFL)
  have hgal : IsGalois ↥F ↥(IntermediateField.extendScalars hFL) := by
    have h1 : IsGalois ↥F ↥(IntermediateField.fixedField
        ((IntermediateField.extendScalars hFL).fixingSubgroup)) := inferInstance
    exact heq ▸ h1
  refine ⟨hfd, hgal, ?_⟩
  -- the Galois group `Gal(L/F)` is `Gal(M/F) ⧸ Gal(M/L)`, and `Gal(M/F) ≅ ↥(F.fixingSubgroup)`
  obtain ⟨e⟩ := galoisData_quotient_fixingSubgroup_mulEquiv_gal (κ := ↥F) (K' := M)
    (IntermediateField.extendScalars hFL)
  haveI hQn : (L.fixingSubgroup.subgroupOf F.fixingSubgroup).Normal :=
    galoisData_subgroupOf_normal_congr hH0 hH1 hn
  have hQ : Subgroup.map (↑(MulEquiv.subgroupCongr hH0))
      (L.fixingSubgroup.subgroupOf F.fixingSubgroup) = H1.subgroupOf H0 :=
    galoisData_map_subgroupCongr_subgroupOf hH0 hH1
  exact ⟨e.symm.trans ((QuotientGroup.congr _ _
      (IntermediateField.fixingSubgroupEquiv F) hmap).symm.trans
    (QuotientGroup.congr _ _ (MulEquiv.subgroupCongr hH0) hQ))⟩

/-- **The Galois data of the inertia/wild-inertia pair, with the quotient `G_0/G_1` made
explicit.**  Let `M/κ` be a finite Galois extension of fields, `A` a discrete valuation ring of
`M` which is Galois-stable (`A.decompositionSubgroup κ = ⊤`), and let `F = M^{G_0}`
(`G_i = ramificationSubgroup A i`) be the inertia field, `L = M^{G_1}` the fixed field of the wild
inertia.  Then `F ≤ L`, `L/F` is finite Galois, and its Galois group is the quotient `G_0/G_1`,
i.e. `Gal(L/F) ≃* R_0 ⧸ (R_1.subgroupOf R_0)` where `R_i` are the ramification subgroups inside
`A.decompositionSubgroup κ`. -/
theorem galoisData_fixedField_extendScalars_mulEquiv_quotient_ramificationSubgroup
    {κ M : Type*} [Field κ] [Field M] [Algebra κ M] [FiniteDimensional κ M] [IsGalois κ M]
    (A : ValuationSubring M) [IsDiscreteValuationRing A]
    (hdec : A.decompositionSubgroup κ = ⊤) :
    let F : IntermediateField κ M := IntermediateField.fixedField
      ((NK.Ramification.ramificationSubgroup (K := κ) A 0).map (A.decompositionSubgroup κ).subtype)
    let L : IntermediateField κ M := IntermediateField.fixedField
      ((NK.Ramification.ramificationSubgroup (K := κ) A 1).map (A.decompositionSubgroup κ).subtype)
    (hFL : F ≤ L) → FiniteDimensional ↥F ↥(IntermediateField.extendScalars hFL) ∧
      IsGalois ↥F ↥(IntermediateField.extendScalars hFL) ∧
      Nonempty ((↥(IntermediateField.extendScalars hFL) ≃ₐ[↥F] ↥(IntermediateField.extendScalars hFL)) ≃*
        ((NK.Ramification.ramificationSubgroup (K := κ) A 0) ⧸
          (NK.Ramification.ramificationSubgroup (K := κ) A 1).subgroupOf
            (NK.Ramification.ramificationSubgroup (K := κ) A 0))) := by
  intro F L hFL
  -- the ramification subgroups of the decomposition subgroup, and the inclusion into `Gal(M/κ)`
  let G0 : Subgroup ↥(A.decompositionSubgroup κ) :=
    NK.Ramification.ramificationSubgroup (K := κ) A 0
  let G1 : Subgroup ↥(A.decompositionSubgroup κ) :=
    NK.Ramification.ramificationSubgroup (K := κ) A 1
  let φ : ↥(A.decompositionSubgroup κ) →* (M ≃ₐ[κ] M) := (A.decompositionSubgroup κ).subtype
  have hφ : Function.Injective φ := Subgroup.subtype_injective _
  have hle : G1.map φ ≤ G0.map φ :=
    Subgroup.map_mono (NK.Ramification.ramificationSubgroup_le_ramificationSubgroup A (Nat.zero_le 1))
  have hgn : (G1.subgroupOf G0).Normal :=
    (NK.Ramification.ramificationSubgroup_normal A 1).subgroupOf G0
  -- normality of the image subgroup, transported along the injective map `φ`
  have hIm : ((G1.map φ).subgroupOf (G0.map φ)).Normal :=
    (galoisData_map_equivMapOfInjective_subgroupOf φ hφ G0 G1) ▸
      (Subgroup.Normal.map hgn _ (Subgroup.equivMapOfInjective G0 φ hφ).surjective)
  -- the general Galois-theoretic computation
  obtain ⟨hfd, hgal, ⟨e⟩⟩ :=
    galoisDataAux_of_subgroups (H0 := G0.map φ) (H1 := G1.map φ) hle hIm hFL
  refine ⟨hfd, hgal, ⟨e.trans (galoisData_quotientMulEquivOfInjective φ hφ G0 G1).symm⟩⟩

end NK.TameStructureDeep.Tame
