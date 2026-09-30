import Mathlib
import Submission.Work.Cohomology.Crux.vkOvlDefs
import Submission.Work.Cohomology.Crux.ovlRestrictionSurjective
import Submission.Work.Cohomology.Ovl.ovlUnionVanishing
import Submission.Work.Cohomology.Ovl.OvlDefs
import Submission.Work.Cohomology.Endgame.relCohMV_elim

/-!
# The restriction `H⁴(Vk(-2), Mk(-2)) → H⁴(U ∩ V, (U ∩ V) ∩ Mk(-2))` is surjective

`Vk(-2)` is the total space of the rank-`4` disc bundle `ξ` over `S⁴`, `Mk(-2)` its unit sphere
bundle, and `U`, `V` the two chart images of `Vk(-2)`, with overlap `O = U ∩ V`.  The target is the
surjectivity of the restriction map of pairs

  `ρ : H⁴(Vk(-2), Mk(-2)) → H⁴(O, O ∩ Mk(-2))`.

The proof replaces the *closed* sphere bundle by the *open* collar `C = collar(-2)` (which contains
it).  The restriction `λ : H⁴(Vk(-2), C) → H⁴(O, O ∩ C)` is surjective: with `W = O ∪ C` it is the
composite

* `σ` — the restriction of the collar pair to `W`, surjective on `H⁴` by the long exact sequence of
  the triple `C ⊆ W ⊆ Vk(-2)` (`H⁵(Vk(-2), W) = 0`, `Work.Cohomology.Ovl.ovlUnionCollar_vanishing`);
* `τ` — the excision isomorphism `H⁴(W, W ∩ C) ≅ H⁴(O ∩ W, O ∩ W ∩ C)` for the open cover
  `W = (O ∩ W) ∪ (W ∩ C)`;
* `χ` — the pullback along the canonical homeomorphism `O ≅ O ∩ W`, a split epimorphism on `H⁴`.

The two collar inclusions fit into the commuting square of pullbacks `e_X ≫ ρ = λ ≫ e_O`
(`collar_nat`), and the pair inclusions `(Vk(-2), Mk(-2)) → (Vk(-2), C)` and
`(O, O ∩ Mk(-2)) → (O, O ∩ C)` are isomorphisms on relative cohomology (`collarIsoX`, `collarIsoW`).
In degree `4` this reads `ρ* ∘ e_X* = e_O* ∘ λ*` with `e_X*`, `e_O*` isomorphisms and `λ*`
surjective, so `ρ*` is a composite of surjections.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 16000000
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits
open scoped Topology

namespace Work.Cohomology.Crux

noncomputable section

/-! ## The overlap and the collar -/

/-- The overlap `U ∩ V` of the two chart images of `Vk(-2)`. -/
abbrev ovlOf : Set vkPairX := vkU ∩ vkV

/-- The collar of the sphere bundle `Mk(-2)`. -/
abbrev collPairSet : Set vkPairX := Work.Milnor.collar (-2)

/-- The sphere bundle is contained in the collar. -/
theorem mem_collPairSet_of_mem_vkPairA : ∀ x ∈ vkPairA, x ∈ collPairSet := by
  intro x hx
  obtain ⟨z, rfl⟩ := hx
  exact Work.Milnor.mem_collar.mpr (Work.Milnor.one_lt_fibreNorm_mkToVkFun (-2) z)

/-- The trace of the sphere bundle on the overlap is contained in the trace of the collar. -/
theorem mem_ovlA2OfVkOvlA : ∀ x ∈ vkOvlA, x ∈ Work.Cohomology.ovlA2 :=
  fun x hx => mem_collPairSet_of_mem_vkPairA x hx

/-! ## The collar-restriction to the overlap is surjective -/

/-- The union `W = (U ∩ V) ∪ collar(-2)`. -/
abbrev collUnion : Set vkPairX := ovlOf ∪ collPairSet

/-- `W`, as a space. -/
abbrev collUnionSp : TopCat := TopCat.of ↥collUnion

/-- The trace of the collar on `W`. -/
abbrev cwSet : Set ↥collUnion := (Subtype.val : ↥collUnion → vkPairX) ⁻¹' collPairSet

/-- The trace of the overlap on `W`. -/
abbrev uoSet : Set ↥collUnion := (Subtype.val : ↥collUnion → vkPairX) ⁻¹' ovlOf

/-- The trace of the collar on the trace of the overlap. -/
abbrev coSet : Set ↥uoSet := (Subtype.val : ↥uoSet → ↥collUnion) ⁻¹' cwSet

/-- `H⁵(Vk(-2), W) = 0`. -/
theorem collUnion_vanishing : Subsingleton (relCohomology ℤ vkPairX collUnion 5) :=
  Work.Cohomology.Ovl.ovlUnionCollar_vanishing

/-- **The restriction of the collar pair to `W` is surjective on `H⁴`** (the long exact sequence of
the triple `collar ⊆ W ⊆ Vk(-2)`, using `H⁵(Vk(-2), W) = 0`). -/
theorem sigma_surjective :
    Function.Surjective (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
      (relComplexMap (X₁ := TopCat.of ↥collUnion) (X₂ := vkPairX) ℤ cwSet collPairSet
        (subtypeIncl vkPairX collUnion) (fun _ hx => hx)) 4)) :=
  Work.Cohomology.Endgame.tripleLESSurj vkPairX collPairSet collUnion
    (fun _ hx => Or.inr hx) 4 collUnion_vanishing

/-- **Excision**: the restriction `H⁴(W, W ∩ C) → H⁴(O ∩ W, O ∩ W ∩ C)` is an isomorphism (the open
sets `O ∩ W` and `W ∩ C` cover `W`). -/
theorem tau_isIso :
    IsIso (HomologicalComplex.homologyMap
      (relComplexMap (X₁ := TopCat.of ↥uoSet) (X₂ := collUnionSp) ℤ coSet cwSet
        (subtypeIncl collUnionSp uoSet) (fun _ hx => hx)) 4) :=
  Work.Cohomology.openCover_excision_isIso collUnionSp uoSet cwSet
    ((vkU_isOpen.inter vkV_isOpen).preimage continuous_subtype_val)
    ((Work.Milnor.isOpen_collar (-2)).preimage continuous_subtype_val)
    (Set.eq_univ_of_forall (fun x => x.2)) 4 (fun _ hx => hx)

/-- The pullback along the identity of a pair is the identity. -/
theorem relComplexMap_id_local {X : TopCat} (A : Set X) (h : ∀ x ∈ A, (𝟙 X : X ⟶ X) x ∈ A) :
    relComplexMap ℤ A A (𝟙 X) h = 𝟙 (relComplex ℤ X A) := by
  apply HomologicalComplex.hom_ext
  intro n
  rw [Work.Cohomology.relComplexMap_f]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  simp only [ModuleCat.hom_ofHom, Work.Cohomology.relMapLM_coe, Work.Cohomology.dualChainMap_id,
    HomologicalComplex.id_f, ModuleCat.hom_id, LinearMap.id_apply]
  rfl

/-- The canonical homeomorphism `O ≅ O ∩ W`. -/
def eIso : TopCat.of ↥ovlOf ≅ TopCat.of ↥uoSet :=
  Work.Cohomology.Endgame.subPreImageHomeo collUnion ovlOf (fun _ hx => Or.inl hx)

/-- `χ` is a split epimorphism on `H⁴`: the pullback along the inverse homeomorphism is a right
inverse. -/
theorem chi_retract :
    relComplexMap (X₁ := TopCat.of ↥uoSet) (X₂ := TopCat.of ↥ovlOf) ℤ coSet
        Work.Cohomology.ovlA2 eIso.inv (fun _ hx => hx)
      ≫ relComplexMap (X₁ := TopCat.of ↥ovlOf) (X₂ := TopCat.of ↥uoSet) ℤ
        Work.Cohomology.ovlA2 coSet eIso.hom (fun _ hx => hx)
    = 𝟙 (relComplex ℤ (TopCat.of ↥ovlOf) Work.Cohomology.ovlA2) := by
  refine (Work.Cohomology.Ovl.relComplexMap_comp_ovl (X₁ := TopCat.of ↥ovlOf)
    (X₂ := TopCat.of ↥uoSet) (X₃ := TopCat.of ↥ovlOf) Work.Cohomology.ovlA2 coSet
    Work.Cohomology.ovlA2 eIso.hom eIso.inv (fun _ hx => hx) (fun _ hx => hx)).symm.trans ?_
  refine (Work.Cohomology.Ovl.relComplexMap_congr_map (X₁ := TopCat.of ↥ovlOf)
    (X₂ := TopCat.of ↥ovlOf) Work.Cohomology.ovlA2 Work.Cohomology.ovlA2 eIso.hom_inv_id
    (fun _ hx => hx) (fun _ hx => hx)).trans ?_
  exact relComplexMap_id_local (X := TopCat.of ↥ovlOf) Work.Cohomology.ovlA2 (fun _ hx => hx)

/-- A morphism that is a left factor of an identity is surjective. -/
theorem surjective_of_split {A B : ModuleCat ℤ} (f : A ⟶ B) (g : B ⟶ A)
    (h : g ≫ f = 𝟙 B) : Function.Surjective f.hom := by
  intro y
  refine ⟨g.hom y, ?_⟩
  have h2 := congrArg (fun (k : B ⟶ B) => (ModuleCat.Hom.hom k) y) h
  rw [ModuleCat.hom_comp, ModuleCat.hom_id] at h2
  simpa using h2

/-- **The restriction `H⁴(O ∩ W, O ∩ W ∩ C) → H⁴(O, O ∩ C)` is surjective.** -/
theorem chi_surjective :
    Function.Surjective (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
      (relComplexMap (X₁ := TopCat.of ↥ovlOf) (X₂ := TopCat.of ↥uoSet) ℤ
        Work.Cohomology.ovlA2 coSet eIso.hom (fun _ hx => hx)) 4)) :=
  surjective_of_split _
    (HomologicalComplex.homologyMap
      (relComplexMap (X₁ := TopCat.of ↥uoSet) (X₂ := TopCat.of ↥ovlOf) ℤ coSet
        Work.Cohomology.ovlA2 eIso.inv (fun _ hx => hx)) 4)
    (by rw [← HomologicalComplex.homologyMap_comp, chi_retract,
      HomologicalComplex.homologyMap_id])

/-- The restriction of the collar pair to the overlap, with the collar as the subspace of the
overlap. -/
abbrev lamCollar : relComplex ℤ vkPairX collPairSet ⟶
    relComplex ℤ (TopCat.of ↥ovlOf) Work.Cohomology.ovlA2 :=
  relComplexMap (X₁ := TopCat.of ↥ovlOf) (X₂ := vkPairX) ℤ Work.Cohomology.ovlA2 collPairSet
    (subtypeIncl vkPairX ovlOf) (fun _ hx => hx)

/-- The inclusion of pairs `(O, O ∩ C) → (Vk(-2), C)` is the composite of the three restrictions
`σ`, `τ`, `χ` (functoriality of the pullback of relative cochain complexes). -/
theorem lamCollar_eq_composite :
    lamCollar
      = relComplexMap (X₁ := TopCat.of ↥collUnion) (X₂ := vkPairX) ℤ cwSet collPairSet
          (subtypeIncl vkPairX collUnion) (fun _ hx => hx)
        ≫ relComplexMap (X₁ := TopCat.of ↥uoSet) (X₂ := collUnionSp) ℤ coSet cwSet
          (subtypeIncl collUnionSp uoSet) (fun _ hx => hx)
        ≫ relComplexMap (X₁ := TopCat.of ↥ovlOf) (X₂ := TopCat.of ↥uoSet) ℤ
          Work.Cohomology.ovlA2 coSet eIso.hom (fun _ hx => hx) := by
  have hcomp : eIso.hom ≫ subtypeIncl collUnionSp uoSet ≫ subtypeIncl vkPairX collUnion
      = subtypeIncl vkPairX ovlOf :=
    Work.Cohomology.Endgame.subPreImageHomeo_comp collUnion ovlOf (fun _ hx => Or.inl hx)
  rw [show lamCollar = relComplexMap (X₁ := TopCat.of ↥ovlOf) (X₂ := vkPairX) ℤ
      Work.Cohomology.ovlA2 collPairSet (subtypeIncl vkPairX ovlOf) (fun _ hx => hx) from rfl]
  rw [← Work.Cohomology.Ovl.relComplexMap_congr_map (X₁ := TopCat.of ↥ovlOf)
    (X₂ := vkPairX) Work.Cohomology.ovlA2 collPairSet hcomp (fun _ hx => hx) (fun _ hx => hx)]
  rw [Work.Cohomology.Ovl.relComplexMap_comp_ovl (X₁ := TopCat.of ↥ovlOf)
    (X₂ := TopCat.of ↥uoSet) (X₃ := vkPairX) Work.Cohomology.ovlA2 coSet collPairSet eIso.hom
    (subtypeIncl collUnionSp uoSet ≫ subtypeIncl vkPairX collUnion)
    (fun _ hx => hx) (fun _ hx => hx)]
  rw [Work.Cohomology.Ovl.relComplexMap_comp_ovl (X₁ := TopCat.of ↥uoSet)
    (X₂ := collUnionSp) (X₃ := vkPairX) coSet cwSet collPairSet
    (subtypeIncl collUnionSp uoSet) (subtypeIncl vkPairX collUnion)
    (fun _ hx => hx) (fun _ hx => hx)]
  rw [Category.assoc]

/-- **The restriction `H⁴(Vk(-2), collar) → H⁴(O, O ∩ collar)` is surjective.** -/
theorem lamCollar_surjective :
    Function.Surjective (HomologicalComplex.homologyMap lamCollar 4).hom := by
  have htau : Function.Surjective (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
      (relComplexMap (X₁ := TopCat.of ↥uoSet) (X₂ := collUnionSp) ℤ coSet cwSet
        (subtypeIncl collUnionSp uoSet) (fun _ hx => hx)) 4)) := by
    haveI := tau_isIso
    exact (ModuleCat.epi_iff_surjective _).mp inferInstance
  have hcomp : HomologicalComplex.homologyMap lamCollar 4
      = HomologicalComplex.homologyMap
          (relComplexMap (X₁ := TopCat.of ↥collUnion) (X₂ := vkPairX) ℤ cwSet collPairSet
            (subtypeIncl vkPairX collUnion) (fun _ hx => hx)) 4
        ≫ HomologicalComplex.homologyMap
          (relComplexMap (X₁ := TopCat.of ↥uoSet) (X₂ := collUnionSp) ℤ coSet cwSet
            (subtypeIncl collUnionSp uoSet) (fun _ hx => hx)) 4
        ≫ HomologicalComplex.homologyMap
          (relComplexMap (X₁ := TopCat.of ↥ovlOf) (X₂ := TopCat.of ↥uoSet) ℤ
            Work.Cohomology.ovlA2 coSet eIso.hom (fun _ hx => hx)) 4 := by
    rw [lamCollar_eq_composite, HomologicalComplex.homologyMap_comp,
      HomologicalComplex.homologyMap_comp]
  rw [hcomp, ModuleCat.hom_comp, ModuleCat.hom_comp, LinearMap.comp_assoc]
  exact chi_surjective.comp (htau.comp sigma_surjective)

/-! ## The naturality square and the target -/

/-- The target map: the restriction of the pair `(Vk(-2), Mk(-2))` to the overlap. -/
abbrev rhoOverlap : relComplex ℤ vkPairX vkPairA ⟶
    relComplex ℤ (TopCat.of ↥ovlOf) vkOvlA :=
  relComplexMap (X₁ := TopCat.of ↥ovlOf) (X₂ := vkPairX) ℤ vkOvlA vkPairA
    (subtypeIncl vkPairX ovlOf) (fun _ hx => hx)

/-- The inclusion of the sphere-bundle pair into the collar pair, over `Vk(-2)`. -/
abbrev eXCollar : relComplex ℤ vkPairX collPairSet ⟶ relComplex ℤ vkPairX vkPairA :=
  relComplexMap (X₁ := vkPairX) (X₂ := vkPairX) ℤ vkPairA collPairSet (𝟙 vkPairX)
    mem_collPairSet_of_mem_vkPairA

/-- The inclusion of the sphere-bundle pair into the collar pair, over the overlap. -/
abbrev eOCollar : relComplex ℤ (TopCat.of ↥ovlOf) Work.Cohomology.ovlA2 ⟶
    relComplex ℤ (TopCat.of ↥ovlOf) vkOvlA :=
  relComplexMap (X₁ := TopCat.of ↥ovlOf) (X₂ := TopCat.of ↥ovlOf) ℤ vkOvlA
    Work.Cohomology.ovlA2 (𝟙 (TopCat.of ↥ovlOf)) mem_ovlA2OfVkOvlA

/-- Both composites are the pullback along the inclusion of pairs `(O, O ∩ Mk) → (Vk(-2), C)`. -/
theorem collar_nat : eXCollar ≫ rhoOverlap = lamCollar ≫ eOCollar := by
  have h1 := Work.Cohomology.Ovl.relComplexMap_comp_ovl
    (X₁ := TopCat.of ↥ovlOf) (X₂ := vkPairX) (X₃ := vkPairX)
    vkOvlA vkPairA collPairSet (subtypeIncl vkPairX ovlOf) (𝟙 vkPairX)
    (h₁ := fun _ hx => hx) (h₂ := mem_collPairSet_of_mem_vkPairA)
  have h2 := Work.Cohomology.Ovl.relComplexMap_comp_ovl
    (X₁ := TopCat.of ↥ovlOf) (X₂ := TopCat.of ↥ovlOf) (X₃ := vkPairX)
    vkOvlA Work.Cohomology.ovlA2 collPairSet (𝟙 (TopCat.of ↥ovlOf))
    (subtypeIncl vkPairX ovlOf) (h₁ := mem_ovlA2OfVkOvlA) (h₂ := fun _ hx => hx)
  refine h1.symm.trans (((Work.Cohomology.Ovl.relComplexMap_congr_map (X₁ := TopCat.of ↥ovlOf)
    (X₂ := vkPairX) vkOvlA collPairSet
    ((Category.comp_id (subtypeIncl vkPairX ovlOf)).trans (Category.id_comp _).symm)
    (h := fun x hx => mem_collPairSet_of_mem_vkPairA (x : vkPairX) hx)
    (h' := fun x hx => mem_collPairSet_of_mem_vkPairA (x : vkPairX) hx))).trans h2)

/-- The pair inclusion `(Vk(-2), Mk(-2)) → (Vk(-2), C)` is an isomorphism on relative
cohomology. -/
theorem collarIsoX_apply : IsIso (HomologicalComplex.homologyMap eXCollar 4) :=
  Work.Cohomology.collarIsoX 4 mem_collPairSet_of_mem_vkPairA

/-- The pair inclusion `(O, O ∩ Mk(-2)) → (O, O ∩ C)` is an isomorphism on relative
cohomology. -/
theorem collarIsoO_apply : IsIso (HomologicalComplex.homologyMap eOCollar 4) :=
  Work.Cohomology.collarIsoW 4 mem_ovlA2OfVkOvlA

/-- **The restriction `H⁴(Vk(-2), Mk(-2)) → H⁴(O, O ∩ Mk(-2))` is surjective.** -/
theorem surj_rhoOverlap : Function.Surjective (HomologicalComplex.homologyMap rhoOverlap 4).hom := by
  haveI hXi : IsIso (HomologicalComplex.homologyMap eXCollar 4) := collarIsoX_apply
  haveI hOi : IsIso (HomologicalComplex.homologyMap eOCollar 4) := collarIsoO_apply
  have hlam : Function.Surjective (HomologicalComplex.homologyMap lamCollar 4).hom :=
    lamCollar_surjective
  -- the naturality square in degree `4`
  have hnat4 : (HomologicalComplex.homologyMap rhoOverlap 4).hom.comp
        (HomologicalComplex.homologyMap eXCollar 4).hom
      = (HomologicalComplex.homologyMap eOCollar 4).hom.comp
        (HomologicalComplex.homologyMap lamCollar 4).hom := by
    have h : (HomologicalComplex.homologyMap (eXCollar ≫ rhoOverlap) 4).hom
        = (HomologicalComplex.homologyMap (lamCollar ≫ eOCollar) 4).hom := by
      rw [collar_nat]
    rw [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp] at h
    rwa [ModuleCat.hom_comp, ModuleCat.hom_comp] at h
  intro y
  obtain ⟨y', hy'⟩ := (ConcreteCategory.bijective_of_isIso
    (HomologicalComplex.homologyMap eOCollar 4)).2 y
  obtain ⟨w, hw⟩ := hlam y'
  refine ⟨(HomologicalComplex.homologyMap eXCollar 4).hom w, ?_⟩
  have h := congrArg (fun f => f w) hnat4
  simp only [LinearMap.comp_apply] at h
  rw [h, hw, hy']

/-- **The restriction `H⁴(Vk(-2), Mk(-2)) → H⁴(U ∩ V, (U ∩ V) ∩ Mk(-2))` is surjective.** -/
theorem ovlRestrSurjCompat :
    Function.Surjective (HomologicalComplex.homologyMap
      (relComplexMap ℤ Work.Cohomology.Crux.vkOvlA Work.Cohomology.vkPairA
        (subtypeIncl Work.Cohomology.vkPairX (Work.Cohomology.Crux.vkU ∩ Work.Cohomology.Crux.vkV))
        (fun _ hx => hx)) 4) :=
  surj_rhoOverlap

end

end Work.Cohomology.Crux
