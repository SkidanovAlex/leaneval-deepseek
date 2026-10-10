import Mathlib
import ChallengeDeps
import Submission.Work.Motivic.Defs
import Submission.Work.CY3.GenericPointAux
import Submission.Work.CY3.structMap_fromSpecStalk
import Submission.Work.CY3.isDominant_ofFromSpecStalk_hom
import Submission.Work.CY3.fromFunctionField_comp_ofFromSpecStalk
import Submission.Work.CY3.exists_theta_of_resEquiv

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false
set_option linter.unnecessarySimpa false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Work.CY3

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme

/-- **Function fields and birationality.**  Two `𝕜`-varieties whose generic points have
`𝕜`-isomorphic residue fields (equivalently: isomorphic function fields over `𝕜`) are birational
over `𝕜`. -/
theorem resEquiv_genericPoint_birationalMap {𝕜 : Type} [Field 𝕜]
    {X Y : AlgebraicGeometry.Scheme.{0}} [MotivicInvariants.Variety 𝕜 X]
    [MotivicInvariants.Variety 𝕜 Y]
    (h : ResEquiv 𝕜 (genericPoint X) (genericPoint Y)) :
    Nonempty (AlgebraicGeometry.Scheme.BirationalMap X Y) := by
  haveI : IsIntegral X := MotivicInvariants.Variety.isIntegral 𝕜
  haveI : IsIntegral Y := MotivicInvariants.Variety.isIntegral 𝕜
  haveI hftX : LocallyOfFiniteType (X ↘ Spec (CommRingCat.of 𝕜)) :=
    MotivicInvariants.Variety.locallyOfFiniteType
  haveI hftY : LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of 𝕜)) :=
    MotivicInvariants.Variety.locallyOfFiniteType
  -- ## the ring isomorphism of function fields
  obtain ⟨θ, hθ⟩ := exists_theta_of_resEquiv (𝕜 := 𝕜) h
  have hθ' : θ.toRingHom.comp (structMap 𝕜 X) = structMap 𝕜 Y := by
    rw [← hθ]; ext a; simp
  -- ## the base and the two structure maps
  let sX : X ⟶ Spec (CommRingCat.of 𝕜) := X ↘ Spec (CommRingCat.of 𝕜)
  let sY : Y ⟶ Spec (CommRingCat.of 𝕜) := Y ↘ Spec (CommRingCat.of 𝕜)
  have hstX : X.fromSpecStalk (genericPoint X) ≫ sX =
      Spec.map (CommRingCat.ofHom (structMap 𝕜 X)) := structMap_fromSpecStalk 𝕜 X
  have hstY : Y.fromSpecStalk (genericPoint Y) ≫ sY =
      Spec.map (CommRingCat.ofHom (structMap 𝕜 Y)) := structMap_fromSpecStalk 𝕜 Y
  -- ## the two `Spec κ(-) ⟶ -` maps which will spread out to rational maps
  let g : Spec X.functionField ⟶ Y :=
    Spec.map (CommRingCat.ofHom θ.symm.toRingHom) ≫ Y.fromSpecStalk (genericPoint Y)
  let g' : Spec Y.functionField ⟶ X :=
    Spec.map (CommRingCat.ofHom θ.toRingHom) ≫ X.fromSpecStalk (genericPoint X)
  have hg : g ≫ sY = X.fromSpecStalk (genericPoint X) ≫ sX := by
    calc g ≫ sY
        = Spec.map (CommRingCat.ofHom θ.symm.toRingHom) ≫ (Y.fromSpecStalk (genericPoint Y) ≫ sY) :=
          Category.assoc _ _ _
      _ = Spec.map (CommRingCat.ofHom θ.symm.toRingHom) ≫
            Spec.map (CommRingCat.ofHom (structMap 𝕜 Y)) := by rw [hstY]
      _ = Spec.map (CommRingCat.ofHom (θ.symm.toRingHom.comp (structMap 𝕜 Y))) := by
            rw [← Spec.map_comp]; rfl
      _ = Spec.map (CommRingCat.ofHom (structMap 𝕜 X)) := by rw [hθ]
      _ = X.fromSpecStalk (genericPoint X) ≫ sX := hstX.symm
  have hg' : g' ≫ sX = Y.fromSpecStalk (genericPoint Y) ≫ sY := by
    calc g' ≫ sX
        = Spec.map (CommRingCat.ofHom θ.toRingHom) ≫ (X.fromSpecStalk (genericPoint X) ≫ sX) :=
          Category.assoc _ _ _
      _ = Spec.map (CommRingCat.ofHom θ.toRingHom) ≫
            Spec.map (CommRingCat.ofHom (structMap 𝕜 X)) := by rw [hstX]
      _ = Spec.map (CommRingCat.ofHom (θ.toRingHom.comp (structMap 𝕜 X))) := by
            rw [← Spec.map_comp]; rfl
      _ = Spec.map (CommRingCat.ofHom (structMap 𝕜 Y)) := by rw [hθ']
      _ = Y.fromSpecStalk (genericPoint Y) ≫ sY := hstY.symm
  -- ## the two partial maps, their dominance, and the two rational maps
  haveI hdf : IsDominant (PartialMap.ofFromSpecStalk sX sY g hg).hom :=
    isDominant_ofFromSpecStalk_hom sX sY g hg (CommRingCat.ofHom θ.symm.toRingHom) rfl
  haveI hdf' : IsDominant (PartialMap.ofFromSpecStalk sY sX g' hg').hom :=
    isDominant_ofFromSpecStalk_hom sY sX g' hg' (CommRingCat.ofHom θ.toRingHom) rfl
  let φ : X ⤏ Y := (PartialMap.ofFromSpecStalk sX sY g hg).toRationalMap
  let ψ : Y ⤏ X := (PartialMap.ofFromSpecStalk sY sX g' hg').toRationalMap
  haveI : φ.IsDominant :=
    (PartialMap.isDominant_toRationalMap_iff _).mpr hdf
  haveI : ψ.IsDominant :=
    (PartialMap.isDominant_toRationalMap_iff _).mpr hdf'
  -- ## the two round trips
  have hcompθ : (CommRingCat.ofHom θ.toRingHom ≫ CommRingCat.ofHom θ.symm.toRingHom) =
      𝟙 X.functionField := by
    rw [← CommRingCat.ofHom_comp]
    rw [show θ.symm.toRingHom.comp θ.toRingHom = RingHom.id _ from
      RingHom.ext fun a => θ.symm_apply_apply a]
    rw [← CommRingCat.hom_id (R := X.functionField), CommRingCat.ofHom_hom]
  have hcompθ' : (CommRingCat.ofHom θ.symm.toRingHom ≫ CommRingCat.ofHom θ.toRingHom) =
      𝟙 Y.functionField := by
    rw [← CommRingCat.ofHom_comp]
    rw [show θ.toRingHom.comp θ.symm.toRingHom = RingHom.id _ from
      RingHom.ext fun a => θ.apply_symm_apply a]
    rw [← CommRingCat.hom_id (R := Y.functionField), CommRingCat.ofHom_hom]
  have hsq : (Spec.map (CommRingCat.ofHom θ.symm.toRingHom) ≫
      Spec.map (CommRingCat.ofHom θ.toRingHom)) = 𝟙 (Spec X.functionField) := by
    rw [← Spec.map_comp, hcompθ]
    exact Spec.map_id X.functionField
  have hsq' : (Spec.map (CommRingCat.ofHom θ.toRingHom) ≫
      Spec.map (CommRingCat.ofHom θ.symm.toRingHom)) = 𝟙 (Spec Y.functionField) := by
    rw [← Spec.map_comp, hcompθ']
    exact Spec.map_id Y.functionField
  have hroundX : ((PartialMap.ofFromSpecStalk sX sY g hg).comp
      (PartialMap.ofFromSpecStalk sY sX g' hg')).fromFunctionField =
      X.fromSpecStalk (genericPoint X) := by
    rw [fromFunctionField_comp_ofFromSpecStalk sX sY g hg
      (PartialMap.ofFromSpecStalk sY sX g' hg') (CommRingCat.ofHom θ.symm.toRingHom) rfl]
    rw [show (PartialMap.ofFromSpecStalk sY sX g' hg').fromFunctionField = g' from
      PartialMap.fromSpecStalkOfMem_ofFromSpecStalk sY sX g' hg']
    rw [show g' = Spec.map (CommRingCat.ofHom θ.toRingHom) ≫ X.fromSpecStalk (genericPoint X)
      from rfl]
    rw [← Category.assoc, hsq, Category.id_comp]
  have hroundY : ((PartialMap.ofFromSpecStalk sY sX g' hg').comp
      (PartialMap.ofFromSpecStalk sX sY g hg)).fromFunctionField =
      Y.fromSpecStalk (genericPoint Y) := by
    rw [fromFunctionField_comp_ofFromSpecStalk sY sX g' hg'
      (PartialMap.ofFromSpecStalk sX sY g hg) (CommRingCat.ofHom θ.toRingHom) rfl]
    rw [show (PartialMap.ofFromSpecStalk sX sY g hg).fromFunctionField = g from
      PartialMap.fromSpecStalkOfMem_ofFromSpecStalk sX sY g hg]
    rw [show g = Spec.map (CommRingCat.ofHom θ.symm.toRingHom) ≫ Y.fromSpecStalk (genericPoint Y)
      from rfl]
    rw [← Category.assoc, hsq', Category.id_comp]
  have hidXFF : (PartialMap.id X).fromFunctionField = X.fromSpecStalk (genericPoint X) := by
    have hh := PartialMap.fromSpecStalkOfMem_toPartialMap (𝟙 X) (genericPoint X)
    simpa [PartialMap.id, PartialMap.fromFunctionField] using hh
  have hidYFF : (PartialMap.id Y).fromFunctionField = Y.fromSpecStalk (genericPoint Y) := by
    have hh := PartialMap.fromSpecStalkOfMem_toPartialMap (𝟙 Y) (genericPoint Y)
    simpa [PartialMap.id, PartialMap.fromFunctionField] using hh
  have hrecX : ∀ h : genericPoint X ∈ ((PartialMap.ofFromSpecStalk sX sY g hg).comp
      (PartialMap.ofFromSpecStalk sY sX g' hg')).domain,
      ((PartialMap.ofFromSpecStalk sX sY g hg).comp
        (PartialMap.ofFromSpecStalk sY sX g' hg')).fromSpecStalkOfMem h =
      X.fromSpecStalk (genericPoint X) := by
    intro h
    rw [← hroundX, PartialMap.fromFunctionField]
  have hrecidX : ∀ h : genericPoint X ∈ (PartialMap.id X).domain,
      (PartialMap.id X).fromSpecStalkOfMem h = X.fromSpecStalk (genericPoint X) := by
    intro h
    rw [← hidXFF, PartialMap.fromFunctionField]
  have hrecY : ∀ h : genericPoint Y ∈ ((PartialMap.ofFromSpecStalk sY sX g' hg').comp
      (PartialMap.ofFromSpecStalk sX sY g hg)).domain,
      ((PartialMap.ofFromSpecStalk sY sX g' hg').comp
        (PartialMap.ofFromSpecStalk sX sY g hg)).fromSpecStalkOfMem h =
      Y.fromSpecStalk (genericPoint Y) := by
    intro h
    rw [← hroundY, PartialMap.fromFunctionField]
  have hrecidY : ∀ h : genericPoint Y ∈ (PartialMap.id Y).domain,
      (PartialMap.id Y).fromSpecStalkOfMem h = Y.fromSpecStalk (genericPoint Y) := by
    intro h
    rw [← hidYFF, PartialMap.fromFunctionField]
  have hgenmemX : ∀ (U : X.Opens), (U : Set X).Nonempty → genericPoint X ∈ U :=
    fun U hU => (IsGenericPoint.mem_open_set_iff (genericPoint_spec X) U.2).mpr (by simpa using hU)
  have hgenmemY : ∀ (U : Y.Opens), (U : Set Y).Nonempty → genericPoint Y ∈ U :=
    fun U hU => (IsGenericPoint.mem_open_set_iff (genericPoint_spec Y) U.2).mpr (by simpa using hU)
  have hmemX : genericPoint X ∈ ((PartialMap.ofFromSpecStalk sX sY g hg).comp
      (PartialMap.ofFromSpecStalk sY sX g' hg')).domain :=
    hgenmemX _ ((PartialMap.ofFromSpecStalk sX sY g hg).comp
      (PartialMap.ofFromSpecStalk sY sX g' hg')).dense_domain.nonempty
  have hmemY : genericPoint Y ∈ ((PartialMap.ofFromSpecStalk sY sX g' hg').comp
      (PartialMap.ofFromSpecStalk sX sY g hg)).domain :=
    hgenmemY _ ((PartialMap.ofFromSpecStalk sY sX g' hg').comp
      (PartialMap.ofFromSpecStalk sX sY g hg)).dense_domain.nonempty
  have hmemidX : genericPoint X ∈ (PartialMap.id X).domain :=
    hgenmemX _ (PartialMap.id X).dense_domain.nonempty
  have hmemidY : genericPoint Y ∈ (PartialMap.id Y).domain :=
    hgenmemY _ (PartialMap.id Y).dense_domain.nonempty
  have hidX : ((PartialMap.ofFromSpecStalk sX sY g hg).comp
      (PartialMap.ofFromSpecStalk sY sX g' hg')).equiv (PartialMap.id X) :=
    PartialMap.equiv_of_fromSpecStalkOfMem_eq (x := genericPoint X) _ _ hmemX hmemidX
      ((hrecX _).trans (hrecidX _).symm)
  have hidY : ((PartialMap.ofFromSpecStalk sY sX g' hg').comp
      (PartialMap.ofFromSpecStalk sX sY g hg)).equiv (PartialMap.id Y) :=
    PartialMap.equiv_of_fromSpecStalkOfMem_eq (x := genericPoint Y) _ _ hmemY hmemidY
      ((hrecY _).trans (hrecidY _).symm)
  -- ## conclusion
  have hcompX : φ.comp ψ = RationalMap.id X := by
    change (PartialMap.ofFromSpecStalk sX sY g hg).toRationalMap.comp
        (PartialMap.ofFromSpecStalk sY sX g' hg').toRationalMap = (PartialMap.id X).toRationalMap
    rw [RationalMap.comp_def, PartialMap.toRationalMap_eq_iff]
    exact (PartialMap.comp_equiv_of_equiv_left
      (PartialMap.representative_toRationalMap_equiv (PartialMap.ofFromSpecStalk sX sY g hg))
      _).trans hidX
  have hcompY : ψ.comp φ = RationalMap.id Y := by
    change (PartialMap.ofFromSpecStalk sY sX g' hg').toRationalMap.comp
        (PartialMap.ofFromSpecStalk sX sY g hg).toRationalMap = (PartialMap.id Y).toRationalMap
    rw [RationalMap.comp_def, PartialMap.toRationalMap_eq_iff]
    exact (PartialMap.comp_equiv_of_equiv_left
      (PartialMap.representative_toRationalMap_equiv (PartialMap.ofFromSpecStalk sY sX g' hg'))
      _).trans hidY
  exact ⟨⟨φ, ψ, hcompX, hcompY⟩⟩

end Work.CY3
