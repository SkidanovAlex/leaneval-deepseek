import Mathlib
import Submission.NK.CFTLib.IdeleHasse.localNormSubgroup
import Submission.NK.CFTLib.IdeleHasse.localFaithfulDefs
import Submission.NK.CFTLib.IdeleHasse.range_localNormFinite_eq_of_liesOver
import Submission.NK.CFTLib.IdeleHasse.Descent.transferCore
import Submission.NK.CFTLib.IdeleHasse.Descent.transferLevels
import Submission.NK.CFTLib.IdeleHasse.Crux.cycClass
import Submission.NK.CFTLib.IdeleHasse.Crux.localNormRep
import Submission.NK.CFTLib.IdeleHasse.Crux.zpowersSubgroup
import Submission.NK.GlobalCFTdeep.HasseNormTheorem
import Submission.NK.CFTLib.IdeleHasse.mem_normImage_iff_localNorm
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open NK.GlobalCFT CategoryTheory
open scoped NumberField

namespace NK.CFTLib.HR.TransferAux

open IsDedekindDomain IdeleHasse

attribute [local instance 5000] Rep.hV1 Rep.hV2

/-! ## Universe-pinned coefficient representations -/

/-- `NK.HassePrinciple.localUnitsRep K F w` with all universes pinned to `0`. -/
noncomputable abbrev lurep (K F : Type) [Field K] [NumberField K] [Field F] [NumberField F]
    [Algebra K F] [FiniteDimensional K F] [IsGalois K F] (w : Place F) :
    Rep.{0,0,0} NK.HassePrinciple.CoeffInt ↥(MulAction.stabilizer (F ≃ₐ[K] F) w) :=
  NK.HassePrinciple.localUnitsRep K F w

/-- The image of a global element in the units of a Galois level is fixed by the Galois action
(universe-pinned version of `NK.CFTLib.IdeleHasse.Descent.unitsRep_apply_unitsImage`). -/
lemma urep_rho_unitsImage {K F : Type} [Field K] [Field F] [Algebra K F]
    (σ : F ≃ₐ[K] F) (x : Kˣ) :
    (NK.CFTLib.IdeleHasse.Crux.urep K F).ρ σ (NK.CFTLib.IdeleHasse.Descent.unitsImage x)
      = NK.CFTLib.IdeleHasse.Descent.unitsImage x := by
  apply Additive.ofMul.injective
  apply Units.ext
  show σ (algebraMap K F (x : K)) = algebraMap K F (x : K)
  exact σ.commutes (x : K)

/-- Restriction of the fixed element to a decomposition group. -/
lemma res_urep_rho_unitsImage {K F : Type} [Field K] [NumberField K] [Field F] [NumberField F]
    [Algebra K F] (w : Place F) (γ : ↥(MulAction.stabilizer (F ≃ₐ[K] F) w)) (x : Kˣ) :
    (Rep.res (MulAction.stabilizer (F ≃ₐ[K] F) w).subtype
        (NK.CFTLib.IdeleHasse.Crux.urep K F)).ρ γ
        (NK.CFTLib.IdeleHasse.Descent.unitsImage x)
      = NK.CFTLib.IdeleHasse.Descent.unitsImage x :=
  urep_rho_unitsImage γ.1 x

/-! ## The localisation dictionary at a finite place -/

/-- The two ways of mapping `Kˣ` into the units of the completion `F_qˣ` agree: via `K → F → F_q`
and via `K → K_Q → F_q`. -/
lemma unitsToLocalUnitsHom_eq_localAlgebraMapUnits {K F : Type} [Field K] [NumberField K]
    [Field F] [NumberField F] [Algebra K F] [IsGalois K F] (q : HeightOneSpectrum (𝓞 F))
    (Q : HeightOneSpectrum (𝓞 K)) (hq : q.asIdeal.LiesOver Q.asIdeal) (x : Kˣ) :
    NK.HassePrinciple.unitsToLocalUnitsHom (Place.ofFinite q)
        (Units.map (algebraMap K F).toMonoidHom x)
      = Place.localAlgebraMapUnits (Place.ofFinite q) (Place.ofFinite Q)
            (Place.liesOver_ofFinite hq)
          (localImageAt (K := K) (Place.ofFinite Q) x) := by
  apply Units.ext
  rw [NK.GlobalCFT.Galois.localAlgebraMapUnits_ofFinite hq]
  show (algebraMap F (q.adicCompletion F) ((algebraMap K F) (x : K)))
    = Commons.RingTheory.Henselian.adicCompletionMap Q q hq
        (((x : K) : Q.adicCompletion K))
  exact (Commons.RingTheory.Henselian.adicCompletionMap_apply Q q hq (x : K)).symm

/-- **The localisation dictionary at a finite place**: the image of the cyclic class of `x` under
the localisation at a finite place `q` vanishes if and only if the local component of `x` is a norm
from the local field `F_q` over `K_Q`. -/
theorem locUnits_cycClassOf_eq_zero_iff_ofFinite {K F : Type} [Field K] [NumberField K]
    [Field F] [NumberField F] [Algebra K F] [FiniteDimensional K F] [IsGalois K F]
    [IsCyclic (F ≃ₐ[K] F)] (q : HeightOneSpectrum (𝓞 F))
    [Fintype ↥(MulAction.stabilizer (F ≃ₐ[K] F) (Place.ofFinite q))]
    (g : F ≃ₐ[K] F) (hg : ∀ σ : F ≃ₐ[K] F, σ ∈ Subgroup.zpowers g) (x : Kˣ) :
    (NK.HassePrinciple.locUnits K F (Place.ofFinite q)).hom
        (NK.CFTLib.IdeleHasse.Descent.cycClassOf g hg x) = 0 ↔
      Additive.ofMul (NK.HassePrinciple.unitsToLocalUnitsHom (Place.ofFinite q)
          (Units.map (algebraMap K F).toMonoidHom x)) ∈
        (Rep.Hom.hom (lurep K F (Place.ofFinite q)).norm).range := by
  obtain ⟨m, hm_eq, hm_card⟩ := NK.CFTLib.IdeleHasse.Crux.exists_zpowers_pow_eq_of_isCyclic g hg
    (MulAction.stabilizer (F ≃ₐ[K] F) (Place.ofFinite q))
  let gG : ↥(MulAction.stabilizer (F ≃ₐ[K] F) (Place.ofFinite q)) :=
    ⟨g ^ m, by rw [hm_eq]; exact Subgroup.mem_zpowers _⟩
  have hgG : ∀ x : ↥(MulAction.stabilizer (F ≃ₐ[K] F) (Place.ofFinite q)),
      x ∈ Subgroup.zpowers gG := by
    intro x
    obtain ⟨k, hk⟩ : (x : F ≃ₐ[K] F) ∈ Subgroup.zpowers (g ^ m) := by
      rw [← hm_eq]; exact x.2
    exact Subgroup.mem_zpowers_iff.mpr ⟨k, Subtype.ext (by
      show ↑(gG ^ k) = (x : F ≃ₐ[K] F)
      rw [Subgroup.coe_zpow]
      exact hk)⟩
  have hcard : m * Fintype.card ↥(MulAction.stabilizer (F ≃ₐ[K] F) (Place.ofFinite q))
      = Fintype.card (F ≃ₐ[K] F) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
    exact hm_card
  have hsub : (MulAction.stabilizer (F ≃ₐ[K] F) (Place.ofFinite q)).subtype gG = g ^ m := rfl
  have hinv1 : ∀ γ : ↥(MulAction.stabilizer (F ≃ₐ[K] F) (Place.ofFinite q)),
      (Rep.res (MulAction.stabilizer (F ≃ₐ[K] F) (Place.ofFinite q)).subtype
        (NK.CFTLib.IdeleHasse.Crux.urep K F)).ρ γ
        (NK.CFTLib.IdeleHasse.Descent.unitsImage x)
      = NK.CFTLib.IdeleHasse.Descent.unitsImage x :=
    fun γ => res_urep_rho_unitsImage (Place.ofFinite q) γ x
  have hinv2 : ∀ γ : ↥(MulAction.stabilizer (F ≃ₐ[K] F) (Place.ofFinite q)),
      (lurep K F (Place.ofFinite q)).ρ γ
        ((NK.HassePrinciple.unitsToLocalUnits K F (Place.ofFinite q)).hom
          (NK.CFTLib.IdeleHasse.Descent.unitsImage x))
      = (NK.HassePrinciple.unitsToLocalUnits K F (Place.ofFinite q)).hom
          (NK.CFTLib.IdeleHasse.Descent.unitsImage x) := by
    intro γ
    rw [← Rep.hom_comm_apply (NK.HassePrinciple.unitsToLocalUnits K F (Place.ofFinite q))
      γ (NK.CFTLib.IdeleHasse.Descent.unitsImage x), hinv1 γ]
  have hloc : (NK.HassePrinciple.locUnits K F (Place.ofFinite q)).hom
      (NK.CFTLib.IdeleHasse.Descent.cycClassOf g hg x)
      = (groupCohomology.map (MonoidHom.id ↥(MulAction.stabilizer (F ≃ₐ[K] F) (Place.ofFinite q)))
            (NK.HassePrinciple.unitsToLocalUnits K F (Place.ofFinite q)) 2).hom
        ((groupCohomology.map (MulAction.stabilizer (F ≃ₐ[K] F) (Place.ofFinite q)).subtype
            (𝟙 (Rep.res (MulAction.stabilizer (F ≃ₐ[K] F) (Place.ofFinite q)).subtype
              (NK.CFTLib.IdeleHasse.Crux.urep K F))) 2).hom
          (NK.CFTLib.IdeleHasse.Descent.cycClassOf g hg x)) := by
    rw [NK.HassePrinciple.locUnits]
    exact ConcreteCategory.comp_apply _ _ _
  rw [hloc, show NK.CFTLib.IdeleHasse.Descent.cycClassOf g hg x
      = NK.CFTLib.Descent.cycClass (NK.CFTLib.IdeleHasse.Crux.urep K F) g hg
          (NK.CFTLib.IdeleHasse.Descent.unitsImage x)
          (fun σ => urep_rho_unitsImage σ x) from rfl]
  rw [NK.CFTLib.IdeleHasse.Descent.map_cycClass (NK.CFTLib.IdeleHasse.Crux.urep K F)
      (Rep.res (MulAction.stabilizer (F ≃ₐ[K] F) (Place.ofFinite q)).subtype
        (NK.CFTLib.IdeleHasse.Crux.urep K F))
      (MulAction.stabilizer (F ≃ₐ[K] F) (Place.ofFinite q)).subtype g hg gG hgG m hsub hcard
      (𝟙 (Rep.res (MulAction.stabilizer (F ≃ₐ[K] F) (Place.ofFinite q)).subtype
        (NK.CFTLib.IdeleHasse.Crux.urep K F)))
      (NK.CFTLib.IdeleHasse.Descent.unitsImage x)
      (fun σ => urep_rho_unitsImage σ x)
      (NK.CFTLib.IdeleHasse.Descent.unitsImage x) rfl hinv1]
  rw [NK.CFTLib.IdeleHasse.Descent.map_cycClass
      (Rep.res (MulAction.stabilizer (F ≃ₐ[K] F) (Place.ofFinite q)).subtype
        (NK.CFTLib.IdeleHasse.Crux.urep K F))
      (lurep K F (Place.ofFinite q))
      (MonoidHom.id _) gG hgG gG hgG 1 (by simp) (by simp)
      (NK.HassePrinciple.unitsToLocalUnits K F (Place.ofFinite q))
      (NK.CFTLib.IdeleHasse.Descent.unitsImage x) hinv1
      ((NK.HassePrinciple.unitsToLocalUnits K F (Place.ofFinite q)).hom
        (NK.CFTLib.IdeleHasse.Descent.unitsImage x)) rfl hinv2]
  rw [NK.CFTLib.IdeleHasse.Descent.cycClass_eq_zero_iff
      (lurep K F (Place.ofFinite q)) gG hgG
      ((NK.HassePrinciple.unitsToLocalUnits K F (Place.ofFinite q)).hom
        (NK.CFTLib.IdeleHasse.Descent.unitsImage x)) hinv2]
  show Additive.ofMul ((NK.HassePrinciple.unitsToLocalUnitsHom (Place.ofFinite q)
        (Units.map (algebraMap K F).toMonoidHom x))) ∈
      (Rep.Hom.hom (lurep K F (Place.ofFinite q)).norm).range ↔ _
  exact Iff.rfl


/-! ## The level inflation map `H²(Gal(M/K), Mˣ) → H²(Gal(E/K), Eˣ)` -/

section Inflation

variable {K M E : Type} [Field K] [Field M] [Field E]
  [Algebra K M] [Algebra K E] [Algebra M E] [IsScalarTower K M E]

/-- The units inclusion `Mˣ → Eˣ` as a `CoeffInt`-linear map. -/
noncomputable def unitsInclLinearMap (K M E : Type) [Field K] [Field M] [Field E]
    [Algebra K M] [Algebra K E] [Algebra M E] [IsScalarTower K M E] :
    Additive Mˣ →ₗ[NK.HassePrinciple.CoeffInt] Additive Eˣ where
  toFun := ⇑(Units.map (algebraMap M E).toMonoidHom).toAdditive
  map_add' := map_add _
  map_smul' n x := by
    obtain ⟨z⟩ := n
    exact map_zsmul _ z x

@[simp]
theorem unitsInclLinearMap_apply (x : Additive Mˣ) :
    unitsInclLinearMap K M E x
      = Additive.ofMul (Units.map (algebraMap M E).toMonoidHom (Additive.toMul x)) := rfl

/-- **The coefficient morphism of the level inflation map**: the units inclusion `Mˣ → Eˣ` as a
morphism of representations over the restriction `Gal(E/K) →* Gal(M/K)`. -/
noncomputable def unitsInclCoeff (K M E : Type) [Field K] [Field M] [Field E]
    [Algebra K M] [Algebra K E] [Algebra M E] [IsScalarTower K M E] [Normal K M] :
    Rep.res (AlgEquiv.restrictNormalHom (K₁ := E) (E := M))
        (NK.CFTLib.IdeleHasse.Crux.urep K M) ⟶ NK.CFTLib.IdeleHasse.Crux.urep K E :=
  Rep.ofHom
    { toLinearMap := unitsInclLinearMap K M E
      isIntertwining' := fun σ => by
        apply LinearMap.ext
        intro x
        set y : Mˣ := Additive.toMul x with hy
        show Additive.ofMul (Units.map (algebraMap M E).toMonoidHom
            (Units.map (((AlgEquiv.restrictNormalHom (K₁ := E) (E := M)) σ)).toMonoidHom y))
          = Additive.ofMul ((σ : E ≃ₐ[K] E) • Units.map (algebraMap M E).toMonoidHom y)
        rw [AlgEquiv.smul_units_def]
        congr 1
        apply Units.ext
        simp only [Units.coe_map]
        rw [show (AlgEquiv.restrictNormalHom (K₁ := E) (E := M)) σ = σ.restrictNormal M from rfl]
        exact AlgEquiv.restrictNormal_commutes (F := K) σ M y }

/-- **The level inflation map** `H²(Gal(M/K), Mˣ) → H²(Gal(E/K), Eˣ)`. -/
noncomputable def levelInfMap (K M E : Type) [Field K] [Field M] [Field E]
    [Algebra K M] [Algebra K E] [Algebra M E] [IsScalarTower K M E] [Normal K M] :
    groupCohomology (NK.CFTLib.IdeleHasse.Crux.urep K M) 2 ⟶
      groupCohomology (NK.CFTLib.IdeleHasse.Crux.urep K E) 2 :=
  groupCohomology.map (AlgEquiv.restrictNormalHom (K₁ := E) (E := M))
    (unitsInclCoeff K M E) 2

end Inflation

/-- **The restriction of a class at the level `E/K` to the subgroup `Gal(E/M)`** (the "descent"
map of the transfer step). -/
noncomputable def resToM (K M E : Type) [Field K] [Field M] [Field E]
    [Algebra K M] [Algebra K E] [Algebra M E] [IsScalarTower K M E] [Normal K M] :
    groupCohomology (NK.CFTLib.IdeleHasse.Crux.urep K E) 2 ⟶
      groupCohomology (Rep.res ((AlgEquiv.restrictNormalHom (K₁ := E) (E := M)).ker).subtype
        (NK.CFTLib.IdeleHasse.Crux.urep K E)) 2 :=
  groupCohomology.map ((AlgEquiv.restrictNormalHom (K₁ := E) (E := M)).ker).subtype
    (𝟙 (Rep.res ((AlgEquiv.restrictNormalHom (K₁ := E) (E := M)).ker).subtype
      (NK.CFTLib.IdeleHasse.Crux.urep K E))) 2


end NK.CFTLib.HR.TransferAux
