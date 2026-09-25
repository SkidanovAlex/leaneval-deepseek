import Mathlib
import Submission.NK.NUV2.LC.RouteB.RouteBDeps
import Submission.NK.NUV2.LC.RouteB.kummerMap_locUnits
import Submission.NK.NUV2.LC.RouteB.unitsLift_kummerLevel
import Submission.NK.NUV2.LC.RouteB.levelGroupEquiv_symm_mem_range_localInclHom
import Submission.NK.HassePrinciple.ArithmeticForm
import Submission.NK.HassePrinciple.map_levelRestrict_stabSubgroup
import Submission.NK.HassePrinciple.IndexInput
import Submission.NeukirchUchida.Local.PlaceFromValuation

/-!
# The local dictionary: `locLevel`-vanishing implies `locL`-vanishing for Kummer images

The main result `NK.NUV2.LC.RouteB.locL_kummerLevel_of_locLevel_eq_zero` states that if the
twisted level class `levelCompare p V L c` is locally trivial at a place `A` of `K'` over a finite
place `q` of `L`, then the `LevelGroup`-based localisation `locL` of the Kummer image of `c` at `q`
vanishes.

The proof reduces the statement to the transport of the same local triviality between the two
models of the level `μ_p`-cohomology:

* `muLevelRestrictCoeff` is the restriction morphism `V → V ⊓ D_A` of the `μ_p` level
  representations in the `NK.HassePrinciple` model;
* `map_muLevelRestrictCoeff_eq_zero` (via the naturality `H2congr_map` of the model comparison
  `NK.NUV2.ABHN.muLevelMulEquiv`) converts the hypothesis in the `NK.BrauerTwist` model into
  the vanishing of the local restriction in the `NK.HassePrinciple` model;
* `muLevelRep_rho_theta` and `muLevelRepModelCompare` identify the two local coefficient modules
  (`Gal(↥L/K)`-model and `Gal(↥L/↥(levelBase V L))`-model) along the arithmetic isomorphism
  `LevelGroup V L ≃* Gal(↥L/↥(levelBase V L))` restricted to the decomposition subgroup;
* `NK.NUV2.LC.RouteB.levelGroupEquiv_symm_mem_range_localInclHom` (a separate file) supplies the
  arithmetic fact that every element of the decomposition subgroup `Γ_q` of the place `q` is the
  image of an element of the local level group `(V ⊓ D_A)/(V ⊓ D_A ⊓ Gal(K'/L))`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

namespace NK.NUV2.LC.RouteB

open CategoryTheory

variable {K K' : Type} [Field K] [NumberField K] [Field K'] [Algebra K K'] [IsSepClosure K K']

open NK.HassePrinciple

private theorem levelGroupRestrictHom_comp_localInclHom (V : Subgroup Gal(K'/K)) (A : ValuationSubring K')
    (L : FiniteGaloisIntermediateField K K') :
    (NK.HassePrinciple.levelGroupRestrictHom V L).comp
        (NK.BrauerHasse.localInclHom V A L)
      = NK.HassePrinciple.levelGroupRestrictHom (V ⊓ NK.BrauerHasse.stabSubgroup A) L := by
  apply MonoidHom.ext
  intro x
  induction x using QuotientGroup.induction_on with
  | H u =>
    simp only [MonoidHom.comp_apply, NK.BrauerHasse.localInclHom, QuotientGroup.map_mk,
      MonoidHom.id_apply, NK.HassePrinciple.levelGroupRestrictHom_mk, Subgroup.coe_inclusion]

private theorem smul_rootsOfUnity_congr {E : Type} [Field E] [Algebra K E]
    {F : IntermediateField K E} {p : ℕ}
    (σ : E ≃ₐ[K] E) (τ : E ≃ₐ[↥F] E) (h : ∀ x : E, σ x = τ x)
    (z : rootsOfUnity p E) : σ • z = τ • z := by
  apply Subtype.ext
  simp only [NK.HassePrinciple.coe_smul_rootsOfUnity, AlgEquiv.smul_units_def]
  rw [show (σ : E →* E) = (τ : E →* E) from MonoidHom.ext (fun x => h x)]

private noncomputable def muLevelRestrictCoeff (p : ℕ) (V : Subgroup Gal(K'/K)) (A : ValuationSubring K')
    (L : FiniteGaloisIntermediateField K K') :
    Rep.res (NK.BrauerHasse.localInclHom V A L)
        (NK.HassePrinciple.muLevelRep (K := K) (K' := K') p V L) ⟶
      NK.HassePrinciple.muLevelRep (K := K) (K' := K')
        p (V ⊓ NK.BrauerHasse.stabSubgroup A) L :=
  Rep.ofHom (LinearMap.intertwiningMap_of_isIntertwiningMap
    (ρ := (Rep.res (NK.BrauerHasse.localInclHom V A L)
      (NK.HassePrinciple.muLevelRep (K := K) (K' := K') p V L)).ρ)
    (σ := (NK.HassePrinciple.muLevelRep (K := K) (K' := K')
      p (V ⊓ NK.BrauerHasse.stabSubgroup A) L).ρ)
    (f := LinearMap.id)
    (fun q x => by
      induction q using QuotientGroup.induction_on with
      | H u =>
        simp only [NK.BrauerHasse.localInclHom, QuotientGroup.map_mk, MonoidHom.id_apply,
          LinearMap.id_coe, LinearMap.id_apply]
        rfl))

private theorem map_muLevelRestrictCoeff_eq_zero (p : ℕ) (V : Subgroup Gal(K'/K))
    (L : FiniteGaloisIntermediateField K K')
    (A : NK.BrauerTwist.OverFinitePrime K K')
    (c : NK.HassePrinciple.MuLevelH2 (K := K) (K' := K') p V L)
    (h : NK.BrauerTwist.locLevel p V A.1 L ((NK.NUV2.ABHN.levelCompare p V L) c) = 0) :
    (groupCohomology.map (NK.BrauerHasse.localInclHom V A.1 L)
      (muLevelRestrictCoeff (K := K) (K' := K') p V A.1 L) 2).hom c = 0 := by
  let W : Subgroup Gal(K'/K) := V ⊓ NK.BrauerHasse.stabSubgroup A.1
  let e := (NK.NUV2.ABHN.muLevelMulEquiv (K := K) (K' := K') p L).toAdditive
  let e' := (NK.NUV2.ABHN.muLevelMulEquiv (K := K) (K' := K') p L).toAdditive
  have he : ∀ (g : NK.BrauerHasse.LevelGroup V L)
      (y : Additive ↥(rootsOfUnity p ↥L)),
      e ((NK.HassePrinciple.muLevelRep.{0, 0} (K := K) (K' := K') p V L).ρ g y) =
        (NK.BrauerTwist.levelRep.{0, 0} (K := K) (K' := K') p V L).ρ g (e y) :=
    NK.NUV2.ABHN.muLevelMulEquiv_smul (K := K) (K' := K') p V L
  have he' : ∀ (g : NK.BrauerHasse.LevelGroup W L)
      (y : Additive ↥(rootsOfUnity p ↥L)),
      e' ((NK.HassePrinciple.muLevelRep.{0, 0} (K := K) (K' := K') p W L).ρ g y) =
        (NK.BrauerTwist.levelRep.{0, 0} (K := K) (K' := K') p W L).ρ g (e' y) :=
    NK.NUV2.ABHN.muLevelMulEquiv_smul (K := K) (K' := K') p W L
  have hφψ : ∀ x : (NK.HassePrinciple.muLevelRep.{0, 0} (K := K) (K' := K') p V L).V,
      e' x = (NK.BrauerTwist.locCoeff.{0, 0} p V A.1 L).hom (e x) := by
    intro x
    rfl
  have hmap := NK.NUV2.ABHN.H2congr_map
    (f := NK.BrauerHasse.localInclHom V A.1 L)
    (muLevelRestrictCoeff (K := K) (K' := K') p V A.1 L)
    (NK.BrauerTwist.locCoeff p V A.1 L)
    e e' he he' hφψ c
  have hzero : (groupCohomology.map (NK.BrauerHasse.localInclHom V A.1 L)
      (NK.BrauerTwist.locCoeff p V A.1 L) 2).hom
      (NK.NUV2.ABHN.H2congr e he c) = 0 := h
  rw [hzero] at hmap
  have h0 : NK.NUV2.ABHN.H2congr (A := NK.HassePrinciple.muLevelRep.{0, 0} (K := K) (K' := K') p W L)
        (B := NK.BrauerTwist.levelRep.{0, 0} (K := K) (K' := K') p W L) e' he'
      ((groupCohomology.map (NK.BrauerHasse.localInclHom V A.1 L)
        (muLevelRestrictCoeff (K := K) (K' := K') p V A.1 L) 2).hom c) =
      NK.NUV2.ABHN.H2congr (A := NK.HassePrinciple.muLevelRep.{0, 0} (K := K) (K' := K') p W L)
        (B := NK.BrauerTwist.levelRep.{0, 0} (K := K) (K' := K') p W L) e' he' 0 := by
    rw [NK.NUV2.ABHN.H2congr_zero]
    exact hmap
  exact (NK.NUV2.ABHN.H2congrEquiv (A := NK.HassePrinciple.muLevelRep.{0, 0} (K := K) (K' := K') p W L)
        (B := NK.BrauerTwist.levelRep.{0, 0} (K := K) (K' := K') p W L) e' he').injective h0

private theorem muLevelRep_rho_theta (p : ℕ) (V : Subgroup Gal(K'/K))
    (L : FiniteGaloisIntermediateField K K') (A : ValuationSubring K')
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥L))
    (θ : MulAction.stabilizer (↥L ≃ₐ[↥(levelBase (K := K) V L)] ↥L)
        (NK.GlobalCFT.Place.ofFinite q) →* NK.BrauerHasse.LocalLevelGroup V A L)
    (hθ : ∀ γ : MulAction.stabilizer (↥L ≃ₐ[↥(levelBase (K := K) V L)] ↥L)
        (NK.GlobalCFT.Place.ofFinite q),
        NK.BrauerHasse.localInclHom V A L (θ γ) =
          (levelGroupEquiv (K := K) (K' := K') V L).symm
            (γ : ↥L ≃ₐ[↥(levelBase (K := K) V L)] ↥L)) :
    ∀ (γ : MulAction.stabilizer (↥L ≃ₐ[↥(levelBase (K := K) V L)] ↥L)
        (NK.GlobalCFT.Place.ofFinite q)) (y : Additive ↥(rootsOfUnity p ↥L)),
      (NK.HassePrinciple.muLevelRep (K := K) (K' := K') p
        (V ⊓ NK.BrauerHasse.stabSubgroup A) L).ρ (θ γ) y =
        (NK.HassePrinciple.muRep p ↥(levelBase (K := K) V L) ↥L).ρ
          (γ : ↥L ≃ₐ[↥(levelBase (K := K) V L)] ↥L) y := by
  intro γ y
  simp only [NK.HassePrinciple.muLevelRep, Rep.coe_res_obj_ρ']
  rw [← levelGroupRestrictHom_comp_localInclHom V A L]
  simp only [MonoidHom.comp_apply, hθ γ]
  exact congrArg Additive.ofMul (smul_rootsOfUnity_congr (K := K)
    (NK.HassePrinciple.levelGroupRestrictHom V L
      ((levelGroupEquiv (K := K) (K' := K') V L).symm
        (γ : ↥L ≃ₐ[↥(levelBase (K := K) V L)] ↥L)))
    (γ : ↥L ≃ₐ[↥(levelBase (K := K) V L)] ↥L)
    (fun x => by
      rw [← levelGroupEquiv_apply (K := K) (K' := K') V L
        ((levelGroupEquiv (K := K) (K' := K') V L).symm
          (γ : ↥L ≃ₐ[↥(levelBase (K := K) V L)] ↥L)) x]
      simp)
    (Additive.toMul y))

private noncomputable def muLevelRepModelCompare (p : ℕ) (V : Subgroup Gal(K'/K))
    (L : FiniteGaloisIntermediateField K K') (A : ValuationSubring K')
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥L))
    (θ : MulAction.stabilizer (↥L ≃ₐ[↥(levelBase (K := K) V L)] ↥L)
        (NK.GlobalCFT.Place.ofFinite q) →* NK.BrauerHasse.LocalLevelGroup V A L)
    (hθ : ∀ γ : MulAction.stabilizer (↥L ≃ₐ[↥(levelBase (K := K) V L)] ↥L)
        (NK.GlobalCFT.Place.ofFinite q),
        NK.BrauerHasse.localInclHom V A L (θ γ) =
          (levelGroupEquiv (K := K) (K' := K') V L).symm
            (γ : ↥L ≃ₐ[↥(levelBase (K := K) V L)] ↥L)) :
    Rep.res θ (NK.HassePrinciple.muLevelRep (K := K) (K' := K') p
        (V ⊓ NK.BrauerHasse.stabSubgroup A) L) ⟶
      Rep.res (MulAction.stabilizer (↥L ≃ₐ[↥(levelBase (K := K) V L)] ↥L)
          (NK.GlobalCFT.Place.ofFinite q)).subtype
        (NK.HassePrinciple.muRep p ↥(levelBase (K := K) V L) ↥L) :=
  Rep.ofHom (LinearMap.intertwiningMap_of_isIntertwiningMap
    (ρ := (Rep.res θ (NK.HassePrinciple.muLevelRep (K := K) (K' := K') p
      (V ⊓ NK.BrauerHasse.stabSubgroup A) L)).ρ)
    (σ := (Rep.res (MulAction.stabilizer (↥L ≃ₐ[↥(levelBase (K := K) V L)] ↥L)
        (NK.GlobalCFT.Place.ofFinite q)).subtype
      (NK.HassePrinciple.muRep p ↥(levelBase (K := K) V L) ↥L)).ρ)
    (f := LinearMap.id)
    (fun γ y => by
      simp only [Rep.coe_res_obj_ρ', NK.HassePrinciple.muLevelRep]
      rw [← levelGroupRestrictHom_comp_localInclHom V A L]
      simp only [MonoidHom.comp_apply, hθ γ]
      exact congrArg Additive.ofMul (smul_rootsOfUnity_congr (K := K)
        (NK.HassePrinciple.levelGroupRestrictHom V L
          ((levelGroupEquiv (K := K) (K' := K') V L).symm
            (γ : ↥L ≃ₐ[↥(levelBase (K := K) V L)] ↥L)))
        (γ : ↥L ≃ₐ[↥(levelBase (K := K) V L)] ↥L)
        (fun x => by
          rw [← levelGroupEquiv_apply (K := K) (K' := K') V L
            ((levelGroupEquiv (K := K) (K' := K') V L).symm
              (γ : ↥L ≃ₐ[↥(levelBase (K := K) V L)] ↥L)) x]
          simp)
        (Additive.toMul y))))


private theorem locL_kummerLevel_crux (p : ℕ) (V : Subgroup Gal(K'/K)) (L : FiniteGaloisIntermediateField K K')
    (hF : L.fixingSubgroup ≤ V)
    (c : NK.HassePrinciple.MuLevelH2 (K := K) (K' := K') p V L)
    (A : NK.BrauerTwist.OverFinitePrime K K')
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥L))
    (hA : A.1.comap (algebraMap ↥L K') =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥L q)
    (h : NK.BrauerTwist.locLevel p V A.1 L ((NK.NUV2.ABHN.levelCompare p V L) c) = 0) :
    (ModuleCat.Hom.hom
      ((groupCohomology.resNatTrans NK.HassePrinciple.CoeffInt
        (G := MulAction.stabilizer (↥L ≃ₐ[↥(levelBase (K := K) V L)] ↥L)
          (NK.GlobalCFT.Place.ofFinite q))
        (H := (↥L ≃ₐ[↥(levelBase (K := K) V L)] ↥L))
        (MulAction.stabilizer (↥L ≃ₐ[↥(levelBase (K := K) V L)] ↥L)
          (NK.GlobalCFT.Place.ofFinite q)).subtype 2).app
        (NK.HassePrinciple.muRep p ↥(levelBase (K := K) V L) ↥L)))
      (muLift (K := K) (K' := K') p V L c) = 0 := by
  let Γ : Subgroup (↥L ≃ₐ[↥(levelBase (K := K) V L)] ↥L) :=
    MulAction.stabilizer (↥L ≃ₐ[↥(levelBase (K := K) V L)] ↥L)
      (NK.GlobalCFT.Place.ofFinite q)
  have hex : ∀ γ : Γ, ∃ δ : NK.BrauerHasse.LocalLevelGroup V A.1 L,
      NK.BrauerHasse.localInclHom V A.1 L δ =
        (levelGroupEquiv (K := K) (K' := K') V L).symm
          (γ : ↥L ≃ₐ[↥(levelBase (K := K) V L)] ↥L) :=
    fun γ => levelGroupEquiv_symm_mem_range_localInclHom V L hF A q hA γ
  let θ : Γ →* NK.BrauerHasse.LocalLevelGroup V A.1 L :=
    { toFun := fun γ => Classical.choose (hex γ)
      map_one' := NK.HassePrinciple.localInclHom_injective V A.1 L (by
        rw [Classical.choose_spec (hex 1), Subgroup.coe_one, map_one, map_one])
      map_mul' := fun γ δ => NK.HassePrinciple.localInclHom_injective V A.1 L (by
        rw [map_mul, Classical.choose_spec (hex (γ * δ)), Subgroup.coe_mul, map_mul,
          Classical.choose_spec (hex γ), Classical.choose_spec (hex δ)]) }
  have hθ : ∀ γ : Γ, NK.BrauerHasse.localInclHom V A.1 L (θ γ) =
      (levelGroupEquiv (K := K) (K' := K') V L).symm
        (γ : ↥L ≃ₐ[↥(levelBase (K := K) V L)] ↥L) := fun γ => Classical.choose_spec (hex γ)
  let ψθ := muLevelRepModelCompare (K := K) (K' := K') p V L A.1 q θ hθ
  have hρ : (NK.BrauerHasse.localInclHom V A.1 L).comp θ =
      (levelGroupEquiv (K := K) (K' := K') V L).symm.toMonoidHom.comp Γ.subtype := by
    ext γ
    exact hθ γ
  let ψ'' : Rep.res ((NK.BrauerHasse.localInclHom V A.1 L).comp θ)
      (NK.HassePrinciple.muLevelRep (K := K) (K' := K') p V L) ⟶
      Rep.res Γ.subtype (NK.HassePrinciple.muRep p ↥(levelBase (K := K) V L) ↥L) :=
    (Rep.resFunctor θ).map (muLevelRestrictCoeff (K := K) (K' := K') p V A.1 L) ≫ ψθ
  rw [muLift_apply, groupCohomology.mapIso_hom, groupCohomology.resNatTrans_app]
  change (ModuleCat.Hom.hom ((groupCohomology.map
      (↑(levelGroupEquiv (K := K) (K' := K') V L).symm) _ 2) ≫
    (groupCohomology.map Γ.subtype _ 2))) c = 0
  rw [← groupCohomology.map_comp]
  have key : (groupCohomology.map ((NK.BrauerHasse.localInclHom V A.1 L).comp θ) ψ'' 2).hom c = 0 := by
    rw [groupCohomology.map_comp]
    rw [ModuleCat.comp_apply]
    rw [map_muLevelRestrictCoeff_eq_zero p V L A c h]
    exact map_zero _
  refine Eq.trans ?_ key
  refine congrArg (fun (z : groupCohomology (NK.HassePrinciple.muLevelRep (K := K) (K' := K') p V L) 2 ⟶
      groupCohomology (Rep.res Γ.subtype
        (NK.HassePrinciple.muRep p ↥(levelBase (K := K) V L) ↥L)) 2) =>
        ModuleCat.Hom.hom z c) ?_
  exact groupCohomology.map_congr hρ.symm (by ext x; rfl) 2

theorem locL_kummerLevel_of_locLevel_eq_zero {K K' : Type} [Field K] [NumberField K] [Field K']
    [Algebra K K'] [IsSepClosure K K'] (p : ℕ) (V : Subgroup Gal(K'/K))
    (L : FiniteGaloisIntermediateField K K') (hF : L.fixingSubgroup ≤ V)
    (c : NK.HassePrinciple.MuLevelH2 (K := K) (K' := K') p V L)
    (A : NK.BrauerTwist.OverFinitePrime K K')
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥L))
    (hA : A.1.comap (algebraMap ↥L K') =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥L q)
    (h : NK.BrauerTwist.locLevel p V A.1 L ((NK.NUV2.ABHN.levelCompare p V L) c) = 0) :
    NK.NUV2.LC.RouteB.locL (K := K) (K' := K') V L (NK.GlobalCFT.Place.ofFinite q)
      ((NK.HassePrinciple.kummerLevel p V L).hom c) = 0 := by
  have hcrit := locL_kummerLevel_crux (K := K) (K' := K') p V L hF c A q hA h
  have h1 : NK.NUV2.LC.RouteB.unitsLift (K := K) (K' := K') V L
      ((NK.HassePrinciple.kummerLevel p V L).hom c) =
      (NK.HassePrinciple.kummerMap p ↥(NK.NUV2.LC.RouteB.levelBase (K := K) V L) ↥L).hom
        (muLift (K := K) (K' := K') p V L c) :=
    unitsLift_kummerLevel (K := K) (K' := K') p V L c
  rw [NK.NUV2.LC.RouteB.locL, h1]
  exact kummerMap_locUnits (F := ↥(levelBase (K := K) V L)) (L := ↥L) p
    (NK.GlobalCFT.Place.ofFinite q) (muLift (K := K) (K' := K') p V L c) hcrit

end NK.NUV2.LC.RouteB
