import Mathlib
import Submission.Work.SSGRoute.sha2_hasse.Gateway
import Submission.Work.SSGRoute.sha2_hasse.place_dictionary
import Submission.Work.SSGRoute.sha2_hasse.exists_section_of_decomp
import Submission.Work.SSGRoute.sha2_hasse.locUnits_levelClass_eq_zero_of_section
import Submission.Work.SSGRoute.sha2_hasse.unitsLevelMapTower_levelClass_eq
import Submission.Work.SSGRoute.sha2_hasse.exists_level_values_and_invariance
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped NumberField Pointwise
open CategoryTheory

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

namespace Work.SSGRoute.sha2_hasse

variable {k : Type} [Field k] [NumberField k]

/-- **The explicit `2`-cocycle condition for `d` on `G_k`**, deduced from the fact that the
descended cocycle at the level `L` is a cocycle. -/
theorem cocycle_condition_of_mem_cocycles₂
    (L : FiniteGaloisIntermediateField k (AlgebraicClosure k))
    (d : (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) →
      (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) → Additive (AlgebraicClosure k)ˣ)
    (hfac : ∀ g h u v : AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k,
      u ∈ (L : IntermediateField k (AlgebraicClosure k)).fixingSubgroup →
      v ∈ (L : IntermediateField k (AlgebraicClosure k)).fixingSubgroup →
      d (g * u) (h * v) = d g h)
    (hvals : ∀ g h : AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k,
      ∃ x : (Lf L)ˣ, inclUnits L (Additive.ofMul x) = d g h)
    (hmem : (fun p : (Lf L ≃ₐ[k] Lf L) × (Lf L ≃ₐ[k] Lf L) =>
        levelCocycle L d hvals p.1 p.2) ∈
      groupCohomology.cocycles₂ (NK.HassePrinciple.unitsRep k (Lf L))) :
    ∀ g h l : AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k,
      d (g * h) l + d g h = g • d h l + d g (h * l) := by
  intro g h l
  have key := (groupCohomology.mem_cocycles₂_iff
    (A := NK.HassePrinciple.unitsRep k (Lf L))
    (fun p : (Lf L ≃ₐ[k] Lf L) × (Lf L ≃ₐ[k] Lf L) => levelCocycle L d hvals p.1 p.2)).mp
      hmem (levelRes L g) (levelRes L h) (levelRes L l)
  have h1 : inclUnits L (levelCocycle L d hvals (levelRes L g * levelRes L h) (levelRes L l)
      + levelCocycle L d hvals (levelRes L g) (levelRes L h)) = d (g * h) l + d g h := by
    rw [map_add]
    congr 1
    · exact levelCocycle_value L d hvals hfac _ _ (g * h) l (map_mul _ g h) rfl
    · exact levelCocycle_value L d hvals hfac _ _ g h rfl rfl
  have h2 : inclUnits L ((levelRes L g) • levelCocycle L d hvals (levelRes L h) (levelRes L l)
      + levelCocycle L d hvals (levelRes L g) (levelRes L h * levelRes L l))
      = g • d h l + d g (h * l) := by
    rw [map_add]
    congr 1
    · rw [inclUnits_smul]
      congr 1
      exact levelCocycle_value L d hvals hfac _ _ h l rfl rfl
    · exact levelCocycle_value L d hvals hfac _ _ g (h * l) rfl (map_mul _ h l)
  rw [← h1, ← h2, key]
  rfl

/-- **The values of `d` lie in any level above `L`.** -/
theorem hvals_of_le
    (L E : FiniteGaloisIntermediateField k (AlgebraicClosure k))
    (hLE : (L : IntermediateField k (AlgebraicClosure k)) ≤
      (E : IntermediateField k (AlgebraicClosure k)))
    [Algebra (Lf L) (Lf E)] [IsScalarTower k (Lf L) (Lf E)]
    [IsScalarTower (Lf L) (Lf E) (AlgebraicClosure k)]
    (d : (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) →
      (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) → Additive (AlgebraicClosure k)ˣ)
    (hvals : ∀ g h : AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k,
      ∃ x : (Lf L)ˣ, inclUnits L (Additive.ofMul x) = d g h) :
    ∀ g h : AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k,
      ∃ x : (Lf E)ˣ, inclUnits E (Additive.ofMul x) = d g h := by
  intro g h
  obtain ⟨x, hx⟩ := hvals g h
  refine ⟨Units.map (algebraMap (Lf L) (Lf E)).toMonoidHom x, ?_⟩
  rw [inclUnits_ofMul, ← hx, inclUnits_ofMul]
  congr 1
  apply Units.ext
  show (algebraMap (Lf E) (AlgebraicClosure k))
      ((algebraMap (Lf L) (Lf E)) (((x : Lf L)) : Lf L))
    = (algebraMap (Lf L) (AlgebraicClosure k)) (((x : Lf L)) : Lf L)
  exact (IsScalarTower.algebraMap_apply (Lf L) (Lf E) (AlgebraicClosure k)
    (((x : Lf L)) : Lf L)).symm

/-- **`hfac` for a level above `L`.** -/
theorem hfac_of_le
    (L E : FiniteGaloisIntermediateField k (AlgebraicClosure k))
    (hLE : (L : IntermediateField k (AlgebraicClosure k)) ≤
      (E : IntermediateField k (AlgebraicClosure k)))
    (d : (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) →
      (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) → Additive (AlgebraicClosure k)ˣ)
    (hfac : ∀ g h u v : AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k,
      u ∈ (L : IntermediateField k (AlgebraicClosure k)).fixingSubgroup →
      v ∈ (L : IntermediateField k (AlgebraicClosure k)).fixingSubgroup →
      d (g * u) (h * v) = d g h) :
    ∀ g h u v : AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k,
      u ∈ (E : IntermediateField k (AlgebraicClosure k)).fixingSubgroup →
      v ∈ (E : IntermediateField k (AlgebraicClosure k)).fixingSubgroup →
      d (g * u) (h * v) = d g h :=
  fun g h u v hu hv => hfac g h u v
    (IntermediateField.fixingSubgroup_antitone hLE hu)
    (IntermediateField.fixingSubgroup_antitone hLE hv)


theorem locUnits_levelClass_eq_zero_finitePlace
    {k : Type} [Field k] [NumberField k]
    (d : (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) →
      (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) → Additive (AlgebraicClosure k)ˣ)
    (L : FiniteGaloisIntermediateField k (AlgebraicClosure k))
    (hfac : ∀ g h u v : AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k,
      u ∈ (L : IntermediateField k (AlgebraicClosure k)).fixingSubgroup →
      v ∈ (L : IntermediateField k (AlgebraicClosure k)).fixingSubgroup →
      d (g * u) (h * v) = d g h)
    (hvals : ∀ g h : AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k,
      ∃ x : (Work.SSGRoute.sha2_hasse.Lf L)ˣ,
        Work.SSGRoute.sha2_hasse.inclUnits L (Additive.ofMul x) = d g h)
    (hDA : ∀ A : ValuationSubring (AlgebraicClosure k), SSGRoute.IsFinPlace k A →
      ∃ b : (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) → Additive (AlgebraicClosure k)ˣ,
        SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b ∧
        ∀ g ∈ SSGRoute.decomp k A, ∀ h ∈ SSGRoute.decomp k A,
          d g h = g • b h - b (g * h) + b g)
    (hmem : (fun p : (Work.SSGRoute.sha2_hasse.Lf L ≃ₐ[k] Work.SSGRoute.sha2_hasse.Lf L) ×
        (Work.SSGRoute.sha2_hasse.Lf L ≃ₐ[k] Work.SSGRoute.sha2_hasse.Lf L) =>
        Work.SSGRoute.sha2_hasse.levelCocycle L d hvals p.1 p.2)
      ∈ groupCohomology.cocycles₂
          (NK.HassePrinciple.unitsRep k (Work.SSGRoute.sha2_hasse.Lf L)))
    (q : IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers (Work.SSGRoute.sha2_hasse.Lf L))) :
    (NK.HassePrinciple.locUnits k (Work.SSGRoute.sha2_hasse.Lf L)
        (NK.GlobalCFT.Place.ofFinite q)).hom
      (Work.SSGRoute.sha2_hasse.levelClass L d hvals hmem) = 0 := by
  classical
  -- ## a place `A` of `k̄` over `q`, and the prime `p` of `k` below it
  obtain ⟨A, p, hAq, hAp⟩ := exists_valuationSubring_at_prime_of_heightOneSpectrum (k := k) L q
  have hAfin : SSGRoute.IsFinPlace k A := by
    rw [SSGRoute.IsFinPlace, hAp]
    exact Submission.NeukirchUchida.Local.valuationSubringAtPrime_ne_top (K := k) p
  -- ## the local witness `b` on the decomposition group of `A`
  obtain ⟨b, hblc, hbcob⟩ := hDA A hAfin
  -- ## a finite Galois level `E ⊇ L` carrying the values of `b` on `D_A`
  obtain ⟨E, hLE, hbval, hbinv⟩ := exists_level_values_and_invariance (k := k) L p A hAp b hblc
  -- ## the tower structure on `L ⊆ E`
  let algLE : Algebra (Lf L) (Lf E) := (IntermediateField.inclusion hLE).toRingHom.toAlgebra
  letI : Algebra (Lf L) (Lf E) := algLE
  haveI hST₁ : IsScalarTower k (Lf L) (Lf E) := by
    refine IsScalarTower.of_algebraMap_eq (fun x => ?_)
    apply Subtype.ext
    rfl
  haveI hST₂ : IsScalarTower (Lf L) (Lf E) (AlgebraicClosure k) := by
    refine IsScalarTower.of_algebraMap_eq (fun x => ?_)
    rfl
  haveI hGal : IsGalois (Lf L) (Lf E) := IsGalois.tower_top_of_isGalois k (Lf L) (Lf E)
  -- ## the place of `E` induced by `A`
  let qE : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers (Lf E)) :=
    Submission.NeukirchUchida.Local.placeOf p A hAp (E : IntermediateField k (AlgebraicClosure k))
  have hlies : (NK.GlobalCFT.Place.ofFinite qE).LiesOver (NK.GlobalCFT.Place.ofFinite q) :=
    NK.GlobalCFT.Place.liesOver_ofFinite
      (placeOf_asIdeal_liesOver (k := k) L E hLE p A hAp q hAq)
  -- ## the level-`E` data
  have hfacE := hfac_of_le (k := k) L E hLE d hfac
  have hvalsE := hvals_of_le (k := k) L E hLE d hvals
  have hd := cocycle_condition_of_mem_cocycles₂ (k := k) L d hfac hvals hmem
  have hmemE : (fun p : (Lf E ≃ₐ[k] Lf E) × (Lf E ≃ₐ[k] Lf E) =>
      levelCocycle E d hvalsE p.1 p.2) ∈
      groupCohomology.cocycles₂ (NK.HassePrinciple.unitsRep k (Lf E)) :=
    (groupCohomology.mem_cocycles₂_iff (A := NK.HassePrinciple.unitsRep k (Lf E))
      (fun p : (Lf E ≃ₐ[k] Lf E) × (Lf E ≃ₐ[k] Lf E) => levelCocycle E d hvalsE p.1 p.2)).mpr
      (levelCocycle_isCocycle E d hvalsE hfacE hd)
  -- ## the section of `D_A → Stab(q_E)` and the local triviality at `E`
  obtain ⟨σ, hσmem, hσres⟩ := exists_section_of_decomp (k := k) p A hAp E
  have hinv' : ∀ γ δ, b (σ γ * σ δ) = b (σ (γ * δ)) := by
    intro γ δ
    have hu : (σ (γ * δ))⁻¹ * (σ γ * σ δ) ∈
        (E : IntermediateField k (AlgebraicClosure k)).fixingSubgroup := by
      rw [← mem_ker_levelRes_iff E ((σ (γ * δ))⁻¹ * (σ γ * σ δ))]
      rw [map_mul, map_inv, map_mul, hσres γ, hσres δ, hσres (γ * δ)]
      simp [Subgroup.coe_mul]
    have huD : (σ (γ * δ))⁻¹ * (σ γ * σ δ) ∈ SSGRoute.decomp k A :=
      (SSGRoute.decomp k A).mul_mem ((SSGRoute.decomp k A).inv_mem (hσmem (γ * δ)))
        ((SSGRoute.decomp k A).mul_mem (hσmem γ) (hσmem δ))
    simpa [mul_inv_cancel_left] using hbinv (σ (γ * δ)) (hσmem (γ * δ))
      ((σ (γ * δ))⁻¹ * (σ γ * σ δ)) hu huD
  have hval' : ∀ γ, ((Additive.toMul (b (σ γ)) : (AlgebraicClosure k)ˣ) :
      AlgebraicClosure k) ∈ (E : IntermediateField k (AlgebraicClosure k)) :=
    fun γ => hbval (σ γ) (hσmem γ)
  have hC := locUnits_levelClass_eq_zero_of_section (k := k) E d hfacE hvalsE hmemE A qE b
    hbcob σ hσmem hσres hval' hinv'
  -- ## the tower square
  have hB := unitsLevelMapTower_levelClass_eq (k := k) L E hLE d hfac hvals hvalsE hmem hmemE
  have hsq := NK.NUV2.LC.RouteB.unitsLevelMapTower_comp_locUnits (F := k) (L := Lf L) (M := Lf E)
    (w := NK.GlobalCFT.Place.ofFinite q) (w' := NK.GlobalCFT.Place.ofFinite qE) hlies
  have h1 : (NK.NUV2.LC.RouteB.localLevelMap hlies).hom
      ((NK.HassePrinciple.locUnits k (Lf L) (NK.GlobalCFT.Place.ofFinite q)).hom
        (levelClass L d hvals hmem)) = 0 := by
    have hthis := congrArg (fun (f : groupCohomology (NK.HassePrinciple.unitsRep k (Lf L)) 2 ⟶
        groupCohomology (NK.HassePrinciple.localUnitsRep k (Lf E)
          (NK.GlobalCFT.Place.ofFinite qE)) 2) => f.hom (levelClass L d hvals hmem)) hsq
    simp only [ModuleCat.comp_apply] at hthis
    rw [hB] at hthis
    rw [hC] at hthis
    exact hthis.symm
  -- ## injectivity of the local level map
  exact NK.CFTLib.HR.TransferAux.localLevelMap_injective_vanishing
    (NK.GlobalCFT.Place.ofFinite q) (NK.GlobalCFT.Place.ofFinite qE) hlies _ h1

end Work.SSGRoute.sha2_hasse
