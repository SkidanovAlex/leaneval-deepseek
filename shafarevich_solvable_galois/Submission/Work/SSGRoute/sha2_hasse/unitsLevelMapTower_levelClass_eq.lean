import Submission.Work.SSGRoute.sha2_hasse.Gateway
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

/-- **The tower map on level classes.**  For finite Galois levels `L ≤ E` of `k̄/k`, the tower
level map `unitsLevelMapTower : H²(Gal(L/k), Lˣ) → H²(Gal(E/k), Eˣ)` carries the level class of a
descended cocycle `d` at `L` to the level class of `d` at `E`. -/
theorem unitsLevelMapTower_levelClass_eq
    (L E : FiniteGaloisIntermediateField k (AlgebraicClosure k))
    (hLE : (L : IntermediateField k (AlgebraicClosure k)) ≤
      (E : IntermediateField k (AlgebraicClosure k)))
    [Algebra (Lf L) (Lf E)] [IsScalarTower k (Lf L) (Lf E)]
    [IsScalarTower (Lf L) (Lf E) (AlgebraicClosure k)]
    (d : (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) →
      (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) → Additive (AlgebraicClosure k)ˣ)
    (hfac : ∀ g h u v : AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k,
      u ∈ (L : IntermediateField k (AlgebraicClosure k)).fixingSubgroup →
      v ∈ (L : IntermediateField k (AlgebraicClosure k)).fixingSubgroup →
      d (g * u) (h * v) = d g h)
    (hvals : ∀ g h : AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k,
      ∃ x : (Lf L)ˣ, inclUnits L (Additive.ofMul x) = d g h)
    (hvalsE : ∀ g h : AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k,
      ∃ x : (Lf E)ˣ, inclUnits E (Additive.ofMul x) = d g h)
    (hmem : (fun p : (Lf L ≃ₐ[k] Lf L) × (Lf L ≃ₐ[k] Lf L) =>
        levelCocycle L d hvals p.1 p.2) ∈
      groupCohomology.cocycles₂ (NK.HassePrinciple.unitsRep k (Lf L)))
    (hmemE : (fun p : (Lf E ≃ₐ[k] Lf E) × (Lf E ≃ₐ[k] Lf E) =>
        levelCocycle E d hvalsE p.1 p.2) ∈
      groupCohomology.cocycles₂ (NK.HassePrinciple.unitsRep k (Lf E))) :
    NK.NUV2.LC.unitsLevelMapTower (levelClass L d hvals hmem) = levelClass E d hvalsE hmemE := by
  -- `hfac` for the level `E` (its fixing subgroup is contained in that of `L`)
  have hfacE : ∀ g h u v : AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k,
      u ∈ (E : IntermediateField k (AlgebraicClosure k)).fixingSubgroup →
      v ∈ (E : IntermediateField k (AlgebraicClosure k)).fixingSubgroup →
      d (g * u) (h * v) = d g h :=
    fun g h u v hu hv => hfac g h u v
      (IntermediateField.fixingSubgroup_antitone hLE hu)
      (IntermediateField.fixingSubgroup_antitone hLE hv)
  -- the restriction map `Gal(E/k) →* Gal(L/k)` of the tower
  let rE : (Lf E ≃ₐ[k] Lf E) →* (Lf L ≃ₐ[k] Lf L) :=
    AlgEquiv.restrictNormalHom (K₁ := Lf E) (E := Lf L)
  have hrEdef : rE = AlgEquiv.restrictNormalHom (K₁ := Lf E) (E := Lf L) := rfl
  have hrE : ∀ σ : AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k,
      levelRes L σ = rE (levelRes E σ) := by
    intro σ
    change AlgEquiv.restrictNormalHom (Lf L) σ
      = rE (AlgEquiv.restrictNormalHom (Lf E) σ)
    rw [IsScalarTower.AlgEquiv.restrictNormalHom_comp_apply (Lf L) (Lf E) σ]
  -- the tower coefficient map is compatible with the coefficient maps `Lˣ → k̄ˣ`, `Eˣ → k̄ˣ`
  have hcompat : ∀ x : Additive (Lf L)ˣ,
      inclUnits E (NK.NUV2.LC.unitsInclTowerCoeff (F := k) (L := Lf L) (M := Lf E) x)
        = inclUnits L x := by
    intro x
    rw [← ofMul_toMul x]
    change inclUnits E (Additive.ofMul (Units.map (algebraMap (Lf L) (Lf E)).toMonoidHom
        (Additive.toMul x))) = inclUnits L (Additive.ofMul (Additive.toMul x))
    rw [inclUnits_ofMul, inclUnits_ofMul]
    congr 1
    apply Units.ext
    show (algebraMap (Lf E) (AlgebraicClosure k))
        ((algebraMap (Lf L) (Lf E)) (((Additive.toMul x : (Lf L)ˣ)) : Lf L))
      = (algebraMap (Lf L) (AlgebraicClosure k)) (((Additive.toMul x : (Lf L)ˣ)) : Lf L)
    exact (IsScalarTower.algebraMap_apply (Lf L) (Lf E) (AlgebraicClosure k)
      (((Additive.toMul x : (Lf L)ˣ)) : Lf L)).symm
  -- the cocycles agree after pushing along the tower coefficient map
  have hcoe : (groupCohomology.mapCocycles₂ rE
        (NK.NUV2.LC.unitsInclTowerCoeff (F := k) (L := Lf L) (M := Lf E))
        (⟨(fun p : (Lf L ≃ₐ[k] Lf L) × (Lf L ≃ₐ[k] Lf L) =>
            levelCocycle L d hvals p.1 p.2), hmem⟩ :
          ↥(groupCohomology.cocycles₂ (NK.HassePrinciple.unitsRep k (Lf L)))) :
        ↥(groupCohomology.cocycles₂ (NK.HassePrinciple.unitsRep k (Lf E))))
      = (⟨(fun p : (Lf E ≃ₐ[k] Lf E) × (Lf E ≃ₐ[k] Lf E) =>
            levelCocycle E d hvalsE p.1 p.2), hmemE⟩ :
          ↥(groupCohomology.cocycles₂ (NK.HassePrinciple.unitsRep k (Lf E)))) := by
    apply Subtype.ext
    funext p
    obtain ⟨g, h⟩ := p
    change (NK.NUV2.LC.unitsInclTowerCoeff (F := k) (L := Lf L) (M := Lf E))
        (levelCocycle L d hvals (rE g) (rE h)) = levelCocycle E d hvalsE g h
    apply inclUnits_injective E
    rw [hcompat (levelCocycle L d hvals (rE g) (rE h)),
      levelCocycle_value E d hvalsE hfacE g h (sec E g) (sec E h) (levelRes_sec E g)
        (levelRes_sec E h)]
    exact levelCocycle_value L d hvals hfac (rE g) (rE h) (sec E g) (sec E h)
      (by rw [hrE, levelRes_sec]) (by rw [hrE, levelRes_sec])
  have h1 : (groupCohomology.map rE
        (NK.NUV2.LC.unitsInclTowerCoeff (F := k) (L := Lf L) (M := Lf E)) 2).hom
      (groupCohomology.H2π (NK.HassePrinciple.unitsRep k (Lf L))
        (⟨(fun p : (Lf L ≃ₐ[k] Lf L) × (Lf L ≃ₐ[k] Lf L) =>
            levelCocycle L d hvals p.1 p.2), hmem⟩ :
          ↥(groupCohomology.cocycles₂ (NK.HassePrinciple.unitsRep k (Lf L)))))
      = groupCohomology.H2π (NK.HassePrinciple.unitsRep k (Lf E))
          (groupCohomology.mapCocycles₂ rE
            (NK.NUV2.LC.unitsInclTowerCoeff (F := k) (L := Lf L) (M := Lf E))
            (⟨(fun p : (Lf L ≃ₐ[k] Lf L) × (Lf L ≃ₐ[k] Lf L) =>
                levelCocycle L d hvals p.1 p.2), hmem⟩ :
              ↥(groupCohomology.cocycles₂ (NK.HassePrinciple.unitsRep k (Lf L))))) := by
    conv_lhs => rw [← ModuleCat.comp_apply (groupCohomology.H2π (NK.HassePrinciple.unitsRep k (Lf L)))
      (groupCohomology.map rE (NK.NUV2.LC.unitsInclTowerCoeff (F := k) (L := Lf L) (M := Lf E)) 2)
      (⟨(fun p : (Lf L ≃ₐ[k] Lf L) × (Lf L ≃ₐ[k] Lf L) =>
          levelCocycle L d hvals p.1 p.2), hmem⟩ :
        ↥(groupCohomology.cocycles₂ (NK.HassePrinciple.unitsRep k (Lf L))))]
    rw [groupCohomology.H2π_comp_map rE
      (NK.NUV2.LC.unitsInclTowerCoeff (F := k) (L := Lf L) (M := Lf E)), ModuleCat.comp_apply]
  change (groupCohomology.map rE
      (NK.NUV2.LC.unitsInclTowerCoeff (F := k) (L := Lf L) (M := Lf E)) 2).hom
      (groupCohomology.H2π (NK.HassePrinciple.unitsRep k (Lf L))
        (⟨(fun p : (Lf L ≃ₐ[k] Lf L) × (Lf L ≃ₐ[k] Lf L) =>
            levelCocycle L d hvals p.1 p.2), hmem⟩ :
          ↥(groupCohomology.cocycles₂ (NK.HassePrinciple.unitsRep k (Lf L)))))
    = groupCohomology.H2π (NK.HassePrinciple.unitsRep k (Lf E))
        (⟨(fun p : (Lf E ≃ₐ[k] Lf E) × (Lf E ≃ₐ[k] Lf E) =>
          levelCocycle E d hvalsE p.1 p.2), hmemE⟩ :
          ↥(groupCohomology.cocycles₂ (NK.HassePrinciple.unitsRep k (Lf E))))
  rw [h1, hcoe]

end Work.SSGRoute.sha2_hasse
