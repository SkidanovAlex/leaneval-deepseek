import Mathlib
import Submission.Work.SSGRoute.PT.g1plus_levelTransport
import Submission.Work.SSGRoute.PT.g1plus_iota
import Submission.Work.SSGRoute.localUnitsMap_exists
import Submission.Work.SSGRoute.decompK_restrict_exists

/-!
# Level transport of the orbit-placement lift `iotaLift`

The second half of the level change of `PT.finAtLevel`: the class `[b]_L` is transported to the
upper level by inflation (`extHMap ρ 𝟙`), the resulting local class `z'` is the local inflation of
the level-`L` class `z`, and the orbit placement `iotaLift w' z'` is the *inflation* of the
orbit placement `iotaLift w z` along the idèle level map (`E9c.idleRepMap`):

`iotaLift w' (localInfl z) = extHMap (galRes) (idleRepMap) (iotaLift w z)`.

The proof is the *uniqueness* of the orbit-supported lift (`PT.eq_iotaLift_of_spec`): the
candidate has `extLoc w' = localInfl z` by `E7cOmega.extLoc_push_ideleMap` and vanishes off the
orbit of `w'`, because the place-below map `u : Place L → Place K` of `E9c.canonicalIdleData` is
equivariant and `u v ∈ orbit(w)` would force `v ∈ orbit(w')`
(`NK.GlobalCFT.Inclusion.globalCFT_exists_smul_eq_of_liesOver`).

This file also records the removal of the `mk₀ (unitRes f)` prefix of `extHMap`
(`extHMap_eq_extRes_comp`), which the orbit argument needs.
-/

set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option autoImplicit false

open CategoryTheory SSGRoute.PTExt

namespace Work.SSGRoute.PT

/-- **`extHMap` is `extRes` followed by post-composition with the coefficient map**: the
`mk₀ (unitRes f)` prefix of the definition is the canonical identification
`unitRep H ≅ Rep.res f (unitRep G)` (`Work.SSGRoute.unitRes_eq_id`). -/
theorem extHMap_eq_extRes_comp {G H : Type} [Group G] [Group H] (f : H →* G)
    {A : Rep Coeff G} {B : Rep Coeff H} (ι : Rep.res f A ⟶ B) {n : ℕ} (y : extH A n) :
    extHMap f ι y = (extRes f y).comp (Abelian.Ext.mk₀ ι) (add_zero n) := by
  have hunit : unitRes f = 𝟙 (unitRep H) := rfl
  rw [extHMap, hunit]
  exact Abelian.Ext.mk₀_id_comp _

/-- The place-below map of `E9c.canonicalIdleData` is equivariant for the restriction
`Gal(L/k) →* Gal(K/k)`. -/
theorem canonicalIdleData_u_smul {k K L : Type} [Field k] [NumberField k] [Field K]
    [NumberField K] [Field L] [NumberField L] [Algebra k K] [Algebra K L] [Algebra k L]
    [IsScalarTower k K L] [FiniteDimensional k K] [IsGalois k K] [FiniteDimensional k L]
    [IsGalois k L] (σ : L ≃ₐ[k] L) (v : NK.GlobalCFT.Place L) :
    (Work.SSGRoute.canonicalIdleData k K L).u (σ • v)
      = galRes k K L σ • (Work.SSGRoute.canonicalIdleData k K L).u v :=
  NK.GlobalCFT.Inclusion.globalCFT_liesOver_unique
    ((Work.SSGRoute.canonicalIdleData k K L).hu (σ • v))
    (NK.HassePrinciple.liesOver_smul_of_restrict (K := k) (F := K) (L := L) σ
      (galRes k K L σ) (fun y => AlgEquiv.restrictNormal_commutes σ K y)
      ((Work.SSGRoute.canonicalIdleData k K L).hu v))

/-- **Level transport of the orbit-supported lift.** -/
theorem iotaLift_idleRepMap (k K L : Type) [Field k] [NumberField k] [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [FiniteDimensional k K] [IsGalois k K] [FiniteDimensional k L] [IsGalois k L]
    (w : NK.GlobalCFT.Place K) (w' : NK.GlobalCFT.Place L)
    (hw' : NK.GlobalCFT.Place.LiesOver w' w)
    (μ : Rep.res (decompKRestrict k K L w w' hw') (localUnitsK (k := k) (K := K) w) ⟶
      localUnitsK (k := k) (K := L) w')
    (hμ : ∀ y : (NK.GlobalCFT.Place.localField K w)ˣ,
      μ.hom (Additive.ofMul y)
        = Additive.ofMul (NK.GlobalCFT.Place.localAlgebraMapUnits w' w hw' y))
    (z : extH (localUnitsK (k := k) (K := K) w) 2) :
    iotaLift (k := k) (L := L) w' (extHMap (decompKRestrict k K L w w' hw') μ z)
      = extHMap (galRes k K L) (Work.SSGRoute.idleRepMap k K L)
          (iotaLift (k := k) (L := K) w z) := by
  classical
  obtain ⟨hspec, hvan⟩ := iotaLift_spec (k := k) (L := K) w z
  -- the place of `K` below `w'` is `w`
  have huw' : (Work.SSGRoute.canonicalIdleData k K L).u w' = w :=
    NK.GlobalCFT.Inclusion.globalCFT_liesOver_unique
      ((Work.SSGRoute.canonicalIdleData k K L).hu w') hw'
  symm
  refine eq_iotaLift_of_spec (k := k) (L := L) w'
    (extHMap (decompKRestrict k K L w w' hw') μ z)
    (extHMap (galRes k K L) (Work.SSGRoute.idleRepMap k K L)
      (iotaLift (k := k) (L := K) w z)) ?_ ?_
  · -- the localisation at `w'` is the local inflation of `z`
    rw [extHMap_eq_extRes_comp (galRes k K L) (Work.SSGRoute.idleRepMap k K L)
        (iotaLift (k := k) (L := K) w z)]
    refine (Work.SSGRoute.E7cOmega.extLoc_push_ideleMap k K L
      (iotaLift (k := k) (L := K) w z) w w' hw' μ hμ).trans ?_
    rw [hspec]
    exact (extHMap_eq_extRes_comp (decompKRestrict k K L w w' hw') μ z).symm
  · -- vanishing off the orbit of `w'`
    intro v hv
    -- the local units map at the pair `(u v, v)`
    have hvu : NK.GlobalCFT.Place.LiesOver v ((Work.SSGRoute.canonicalIdleData k K L).u v) :=
      (Work.SSGRoute.canonicalIdleData k K L).hu v
    obtain ⟨μv, hμv⟩ := localUnitsMap_exists k K L ((Work.SSGRoute.canonicalIdleData k K L).u v)
      v hvu (decompKRestrict k K L ((Work.SSGRoute.canonicalIdleData k K L).u v) v hvu)
      (decompKRestrict_coe k K L ((Work.SSGRoute.canonicalIdleData k K L).u v) v hvu)
    rw [extHMap_eq_extRes_comp (galRes k K L) (Work.SSGRoute.idleRepMap k K L)
        (iotaLift (k := k) (L := K) w z)]
    refine (Work.SSGRoute.E7cOmega.extLoc_push_ideleMap k K L (iotaLift (k := k) (L := K) w z)
      ((Work.SSGRoute.canonicalIdleData k K L).u v) v hvu μv hμv).trans ?_
    -- `u v` is outside the orbit of `w`, so the level-`K` localisation vanishes
    have hoff : ∀ σ : K ≃ₐ[k] K, σ • w ≠ (Work.SSGRoute.canonicalIdleData k K L).u v := by
      intro σ hσ
      -- lift `σ` to `Gal(L/k)` and conjugate `w'` to `v`
      obtain ⟨σt, hσt⟩ := AlgEquiv.restrictNormalHom_surjective (F := k) (K₁ := K) L σ
      have hσt' : galRes k K L σt = σ := hσt
      have hσtinv : galRes k K L σt⁻¹ = σ⁻¹ := by rw [map_inv, hσt']
      have h1 : (Work.SSGRoute.canonicalIdleData k K L).u (σt⁻¹ • v)
          = (Work.SSGRoute.canonicalIdleData k K L).u w' := by
        rw [canonicalIdleData_u_smul, hσtinv, ← hσ, inv_smul_smul, ← huw']
      have h2 : NK.GlobalCFT.Place.LiesOver (σt⁻¹ • v) w := by
        rw [← huw']
        exact h1 ▸ (Work.SSGRoute.canonicalIdleData k K L).hu (σt⁻¹ • v)
      haveI : IsGalois K L := IsGalois.tower_top_of_isGalois k K L
      haveI : FiniteDimensional K L := FiniteDimensional.right k K L
      obtain ⟨ρ, hρ⟩ :=
        NK.GlobalCFT.Inclusion.globalCFT_exists_smul_eq_of_liesOver (K := K) (L := L) h2 hw'
      have hsmul : ∀ x : NK.GlobalCFT.Place L, (AlgEquiv.restrictScalars k ρ) • x = ρ • x :=
        fun x => rfl
      have hsmulinv : ∀ x : NK.GlobalCFT.Place L,
          (AlgEquiv.restrictScalars k ρ)⁻¹ • x = ρ⁻¹ • x := fun x => rfl
      have h3 : (AlgEquiv.restrictScalars k ρ)⁻¹ • w' = σt⁻¹ • v := by
        rw [hsmulinv, ← hρ, inv_smul_smul]
      refine hv (σt * (AlgEquiv.restrictScalars k ρ)⁻¹) ?_
      rw [mul_smul, h3]
      simp
    rw [hvan ((Work.SSGRoute.canonicalIdleData k K L).u v) hoff, extRes,
      Abelian.Ext.mapExactFunctor_zero, Abelian.Ext.zero_comp]
    rfl

end Work.SSGRoute.PT
