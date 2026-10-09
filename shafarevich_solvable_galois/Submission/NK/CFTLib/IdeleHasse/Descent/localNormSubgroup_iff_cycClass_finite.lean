import Mathlib
import Submission.NK.CFTLib.IdeleHasse.Descent.transferLevels
import Submission.NK.CFTLib.IdeleHasse.Descent.localDictionaryAux
import Submission.NK.CFTLib.IdeleHasse.Crux.zpowersSubgroup
import Submission.NK.HassePrinciple.LocalUnits
import Submission.NK.CFTLib.IdeleHasse.range_localNormFinite_eq_of_liesOver
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The localisation dictionary at a finite place, for the explicit-cocycle cyclic class

For a cyclic Galois extension `F/K` of number fields, a place `q` of `F` over a place `Q` of `K`,
a generator `g` of `Gal(F/K)` and `x ∈ Kˣ`:

  `(locUnits K F q) (cycClassOf g hg x) = 0  ↔  localImageAt Q x ∈ localNormSubgroup K F Q`,

i.e. **the localisation of the class of the cyclic algebra `(F/K, x)` at `q` vanishes exactly when
`x` is a local norm from `F_q` over `K_Q`**.

This is the explicit-cocycle counterpart of the proved
`NK.CFTLib.IdeleHasse.Crux.locUnits_cyclicClass_ofFinite` (which is stated for Mathlib's
periodicity class).  The proof mirrors that of the Crux version; the two periodicity steps
(`resNatTransPiEven` + `periodMap_mapCoeff`) are replaced by the single functoriality theorem
`NK.CFTLib.IdeleHasse.Descent.map_cycClass` for the explicit cocycle, and Mathlib's
`groupCohomologyπEven_eq_zero_iff` is replaced by `Descent.cycClass_eq_zero_iff`.
-/

open scoped NumberField
open NumberField IsDedekindDomain
open NK.GlobalCFT CategoryTheory

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 32000000

namespace NK.CFTLib.IdeleHasse.Descent

open NK.CFTLib.Descent (cycClass cycFun)

/-- **The localisation dictionary, explicit-cocycle form.** -/
theorem localNormSubgroup_iff_cycClass_finite {K F : Type} [Field K] [NumberField K] [Field F]
    [NumberField F] [Algebra K F] [FiniteDimensional K F] [IsGalois K F] [IsCyclic (F ≃ₐ[K] F)]
    (g : F ≃ₐ[K] F) (hg : ∀ x : F ≃ₐ[K] F, x ∈ Subgroup.zpowers g)
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F))
    (hq : q.asIdeal.LiesOver Q.asIdeal) (y : Kˣ) :
    (NK.HassePrinciple.locUnits K F (NK.GlobalCFT.Place.ofFinite q))
        (cycClassOf (K := K) (F := F) g hg y) = 0 ↔
      localImageAt (K := K) (NK.GlobalCFT.Place.ofFinite Q) y ∈
        localNormSubgroup (K := K) (L := F) (NK.GlobalCFT.Place.ofFinite Q) := by
  classical
  -- the decomposition group of `q`, as a power of the generator
  let S : Subgroup (F ≃ₐ[K] F) := MulAction.stabilizer (F ≃ₐ[K] F) (NK.GlobalCFT.Place.ofFinite q)
  obtain ⟨m, hSm, hm⟩ := NK.CFTLib.IdeleHasse.Crux.exists_zpowers_pow_eq_of_isCyclic
    (G := F ≃ₐ[K] F) g hg S
  haveI hSfin : Fintype ↥S := hSm ▸ (inferInstance : Fintype ↥(Subgroup.zpowers (g ^ m)))
  let γ : ↥S := ⟨g ^ m, hSm ▸ Subgroup.mem_zpowers (g ^ m)⟩
  have hγ : (γ : F ≃ₐ[K] F) = g ^ m := rfl
  have hgen : ∀ z : ↥S, z ∈ Subgroup.zpowers γ := by
    intro z
    exact mem_zpowers_of_coe_mem_zpowers (S := S) (γ := γ)
      (a := g ^ m) rfl (by rw [← hSm]; exact z.2)
  -- the arithmetic normalisation
  have hcard : m * Fintype.card ↥S = Fintype.card (F ≃ₐ[K] F) := by
    rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card]
    exact hm
  -- the element of the invariants and its image under the localisation
  have hφa : (NK.HassePrinciple.unitsToLocalUnits K F (NK.GlobalCFT.Place.ofFinite q)).hom
      (unitsImage (K := K) (F := F) y)
      = Additive.ofMul (Units.map (Place.localAlgebraMapFinite q Q hq).toMonoidHom
          (localImageAt (K := K) (NK.GlobalCFT.Place.ofFinite Q) y)) := by
    change Additive.ofMul (NK.HassePrinciple.unitsToLocalUnitsHom
        (NK.GlobalCFT.Place.ofFinite q) (Units.map (algebraMap K F).toMonoidHom y)) = _
    rw [unitsToLocalUnitsHom_algebraMap Q q hq y]
  have hinv : ∀ σ : ↥S,
      (NK.HassePrinciple.localUnitsRep K F (NK.GlobalCFT.Place.ofFinite q)).ρ σ
        (Additive.ofMul (Units.map (Place.localAlgebraMapFinite q Q hq).toMonoidHom
            (localImageAt (K := K) (NK.GlobalCFT.Place.ofFinite Q) y)))
      = Additive.ofMul (Units.map (Place.localAlgebraMapFinite q Q hq).toMonoidHom
          (localImageAt (K := K) (NK.GlobalCFT.Place.ofFinite Q) y)) := by
    intro σ
    have hthis := Rep.hom_comm_apply
      (NK.HassePrinciple.unitsToLocalUnits K F (NK.GlobalCFT.Place.ofFinite q)) σ
      (unitsImage (K := K) (F := F) y)
    have hfix : (Rep.res S.subtype (NK.HassePrinciple.unitsRep K F)).ρ σ
        (unitsImage (K := K) (F := F) y) = unitsImage (K := K) (F := F) y := by
      apply Additive.ofMul.injective
      apply Units.ext
      exact (σ : F ≃ₐ[K] F).commutes (y : K)
    rw [hfix] at hthis
    rw [hφa] at hthis
    exact hthis.symm
  -- the localisation of the cyclic class is the local cyclic class
  have hloc : (NK.HassePrinciple.locUnits K F (NK.GlobalCFT.Place.ofFinite q))
        (cycClassOf (K := K) (F := F) g hg y)
      = cycClass (NK.HassePrinciple.localUnitsRep K F (NK.GlobalCFT.Place.ofFinite q))
          γ hgen (Additive.ofMul (Units.map (Place.localAlgebraMapFinite q Q hq).toMonoidHom
            (localImageAt (K := K) (NK.GlobalCFT.Place.ofFinite Q) y))) hinv := by
    unfold cycClassOf
    rw [show NK.HassePrinciple.locUnits K F (NK.GlobalCFT.Place.ofFinite q)
        = groupCohomology.map S.subtype
            (NK.HassePrinciple.unitsToLocalUnits K F (NK.GlobalCFT.Place.ofFinite q)) 2 from ?_]
    · exact map_cycClass (NK.HassePrinciple.unitsRep K F)
        (NK.HassePrinciple.localUnitsRep K F (NK.GlobalCFT.Place.ofFinite q))
        S.subtype g hg γ hgen m hγ hcard
        (NK.HassePrinciple.unitsToLocalUnits K F (NK.GlobalCFT.Place.ofFinite q))
        (unitsImage (K := K) (F := F) y)
        (fun σ => unitsRep_apply_unitsImage (K := K) (F := F) σ y)
        (Additive.ofMul (Units.map (Place.localAlgebraMapFinite q Q hq).toMonoidHom
          (localImageAt (K := K) (NK.GlobalCFT.Place.ofFinite Q) y))) hφa hinv
    · rw [NK.HassePrinciple.locUnits]
      exact (groupCohomology.map_comp S.subtype (MonoidHom.id ↥S)
        (𝟙 (Rep.res S.subtype (NK.HassePrinciple.unitsRep K F)))
        (NK.HassePrinciple.unitsToLocalUnits K F (NK.GlobalCFT.Place.ofFinite q)) 2).symm
  rw [hloc, cycClass_eq_zero_iff]
  -- the local norm subgroup is the range of the norm map at `q`
  have hsub : localNormSubgroup (K := K) (L := F) (NK.GlobalCFT.Place.ofFinite Q)
      = MonoidHom.range (Place.localNormFinite q Q hq) :=
    localNormSubgroup_ofFinite_eq_range (K := K) (F := F) Q q hq
  rw [hsub]
  show (Additive.ofMul (Units.map (Place.localAlgebraMapFinite q Q hq).toMonoidHom
        (localImageAt (K := K) (NK.GlobalCFT.Place.ofFinite Q) y)) ∈
      LinearMap.range (Rep.Hom.hom (Rep.norm (NK.HassePrinciple.localUnitsRep K F
        (NK.GlobalCFT.Place.ofFinite q)))).toLinearMap)
      ↔ localImageAt (K := K) (NK.GlobalCFT.Place.ofFinite Q) y
        ∈ MonoidHom.range (Place.localNormFinite q Q hq)
  rw [mem_range_norm_localUnitsRep_apply (K := K) (F := F) Q q hq]
  constructor
  · rintro ⟨z, hz⟩
    exact ⟨z, injective_units_map _
      (Commons.NumberTheory.NumberField.Completion.adicCompletionMap_injective Q q hq) hz⟩
  · rintro ⟨z, hz⟩
    exact ⟨z, by rw [hz]⟩

end NK.CFTLib.IdeleHasse.Descent
