import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.NumberTheory.NumberField.Completion.LiesOverInstances
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
import Submission.NK.CFTLib.Existence.isUnramified_of_normClassSubgroup_le_integralIdeles_two
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The localisation dictionary at an infinite place, for the explicit-cocycle cyclic class

This is the archimedean companion of
`NK.CFTLib.IdeleHasse.Descent.localNormSubgroup_iff_cycClass_finite`: for a cyclic Galois
extension `F/K` of number fields, an infinite place `w` of `F` over an infinite place `v` of `K`,
a generator `g` of `Gal(F/K)` and `x ∈ Kˣ`,

  `(locUnits K F (ofInfinite w)) (cycClassOf g hg x) = 0  ↔
     localImageAt (ofInfinite v) x ∈ localNormSubgroup K F (ofInfinite v)`,

i.e. the localisation of the class of the cyclic algebra `(F/K, x)` at `w` vanishes exactly when
`x` is a local norm at `v`.

The proof is the same as in the finite case, with the finite-place norm identification
`NK.CFTLib.IdeleHasse.Descent.mem_range_norm_localUnitsRep_apply` replaced by the archimedean
`NK.CFTLib.Existence.mem_range_norm_localUnitsRep_infinite`, and the injectivity of the local
algebra map by the injectivity of `NumberField.LiesOver.completionMap` (a ring homomorphism out of
the field `v.Completion`).
-/

open scoped NumberField
open scoped NumberField.LiesOver
open NumberField IsDedekindDomain
open NK.GlobalCFT CategoryTheory

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000

namespace NK.CFTLib.IdeleHasse.Descent

open NK.CFTLib.Descent (cycClass cycFun)

variable {K F : Type} [Field K] [NumberField K] [Field F] [NumberField F] [Algebra K F]
  [FiniteDimensional K F] [IsGalois K F]

/-- **The completion map is compatible with the embeddings of the base field** (archimedean
case). -/
lemma completionMap_algebraMap_inf {v : InfinitePlace K} {w : InfinitePlace F}
    [hw : w.LiesOver v] (k : K) :
    NumberField.LiesOver.completionMap (v := v) (w := w) (algebraMap K v.Completion k)
      = algebraMap F w.Completion (algebraMap K F k) := by
  have h1 : NumberField.LiesOver.completionMap (v := v) (w := w) (algebraMap K v.Completion k)
      = algebraMap K w.Completion k := by
    rw [show ⇑(NumberField.LiesOver.completionMap (v := v) (w := w))
        = ⇑(algebraMap (v.Completion) (w.Completion)) from by
      rw [RingHom.algebraMap_toAlgebra]]
    exact (IsScalarTower.algebraMap_apply K (v.Completion) (w.Completion) k).symm
  rw [h1]
  rfl

/-- **The image of a global unit at an infinite place, in the two vocabularies.** -/
lemma unitsToLocalUnitsHom_algebraMap_ofInfinite (v : InfinitePlace K) (w : InfinitePlace F)
    (hw : w.LiesOver v) (y : Kˣ) :
    NK.HassePrinciple.unitsToLocalUnitsHom (Place.ofInfinite w)
        (Units.map (algebraMap K F).toMonoidHom y)
      = Units.map (NumberField.LiesOver.completionMap (v := v) (w := w)).toMonoidHom
          (localImageAt (K := K) (Place.ofInfinite v) y) := by
  haveI := hw
  apply Units.ext
  simp only [NK.HassePrinciple.unitsToLocalUnitsHom, localImageAt, Units.coe_map]
  exact (completionMap_algebraMap_inf (K := K) (F := F) (v := v) (w := w) (y : K)).symm


/-- **The local norm subgroup at an infinite place is the range of the local norm at any place
above it.** -/
lemma localNormSubgroup_ofInfinite_eq_range_inf {K L : Type} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (v : InfinitePlace K) (w₀ : InfinitePlace L) (hw₀ : w₀.LiesOver v) :
    NK.CFTLib.IdeleHasse.localNormSubgroup (K := K) (L := L)
        (NK.GlobalCFT.Place.ofInfinite v) =
      (NK.GlobalCFT.Place.localNormInfinite w₀ v).range := by
  rw [NK.CFTLib.IdeleHasse.localNormSubgroup_ofInfinite]
  refine le_antisymm (iSup_le fun w' => ?_)
    (le_iSup (fun w' : {w' : InfinitePlace L // w'.LiesOver v} =>
      MonoidHom.range (@NK.GlobalCFT.Place.localNormInfinite K _ L _ _ w'.1 v w'.2)) ⟨w₀, hw₀⟩)
  rw [NK.CFTLib.Existence.range_localNormInfinite_eq_of_liesOver w'.2 hw₀]

/-- **The localisation dictionary at an infinite place, explicit-cocycle form.** -/
theorem localNormSubgroup_iff_cycClass_infinite [IsCyclic (F ≃ₐ[K] F)] (g : F ≃ₐ[K] F)
    (hg : ∀ x : F ≃ₐ[K] F, x ∈ Subgroup.zpowers g)
    (v : InfinitePlace K) (w : InfinitePlace F) (hw : w.LiesOver v) (y : Kˣ) :
    (NK.HassePrinciple.locUnits K F (Place.ofInfinite w))
        (cycClassOf (K := K) (F := F) g hg y) = 0 ↔
      localImageAt (K := K) (Place.ofInfinite v) y ∈
        localNormSubgroup (K := K) (L := F) (Place.ofInfinite v) := by
  classical
  haveI hwI : w.LiesOver v := hw
  -- the decomposition group of `w`, as a power of the generator
  let S : Subgroup (F ≃ₐ[K] F) := MulAction.stabilizer (F ≃ₐ[K] F) (Place.ofInfinite w)
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
  have hφa : (NK.HassePrinciple.unitsToLocalUnits K F (Place.ofInfinite w)).hom
      (unitsImage (K := K) (F := F) y)
      = Additive.ofMul (Units.map
          (NumberField.LiesOver.completionMap (v := v) (w := w)).toMonoidHom
          (localImageAt (K := K) (Place.ofInfinite v) y)) := by
    change Additive.ofMul (NK.HassePrinciple.unitsToLocalUnitsHom
        (Place.ofInfinite w) (Units.map (algebraMap K F).toMonoidHom y)) = _
    rw [unitsToLocalUnitsHom_algebraMap_ofInfinite v w hw y]
  have hinv : ∀ σ : ↥S,
      (NK.HassePrinciple.localUnitsRep K F (Place.ofInfinite w)).ρ σ
        (Additive.ofMul (Units.map
            (NumberField.LiesOver.completionMap (v := v) (w := w)).toMonoidHom
            (localImageAt (K := K) (Place.ofInfinite v) y)))
      = Additive.ofMul (Units.map
          (NumberField.LiesOver.completionMap (v := v) (w := w)).toMonoidHom
          (localImageAt (K := K) (Place.ofInfinite v) y)) := by
    intro σ
    have hthis := Rep.hom_comm_apply
      (NK.HassePrinciple.unitsToLocalUnits K F (Place.ofInfinite w)) σ
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
  have hloc : (NK.HassePrinciple.locUnits K F (Place.ofInfinite w))
        (cycClassOf (K := K) (F := F) g hg y)
      = cycClass (NK.HassePrinciple.localUnitsRep K F (Place.ofInfinite w))
          γ hgen (Additive.ofMul (Units.map
            (NumberField.LiesOver.completionMap (v := v) (w := w)).toMonoidHom
            (localImageAt (K := K) (Place.ofInfinite v) y))) hinv := by
    unfold cycClassOf
    rw [show NK.HassePrinciple.locUnits K F (Place.ofInfinite w)
        = groupCohomology.map S.subtype
            (NK.HassePrinciple.unitsToLocalUnits K F (Place.ofInfinite w)) 2 from ?_]
    · exact map_cycClass (NK.HassePrinciple.unitsRep K F)
        (NK.HassePrinciple.localUnitsRep K F (Place.ofInfinite w))
        S.subtype g hg γ hgen m hγ hcard
        (NK.HassePrinciple.unitsToLocalUnits K F (Place.ofInfinite w))
        (unitsImage (K := K) (F := F) y)
        (fun σ => unitsRep_apply_unitsImage (K := K) (F := F) σ y)
        (Additive.ofMul (Units.map
          (NumberField.LiesOver.completionMap (v := v) (w := w)).toMonoidHom
          (localImageAt (K := K) (Place.ofInfinite v) y))) hφa hinv
    · rw [NK.HassePrinciple.locUnits]
      exact (groupCohomology.map_comp S.subtype (MonoidHom.id ↥S)
        (𝟙 (Rep.res S.subtype (NK.HassePrinciple.unitsRep K F)))
        (NK.HassePrinciple.unitsToLocalUnits K F (Place.ofInfinite w)) 2).symm
  rw [hloc, cycClass_eq_zero_iff]
  -- the local norm subgroup is the range of the norm map at `w`
  have hsub : localNormSubgroup (K := K) (L := F) (Place.ofInfinite v)
      = MonoidHom.range (Place.localNormInfinite w v) :=
    localNormSubgroup_ofInfinite_eq_range_inf v w hw
  rw [hsub]
  show (Additive.ofMul (Units.map
        (NumberField.LiesOver.completionMap (v := v) (w := w)).toMonoidHom
        (localImageAt (K := K) (Place.ofInfinite v) y)) ∈
      LinearMap.range (Rep.Hom.hom (Rep.norm (NK.HassePrinciple.localUnitsRep K F
        (Place.ofInfinite w)))).toLinearMap)
      ↔ localImageAt (K := K) (Place.ofInfinite v) y
        ∈ MonoidHom.range (Place.localNormInfinite w v)
  rw [NK.CFTLib.Existence.mem_range_norm_localUnitsRep_infinite (K := K) (N := F) w v]
  constructor
  · rintro ⟨z, hz⟩
    exact ⟨z, injective_units_map _
      (RingHom.injective (NumberField.LiesOver.completionMap (v := v) (w := w))) hz⟩
  · rintro ⟨z, hz⟩
    exact ⟨z, by rw [hz]⟩

end NK.CFTLib.IdeleHasse.Descent
