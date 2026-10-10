import Mathlib.RingTheory.Henselian
import Mathlib.FieldTheory.Galois.GaloisClosure
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Submission.Work.SSGRoute.sha2_hasse.locUnits_mkClass_apply
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

/-- The equivariance of the coefficient map `Eˣ → E_wˣ` of the localisation. -/
theorem unitsToLocalUnits_smul_apply
    (E : FiniteGaloisIntermediateField k (AlgebraicClosure k))
    (w : NK.GlobalCFT.Place (Lf E))
    (γ : ↥(MulAction.stabilizer (Lf E ≃ₐ[k] Lf E) w)) (x : Additive (Lf E)ˣ) :
    (NK.HassePrinciple.unitsToLocalUnits k (Lf E) w).hom
        (((γ : Lf E ≃ₐ[k] Lf E)) • x) =
      (NK.HassePrinciple.localUnitsRep k (Lf E) w).ρ γ
        ((NK.HassePrinciple.unitsToLocalUnits k (Lf E) w).hom x) :=
  LinearMap.congr_fun
    ((Rep.Hom.hom (NK.HassePrinciple.unitsToLocalUnits k (Lf E) w)).isIntertwining' γ) x

/-- **Local triviality of the level class at `E` from a coboundary on the decomposition group of
a place of `k̄`**: if the cocycle `d` is the coboundary of `b` on the decomposition group
`D_A` of a place `A` of `k̄`, and the restriction of `D_A` to `Gal(E/k)` covers the stabiliser of
`qE` (a section `σ`), then the level class of `d` at `E` localised at `qE` vanishes. -/
theorem locUnits_levelClass_eq_zero_of_section
    (E : FiniteGaloisIntermediateField k (AlgebraicClosure k))
    (d : (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) →
      (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) → Additive (AlgebraicClosure k)ˣ)
    (hfacE : ∀ g h u v : AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k,
      u ∈ (E : IntermediateField k (AlgebraicClosure k)).fixingSubgroup →
      v ∈ (E : IntermediateField k (AlgebraicClosure k)).fixingSubgroup →
      d (g * u) (h * v) = d g h)
    (hvalsE : ∀ g h : AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k,
      ∃ x : (Lf E)ˣ, inclUnits E (Additive.ofMul x) = d g h)
    (hmemE : (fun p : (Lf E ≃ₐ[k] Lf E) × (Lf E ≃ₐ[k] Lf E) =>
        levelCocycle E d hvalsE p.1 p.2) ∈
      groupCohomology.cocycles₂ (NK.HassePrinciple.unitsRep k (Lf E)))
    (A : ValuationSubring (AlgebraicClosure k))
    (qE : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers (Lf E)))
    (b : (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) → Additive (AlgebraicClosure k)ˣ)
    (hcob : ∀ g ∈ SSGRoute.decomp k A, ∀ h ∈ SSGRoute.decomp k A,
      d g h = g • b h - b (g * h) + b g)
    (σ : ↥(MulAction.stabilizer (Lf E ≃ₐ[k] Lf E)
        (NK.GlobalCFT.Place.ofFinite qE)) →
        (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k))
    (hσmem : ∀ γ, σ γ ∈ SSGRoute.decomp k A)
    (hσres : ∀ γ, levelRes E (σ γ) = (γ : Lf E ≃ₐ[k] Lf E))
    (hval : ∀ γ, ((Additive.toMul (b (σ γ)) : (AlgebraicClosure k)ˣ) : AlgebraicClosure k) ∈
      (E : IntermediateField k (AlgebraicClosure k)))
    (hinv : ∀ γ δ, b (σ γ * σ δ) = b (σ (γ * δ))) :
    (NK.HassePrinciple.locUnits k (Lf E) (NK.GlobalCFT.Place.ofFinite qE)).hom
      (levelClass E d hvalsE hmemE) = 0 := by
  classical
  let Γ := ↥(MulAction.stabilizer (Lf E ≃ₐ[k] Lf E) (NK.GlobalCFT.Place.ofFinite qE))
  let f : Γ → (Lf E)ˣ :=
    fun γ => Units.mk0 (⟨((Additive.toMul (b (σ γ)) : (AlgebraicClosure k)ˣ) :
        AlgebraicClosure k), hval γ⟩ : (E : IntermediateField k (AlgebraicClosure k))) (by
      intro h
      have h2 : ((Additive.toMul (b (σ γ)) : (AlgebraicClosure k)ˣ) : AlgebraicClosure k) = 0 := by
        simpa using congrArg Subtype.val h
      exact (Additive.toMul (b (σ γ))).ne_zero h2)
  have hf_val : ∀ γ : Γ, ((f γ : Lf E) : AlgebraicClosure k) =
      ((Additive.toMul (b (σ γ)) : (AlgebraicClosure k)ˣ) : AlgebraicClosure k) := fun γ => rfl
  have hf_units : ∀ γ : Γ, Units.map (algebraMap (Lf E) (AlgebraicClosure k)).toMonoidHom (f γ)
      = Additive.toMul (b (σ γ)) := by
    intro γ
    apply Units.ext
    simpa [Units.coe_map] using hf_val γ
  have hcobE : ∀ γ δ : Γ,
      levelCocycle E d hvalsE (γ : Lf E ≃ₐ[k] Lf E) (δ : Lf E ≃ₐ[k] Lf E) =
        (γ : Lf E ≃ₐ[k] Lf E) • (Additive.ofMul (f δ))
        - Additive.ofMul (f (γ * δ)) + Additive.ofMul (f γ) := by
    intro γ δ
    apply inclUnits_injective E
    have hsmul : inclUnits E ((γ : Lf E ≃ₐ[k] Lf E) • Additive.ofMul (f δ))
        = (σ γ) • inclUnits E (Additive.ofMul (f δ)) := by
      rw [show (γ : Lf E ≃ₐ[k] Lf E) • Additive.ofMul (f δ)
          = (levelRes E (σ γ)) • Additive.ofMul (f δ) from by rw [hσres]]
      exact inclUnits_smul E (σ γ) (Additive.ofMul (f δ))
    have hfδ : inclUnits E (Additive.ofMul (f δ)) = b (σ δ) :=
      (inclUnits_ofMul E (f δ)).trans (congrArg Additive.ofMul (hf_units δ))
    have hfγδ : inclUnits E (Additive.ofMul (f (γ * δ))) = b (σ (γ * δ)) :=
      (inclUnits_ofMul E (f (γ * δ))).trans (congrArg Additive.ofMul (hf_units (γ * δ)))
    have hfγ : inclUnits E (Additive.ofMul (f γ)) = b (σ γ) :=
      (inclUnits_ofMul E (f γ)).trans (congrArg Additive.ofMul (hf_units γ))
    rw [map_add, map_sub]
    rw [levelCocycle_value E d hvalsE hfacE (γ : Lf E ≃ₐ[k] Lf E) (δ : Lf E ≃ₐ[k] Lf E)
        (σ γ) (σ δ) (hσres γ) (hσres δ), hsmul, hfδ, hfγδ, hfγ, ← hinv γ δ]
    exact hcob (σ γ) (hσmem γ) (σ δ) (hσmem δ)
  have hmemB : groupCohomology.H2π (NK.HassePrinciple.localUnitsRep k (Lf E)
        (NK.GlobalCFT.Place.ofFinite qE))
      (groupCohomology.mapCocycles₂ (MulAction.stabilizer (Lf E ≃ₐ[k] Lf E)
          (NK.GlobalCFT.Place.ofFinite qE)).subtype
        (NK.HassePrinciple.unitsToLocalUnits k (Lf E) (NK.GlobalCFT.Place.ofFinite qE))
        (⟨(fun p : (Lf E ≃ₐ[k] Lf E) × (Lf E ≃ₐ[k] Lf E) =>
            levelCocycle E d hvalsE p.1 p.2), hmemE⟩ :
          ↥(groupCohomology.cocycles₂ (NK.HassePrinciple.unitsRep k (Lf E))))) = 0 := by
    rw [groupCohomology.H2π_eq_zero_iff]
    refine ⟨fun γ => (NK.HassePrinciple.unitsToLocalUnits k (Lf E)
      (NK.GlobalCFT.Place.ofFinite qE)).hom (Additive.ofMul (f γ)), funext ?_⟩
    rintro ⟨γ, δ⟩
    rw [groupCohomology.d₁₂_hom_apply, groupCohomology.coe_mapCocycles₂,
      cochainsMap₂_apply]
    change (NK.HassePrinciple.localUnitsRep k (Lf E) (NK.GlobalCFT.Place.ofFinite qE)).ρ γ
        ((NK.HassePrinciple.unitsToLocalUnits k (Lf E)
          (NK.GlobalCFT.Place.ofFinite qE)).hom (Additive.ofMul (f δ)))
        - (NK.HassePrinciple.unitsToLocalUnits k (Lf E)
          (NK.GlobalCFT.Place.ofFinite qE)).hom (Additive.ofMul (f (γ * δ)))
        + (NK.HassePrinciple.unitsToLocalUnits k (Lf E)
          (NK.GlobalCFT.Place.ofFinite qE)).hom (Additive.ofMul (f γ))
      = (NK.HassePrinciple.unitsToLocalUnits k (Lf E)
          (NK.GlobalCFT.Place.ofFinite qE)).hom
          (levelCocycle E d hvalsE (γ : Lf E ≃ₐ[k] Lf E) (δ : Lf E ≃ₐ[k] Lf E))
    rw [hcobE γ δ, map_add, map_sub, unitsToLocalUnits_smul_apply]
    rfl
  have hstep := locUnits_mkClass_apply (k := k) E (NK.GlobalCFT.Place.ofFinite qE)
    (fun p : (Lf E ≃ₐ[k] Lf E) × (Lf E ≃ₐ[k] Lf E) => levelCocycle E d hvalsE p.1 p.2) hmemE
  show (NK.HassePrinciple.locUnits k (Lf E) (NK.GlobalCFT.Place.ofFinite qE)).hom
      (mkClass (NK.HassePrinciple.unitsRep k (Lf E))
        (fun p : (Lf E ≃ₐ[k] Lf E) × (Lf E ≃ₐ[k] Lf E) => levelCocycle E d hvalsE p.1 p.2)
        hmemE) = 0
  rw [hstep]
  exact hmemB

end Work.SSGRoute.sha2_hasse
