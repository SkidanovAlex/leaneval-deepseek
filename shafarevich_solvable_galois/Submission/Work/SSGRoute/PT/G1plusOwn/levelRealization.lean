import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Submission.Work.SSGRoute.PT.G1plusOwn.levelFree
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Level realisation

An abstract Galois level `L/k` carrying a place `w'` above the finite place of `K` cut out by a
finite place `A` of `Ω` is isomorphic to a level `L₀ ⊆ Ω` whose *canonical* place (the one below
`A`, `PT.finQW L₀ A hA`) lies over the given place `w'`.

The construction is the standard one: embed `L` into `Ω` over `K` (`ψ`, using
`IsAlgClosed.surjective_domRestrict_of_isAlgebraic`), so that `L₁ := ψ.fieldRange` is a level
of `Ω` over `k` containing `K`; pull the canonical place `Λ = finQW L₁ A hA` of `L₁` back to a
place `vt` of (the abstract) `L` along the induced isomorphism `𝓞 L ≃+* 𝓞 L₁`; the two places
`vt` and `w'` both lie over the place of `K` cut out by `A`, so they are conjugate under
`Gal(L/K)` (`globalCFT_exists_smul_eq_of_liesOver`); twisting `ψ` by this automorphism gives the
required `K`-algebra structure `L → L₁` whose induced place is `w'`.
-/

set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open scoped NumberField

namespace Work.SSGRoute.PT.G1plusOwn

theorem levelRealization
    (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (L : Type) [Field L] [NumberField L] [Algebra k L] [Algebra ↥K L] [IsScalarTower k ↥K L]
      [FiniteDimensional k L] [IsGalois k L]
    (w' : NK.GlobalCFT.Place L)
    (hw' : NK.GlobalCFT.Place.LiesOver w' (NK.GlobalCFT.Place.ofFinite (SSGRoute.PT.finQ K A hA))) :
    ∃ (L₀ : IntermediateField k Ω) (hFD : FiniteDimensional k ↥L₀) (hGal : IsGalois k ↥L₀)
      (hKL₀ : K ≤ L₀) (algL : Algebra L ↥L₀),
      letI : FiniteDimensional k ↥L₀ := hFD
      letI : IsGalois k ↥L₀ := hGal
      letI : Algebra ↥K ↥L₀ := (IntermediateField.inclusion hKL₀).toAlgebra
      letI : Algebra L ↥L₀ := algL
      IsScalarTower k L ↥L₀ ∧ IsScalarTower ↥K L ↥L₀ ∧
        NK.GlobalCFT.Place.LiesOver (NK.GlobalCFT.Place.ofFinite (SSGRoute.PT.finQW L₀ A hA)) w' := by
  classical
  have hAlgCl : IsAlgClosed Ω := IsAlgClosure.isAlgClosed k
  have hAA : Algebra.IsAlgebraic ↥K L := Algebra.IsAlgebraic.of_finite ↥K L
  haveI hfinKL : FiniteDimensional ↥K L := Module.Finite.right k ↥K L
  haveI hgalKL : IsGalois ↥K L := IsGalois.tower_top_of_isGalois k ↥K L
  -- ## Step 1: a `↥K`-linear embedding `ψ : L → Ω` (via the extension lemma for embeddings).
  obtain ⟨ψ, hψ⟩ : ∃ ψ : L →ₐ[k] Ω, ∀ y : ↥K, ψ (algebraMap ↥K L y) = algebraMap ↥K Ω y := by
    have hsurj := IsAlgClosed.surjective_domRestrict_of_isAlgebraic (K := k) (L := ↥K) (M := Ω)
      (E := L)
    obtain ⟨ψ, hψ⟩ := hsurj (IntermediateField.val K)
    refine ⟨ψ, fun y => ?_⟩
    calc ψ (algebraMap ↥K L y) = (AlgHom.domRestrict ↥K ψ) y := rfl
      _ = (IntermediateField.val K) y := congrArg (fun (f : ↥K →ₐ[k] Ω) => f y) hψ
      _ = algebraMap ↥K Ω y := rfl
  -- ## Step 2: the level `L₁ = ψ(L) ⊆ Ω` and the pullback `vt` of its canonical place.
  let L₁ : IntermediateField k Ω := ψ.fieldRange
  have hKL₁ : K ≤ L₁ := by
    intro x hx
    rw [AlgHom.mem_fieldRange]
    exact ⟨algebraMap ↥K L ⟨x, hx⟩, by rw [hψ]; rfl⟩
  have hFD₁ : FiniteDimensional k ↥L₁ :=
    LinearEquiv.finiteDimensional (ψ.equivFieldRange).toLinearEquiv
  have hGal₁ : IsGalois k ↥L₁ := IsGalois.of_algEquiv ψ.equivFieldRange
  haveI hFD₁' : FiniteDimensional k ↥L₁ := hFD₁
  haveI hGal₁' : IsGalois k ↥L₁ := hGal₁
  let Λ : IsDedekindDomain.HeightOneSpectrum (𝓞 ↥L₁) := SSGRoute.PT.finQW L₁ A hA
  let e : 𝓞 L ≃+* 𝓞 ↥L₁ :=
    NumberField.RingOfIntegers.mapRingEquiv ψ.equivFieldRange.toRingEquiv
  have he_apply : ∀ x : 𝓞 L,
      (((e : 𝓞 L →+* 𝓞 ↥L₁) x : 𝓞 ↥L₁) : ↥L₁) = ψ.equivFieldRange (x : L) := by
    intro x
    show ((e x : 𝓞 ↥L₁) : ↥L₁) = ψ.equivFieldRange (x : L)
    rw [NumberField.RingOfIntegers.mapRingEquiv_apply]
    rfl
  have he_applyΩ : ∀ x : 𝓞 L, ((((e : 𝓞 L →+* 𝓞 ↥L₁) x : 𝓞 ↥L₁) : ↥L₁) : Ω) = ψ (x : L) := by
    intro x
    rw [he_apply x, AlgHom.equivFieldRange_apply_coe]
  have hne : Ideal.comap (e : 𝓞 L →+* 𝓞 ↥L₁) Λ.asIdeal ≠ ⊥ := by
    intro h
    refine Λ.ne_bot ?_
    rw [← Ideal.map_comap_of_surjective (e : 𝓞 L →+* 𝓞 ↥L₁) e.surjective Λ.asIdeal, h,
      Ideal.map_bot]
  let vt : IsDedekindDomain.HeightOneSpectrum (𝓞 L) :=
    ⟨Ideal.comap (e : 𝓞 L →+* 𝓞 ↥L₁) Λ.asIdeal, Ideal.IsPrime.comap _, hne⟩
  -- `vt` is cut out by `A` along `ψ`
  have hmem : ∀ x : 𝓞 L, x ∈ vt.asIdeal ↔ A.valuation (ψ (x : L)) < 1 := by
    intro x
    change x ∈ Ideal.comap (e : 𝓞 L →+* 𝓞 ↥L₁) Λ.asIdeal ↔ _
    rw [Ideal.mem_comap, SSGRoute.PT.finQW_spec]
    rw [he_applyΩ x]
  -- hence `vt` lies over the place of `K` cut out by `A`
  have hlies : vt.asIdeal.LiesOver (SSGRoute.PT.finQ K A hA).asIdeal := by
    refine Ideal.LiesOver.mk (Ideal.ext fun x => ?_)
    rw [Ideal.mem_under, hmem, SSGRoute.PT.finQ_spec]
    have h : ((algebraMap (𝓞 ↥K) (𝓞 L) x : 𝓞 L) : L) = algebraMap ↥K L (x : ↥K) := by
      rw [NumberField.RingOfIntegers.coe_eq_algebraMap,
        ← IsScalarTower.algebraMap_apply (𝓞 ↥K) (𝓞 L) L,
        ← IsScalarTower.algebraMap_apply (𝓞 ↥K) ↥K L]
    rw [h, hψ]
    rfl
  -- ## Step 3: `w'` is a finite place.
  obtain ⟨q₀, rfl⟩ : ∃ q₀ : IsDedekindDomain.HeightOneSpectrum (𝓞 L),
      w' = NK.GlobalCFT.Place.ofFinite q₀ :=
    NK.GlobalCFT.Place.isFinite_iff.mp
      ((NK.GlobalCFT.Place.isFinite_of_liesOver hw').mpr
        (NK.GlobalCFT.Place.isFinite_ofFinite _))
  have hq₀lies : q₀.asIdeal.LiesOver (SSGRoute.PT.finQ K A hA).asIdeal :=
    (NK.GlobalCFT.Galois.globalCFT_liesOver_ofFinite_iff q₀ _).mp hw'
  -- ## Step 4: transitivity of the Galois action over the place of `K` cut out by `A`.
  obtain ⟨σ, hσ⟩ := NK.GlobalCFT.Inclusion.globalCFT_exists_smul_eq_of_liesOver
    (K := ↥K) (L := L) (NK.GlobalCFT.Place.liesOver_ofFinite hlies)
    (NK.GlobalCFT.Place.liesOver_ofFinite hq₀lies)
  have hσ' : Ideal.map (NK.GlobalCFT.Place.ringOfIntegersEquiv σ) vt.asIdeal = q₀.asIdeal := by
    rw [NK.GlobalCFT.Place.smul_ofFinite, NK.GlobalCFT.Place.ofFinite_inj] at hσ
    have h1 : (NK.GlobalCFT.Place.smulHeightOneSpectrum σ vt).asIdeal = q₀.asIdeal :=
      congrArg IsDedekindDomain.HeightOneSpectrum.asIdeal hσ
    rwa [NK.GlobalCFT.Place.smulHeightOneSpectrum_asIdeal] at h1
  -- ## Step 5: the twisted embedding and the algebra structure on `L₁`.
  let eφ : L ≃ₐ[k] ↥L₁ := (AlgEquiv.restrictScalars k σ.symm).trans ψ.equivFieldRange
  have hφcoe : ∀ y : L, ((eφ y : ↥L₁) : Ω) = ψ (σ.symm y) := by
    intro y
    rw [show eφ y = ψ.equivFieldRange (σ.symm y) from rfl, AlgHom.equivFieldRange_apply_coe]
  letI algL : Algebra L ↥L₁ := eφ.toRingEquiv.toRingHom.toAlgebra
  letI algK : Algebra ↥K ↥L₁ := (IntermediateField.inclusion hKL₁).toAlgebra
  have hST1 : IsScalarTower k L ↥L₁ := by
    refine IsScalarTower.of_algebraMap_eq fun a => ?_
    rw [RingHom.algebraMap_toAlgebra]
    exact (eφ.commutes a).symm
  have hST2 : IsScalarTower ↥K L ↥L₁ := by
    refine IsScalarTower.of_algebraMap_eq fun y => ?_
    rw [RingHom.algebraMap_toAlgebra, RingHom.algebraMap_toAlgebra]
    apply Subtype.ext
    show (((IntermediateField.inclusion hKL₁) y : ↥L₁) : Ω) =
      ((eφ (algebraMap ↥K L y) : ↥L₁) : Ω)
    rw [IntermediateField.coe_inclusion, hφcoe, (σ.symm).commutes y, hψ]
    rfl
  -- ## Step 6: the canonical place of `L₁` lies over `w'`.
  have hLies : NK.GlobalCFT.Place.LiesOver
      (NK.GlobalCFT.Place.ofFinite (SSGRoute.PT.finQW L₁ A hA))
      (NK.GlobalCFT.Place.ofFinite q₀) := by
    rw [NK.GlobalCFT.Galois.globalCFT_liesOver_ofFinite_iff]
    refine Ideal.LiesOver.mk (Ideal.ext fun x => ?_)
    rw [Ideal.mem_under, SSGRoute.PT.finQW_spec]
    have hcompat : (((algebraMap (𝓞 L) (𝓞 ↥L₁) x : 𝓞 ↥L₁) : ↥L₁) : Ω) =
        ψ (σ.symm (x : L)) := by
      have h1 : (((algebraMap (𝓞 L) (𝓞 ↥L₁) x : 𝓞 ↥L₁)) : ↥L₁) = algebraMap L ↥L₁ (x : L) := by
        rw [NumberField.RingOfIntegers.coe_eq_algebraMap,
          ← IsScalarTower.algebraMap_apply (𝓞 L) (𝓞 ↥L₁) ↥L₁,
          ← IsScalarTower.algebraMap_apply (𝓞 L) L ↥L₁]
      rw [h1, RingHom.algebraMap_toAlgebra]
      exact hφcoe (x : L)
    rw [hcompat]
    have hA' : (A.valuation (ψ (σ.symm (x : L))) < 1) ↔
        (NK.GlobalCFT.Place.ringOfIntegersEquiv σ.symm x ∈ vt.asIdeal) :=
      (hmem (NK.GlobalCFT.Place.ringOfIntegersEquiv σ.symm x)).symm
    have hB : (NK.GlobalCFT.Place.ringOfIntegersEquiv σ.symm x ∈ vt.asIdeal) ↔
        x ∈ q₀.asIdeal := by
      rw [← hσ']
      show (NK.GlobalCFT.Place.ringOfIntegersEquiv σ).symm x ∈ vt.asIdeal ↔ x ∈ _
      exact Ideal.symm_apply_mem_of_equiv_iff
    exact (hA'.trans hB).symm
  exact ⟨L₁, hFD₁, hGal₁, hKL₁, algL, hST1, hST2, hLies⟩

end Work.SSGRoute.PT.G1plusOwn
