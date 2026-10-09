import Mathlib
import Submission.Work.SSGRoute.PT.finHalfData
import Submission.Work.SSGRoute.glue_fin_decomp_ex
import Submission.NK.Reconstruct.restrictNormalHom_smul_valuationSubringAtPrime
import Submission.Work.SSGRoute.E7cOmega.freeOrbitAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Auxiliary lemmas for the transversal of the places of a level

These are the shared, level-local ingredients used by `Work.SSGRoute.PT.vf_transverse` and by the
two pieces it is assembled from (`vf_coverage`, `vf_injective`):

* `finQW_comap` — the trace on `L` of a finite place of `Ω` is the valuation ring of `finQW L A`;
* `smul_valuationSubringAtPrime` — the Galois action on the valuation rings of the primes of `𝓞 L`;
* `comap_smul_eq_restrictNormal_smul` — the trace on `L` of a translated place;
* `finQW_smulHeightOneSpectrum`, `ofFinite_finQW_smul` — compatibility of `finQW` with the Galois
  action on the places of `Ω`;
* `isFinite_smul_iff` — nonarchimedeanness is `Gal(L/k)`-invariant.
-/

set_option maxHeartbeats 1000000

open scoped Pointwise
open NumberField IsDedekindDomain

namespace Work.SSGRoute.PT

variable {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]

/-- **The trace of a finite place of `Ω` on the level `L`.**  The restriction to `L` of the
valuation ring of a finite place `A` of `Ω` over `k` is the valuation ring of the prime
`finQW L A` of `𝓞 L` cut out by `A`. -/
theorem finQW_comap (L : IntermediateField k Ω) [FiniteDimensional k L] [IsGalois k L]
    [NumberField L] (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A) :
    A.comap (algebraMap ↥L Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥L (finQW L A hA) :=
  Work.SSGRoute.place_comap_valuationSubringAtPrime k Ω L A hA (finQW L A hA)
    (fun x => finQW_spec L A hA x)

/-- **`Place.ringOfIntegersEquiv` is `galRestrict`**, as ring homomorphisms. -/
theorem ringOfIntegersEquiv_eq_galRestrictHom (L : IntermediateField k Ω) [FiniteDimensional k L]
    [IsGalois k L] [NumberField L] (σ : ↥L ≃ₐ[k] ↥L) :
    (NK.GlobalCFT.Place.ringOfIntegersEquiv σ : 𝓞 ↥L →+* 𝓞 ↥L) =
      (galRestrict (𝓞 k) k ↥L (𝓞 ↥L) σ : 𝓞 ↥L →+* 𝓞 ↥L) :=
  Work.SSGRoute.E7cOmega.ringOfIntegersEquiv_eq_galRestrict' (k := k) (L := ↥L) σ

/-- **The Galois action on the valuation rings of the primes of `𝓞 L`.**  Translating the prime
`q` translates its valuation ring. -/
theorem smul_valuationSubringAtPrime (L : IntermediateField k Ω) [FiniteDimensional k L]
    [IsGalois k L] [NumberField L] (σ : ↥L ≃ₐ[k] ↥L)
    (q : IsDedekindDomain.HeightOneSpectrum (𝓞 ↥L)) :
    σ • IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥L q =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥L
        (NK.GlobalCFT.Place.smulHeightOneSpectrum σ q) :=
  Commons.NumberTheory.RamificationInertia.smul_valuationSubringAtPrime_eq_map_galRestrict
    (K := k) (L := ↥L) q (NK.GlobalCFT.Place.smulHeightOneSpectrum σ q) σ
    (by
      rw [NK.GlobalCFT.Place.smulHeightOneSpectrum_asIdeal]
      exact congrArg (fun f : 𝓞 ↥L →+* 𝓞 ↥L => Ideal.map f q.asIdeal)
        (ringOfIntegersEquiv_eq_galRestrictHom L σ))

/-- **The trace on `L` of a translated place of `Ω`.** -/
theorem comap_smul_eq_restrictNormal_smul (L : IntermediateField k Ω) [FiniteDimensional k L]
    [IsGalois k L] [NumberField L] (A : ValuationSubring Ω) (τ : Ω ≃ₐ[k] Ω) :
    (τ • A).comap (algebraMap ↥L Ω) = (τ.restrictNormal ↥L) • (A.comap (algebraMap ↥L Ω)) := by
  rw [NK.Reconstruct.comap_smul_eq_restrictNormalHom_smul' (F := k) (E := ↥L) (K := Ω) A τ]
  rfl

/-- **`finQW` is compatible with the Galois action.**  The prime of `𝓞 L` cut out by a translated
place of `Ω` is the translation of the prime cut out by the original place. -/
theorem finQW_smulHeightOneSpectrum (L : IntermediateField k Ω) [FiniteDimensional k L]
    [IsGalois k L] [NumberField L] (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (τ : Ω ≃ₐ[k] Ω) (hA' : SSGRoute.IsFinPlace k (τ • A)) :
    finQW L (τ • A) hA' =
      NK.GlobalCFT.Place.smulHeightOneSpectrum (τ.restrictNormal ↥L) (finQW L A hA) := by
  refine Commons.RingTheory.Valuation.valuationSubringAtPrime_injective
    (R := 𝓞 ↥L) (K := ↥L) ?_
  calc IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥L (finQW L (τ • A) hA')
      = (τ • A).comap (algebraMap ↥L Ω) := (finQW_comap L (τ • A) hA').symm
    _ = (τ.restrictNormal ↥L) • (A.comap (algebraMap ↥L Ω)) :=
        comap_smul_eq_restrictNormal_smul L A τ
    _ = (τ.restrictNormal ↥L) •
          IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥L (finQW L A hA) := by
        rw [finQW_comap L A hA]
    _ = IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥L
          (NK.GlobalCFT.Place.smulHeightOneSpectrum (τ.restrictNormal ↥L) (finQW L A hA)) :=
        smul_valuationSubringAtPrime L (τ.restrictNormal ↥L) (finQW L A hA)

/-- **The place form of `finQW_smulHeightOneSpectrum`.** -/
theorem ofFinite_finQW_smul (L : IntermediateField k Ω) [FiniteDimensional k L]
    [IsGalois k L] [NumberField L] (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (τ : Ω ≃ₐ[k] Ω) (hA' : SSGRoute.IsFinPlace k (τ • A)) :
    NK.GlobalCFT.Place.ofFinite (finQW L (τ • A) hA') =
      (τ.restrictNormal ↥L) • NK.GlobalCFT.Place.ofFinite (finQW L A hA) := by
  rw [finQW_smulHeightOneSpectrum L A hA τ hA', NK.GlobalCFT.Place.smul_ofFinite]

/-- Nonarchimedeanness of a place of `L` is invariant under `Gal(L/k)`. -/
theorem isFinite_smul_iff (L : IntermediateField k Ω) [FiniteDimensional k L] [IsGalois k L]
    [NumberField L] (σ : ↥L ≃ₐ[k] ↥L) (w : NK.GlobalCFT.Place ↥L) :
    (σ • w).IsFinite ↔ w.IsFinite := by
  cases w with
  | inl w => simp [NK.GlobalCFT.Place.IsFinite, NK.GlobalCFT.Place.IsInfinite]
  | inr q => simp [NK.GlobalCFT.Place.IsFinite, NK.GlobalCFT.Place.IsInfinite]

/-- **Lifting an automorphism of a level to `Ω`.**  Every `σ : Gal(L/k)` is the restriction of
some `k`-automorphism of the algebraic closure `Ω`. -/
theorem exists_restrictNormal_eq_of_isAlgClosure (L : IntermediateField k Ω)
    [FiniteDimensional k L] [IsGalois k L] [NumberField L] (σ : ↥L ≃ₐ[k] ↥L) :
    ∃ τ : Ω ≃ₐ[k] Ω, τ.restrictNormal ↥L = σ :=
  AlgEquiv.restrictNormalHom_surjective (F := k) (K₁ := ↥L) Ω σ

/-- **Transitivity of the Galois action on the prolongations of a place to `Ω`.**  Two places of
`Ω` with the same trace on `L` are conjugate under `Gal(Ω/L)`. -/
theorem exists_smul_eq_of_comap_eq_of_isAlgClosure (L : IntermediateField k Ω)
    [FiniteDimensional k L] [NumberField L] (A B : ValuationSubring Ω)
    (h : A.comap (algebraMap ↥L Ω) = B.comap (algebraMap ↥L Ω)) :
    ∃ ρ : Ω ≃ₐ[↥L] Ω, ρ • A = B := by
  haveI : IsAlgClosure ↥L Ω := ⟨IsAlgClosure.isAlgClosed k, inferInstance⟩
  haveI : IsGalois ↥L Ω := IsSepClosure.isGalois (k := ↥L) (K := Ω)
  exact Commons.RingTheory.Valuation.exists_smul_eq_of_comap_eq (F := ↥L) A B h

/-- **The combination of a `k`-automorphism and an `L`-automorphism of `Ω` is a conjugacy over
`k`.** -/
theorem isConjPlace_of_smul_smul (L : IntermediateField k Ω) [FiniteDimensional k L]
    [NumberField L] {A B : ValuationSubring Ω} (τ : Ω ≃ₐ[k] Ω) (ρ : Ω ≃ₐ[↥L] Ω)
    (h : ρ • (τ • A) = B) : SSGRoute.IsConjPlace k A B :=
  ⟨(AlgEquiv.restrictScalars k ρ) * τ, by
    have h' : (AlgEquiv.restrictScalars k ρ) • (τ • A) = B := h
    rw [mul_smul]
    exact h'⟩

end Work.SSGRoute.PT
