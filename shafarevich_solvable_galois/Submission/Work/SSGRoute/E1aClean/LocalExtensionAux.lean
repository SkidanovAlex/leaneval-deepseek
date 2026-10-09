import Mathlib
import Submission.Work.SSGRoute.localField_subfield_place_compat
import Submission.Work.SSGRoute.localUnitsK_iso_intermediateField_pointwise
import Submission.Work.SSGRoute.exists_adicCompletion_algebra_compat
import Submission.Work.SSGRoute.E1aClean.BaseChangeSquareStep3
import Submission.Work.SSGRoute.localAutHom_bijective
import Submission.Work.SSGRoute.map_restrictNormalHom_decomp_eq
import Submission.NK.Reconstruct.PlaceCorrespondence
import Submission.Commons.RingTheory.Valuation.valuationSubringAtPrime_injective
import Submission.Work.SSGRoute.place_comap_valuationSubringAtPrime
import Submission.Work.SSGRoute.PT.exists_localField_place_data
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Auxiliary lemmas for the local extension statement of the `E1a` node

This module collects the auxiliary facts used by
`Submission/Work/SSGRoute/E1aClean/exists_localExtension.lean`.
-/

namespace Work.SSGRoute.E1aClean

open CategoryTheory SSGRoute.PTExt
open scoped Pointwise

attribute [local instance 10000] Rep.hV1 Rep.hV2

noncomputable section

attribute [instance] ValuationSubring.pointwiseMulAction
attribute [instance] Ideal.pointwiseDistribMulAction
attribute [instance] Ideal.pointwiseMulSemiringAction

/-- Auxiliary: the pointwise Galois action on ideals of `𝓞 K` is the action through
`NK.GlobalCFT.Place.ringOfIntegersEquiv`. -/
lemma smul_asIdeal_eq_map_ringOfIntegersEquiv (k K : Type) [Field k] [NumberField k] [Field K]
    [NumberField K] [Algebra k K] [IsGalois k K] (τ : K ≃ₐ[k] K)
    (I : Ideal (NumberField.RingOfIntegers K)) :
    τ • I = Ideal.map (NK.GlobalCFT.Place.ringOfIntegersEquiv τ) I := by
  rw [Ideal.pointwise_smul_def]
  congr 1

/-- Auxiliary: the decomposition group of a finite place `Place.ofFinite q` is the stabiliser of
the prime `q.asIdeal` under the Galois action on ideals. -/
lemma decompK_ofFinite_eq_stabilizer_asIdeal (k K : Type) [Field k] [NumberField k] [Field K]
    [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    SSGRoute.PTExt.decompK (k := k) (K := K) (NK.GlobalCFT.Place.ofFinite q)
      = MulAction.stabilizer (K ≃ₐ[k] K) q.asIdeal := by
  ext τ
  rw [MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff]
  constructor
  · intro h
    have h2 : NK.GlobalCFT.Place.smulHeightOneSpectrum τ q = q :=
      NK.GlobalCFT.Place.ofFinite_inj.mp (by rw [← NK.GlobalCFT.Place.smul_ofFinite]; exact h)
    rw [smul_asIdeal_eq_map_ringOfIntegersEquiv]
    exact congrArg IsDedekindDomain.HeightOneSpectrum.asIdeal h2
  · intro h
    rw [NK.GlobalCFT.Place.smul_ofFinite, NK.GlobalCFT.Place.ofFinite_inj]
    exact IsDedekindDomain.HeightOneSpectrum.ext
      ((smul_asIdeal_eq_map_ringOfIntegersEquiv k K τ q.asIdeal).trans h)

/-- **The image of the decomposition group of a finite place `A` of `Ω` under restriction to `K`
is the decomposition group of the prime `q` of `K` below it.** -/
theorem decomp_map_res_eq_decompK
    (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K] [NumberField K]
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hAq : ∀ x : NumberField.RingOfIntegers K,
      x ∈ q.asIdeal ↔ A.valuation (((x : K) : Ω)) < 1) :
    (SSGRoute.decomp k A).map (SSGRoute.res k K) =
      SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q) := by
  rw [Work.SSGRoute.map_restrictNormalHom_decomp_eq k Ω A hA K,
    decompK_ofFinite_eq_stabilizer_asIdeal k K q]
  have hP : Work.SSGRoute.levelPrime k Ω A hA K = q := by
    refine (Commons.RingTheory.Valuation.valuationSubringAtPrime_injective
      (R := NumberField.RingOfIntegers ↥K) (K := ↥K)) ?_
    have h1 : A.comap (algebraMap ↥K Ω) =
        IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K
          (Work.SSGRoute.levelPrime k Ω A hA K) :=
      NK.Reconstruct.primeOfLevel_spec A K (NK.Reconstruct.comap_level_ne_top hA K)
    have h2 : A.comap (algebraMap ↥K Ω) =
        IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K q :=
      Work.SSGRoute.place_comap_valuationSubringAtPrime k Ω K A hA q hAq
    exact h1.symm.trans h2
  rw [show Work.SSGRoute.levelDecompAt k Ω A hA K
      = MulAction.stabilizer (↥K ≃ₐ[k] ↥K) (Work.SSGRoute.levelPrime k Ω A hA K).asIdeal
    from rfl, hP]

/-- Element-level form of `decomp_map_res_eq_decompK`: every element of the decomposition group of
`q` is the restriction of an element of the decomposition group of `A`. -/
theorem exists_res_eq_of_mem_decompK
    (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K] [NumberField K]
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hAq : ∀ x : NumberField.RingOfIntegers K,
      x ∈ q.asIdeal ↔ A.valuation (((x : K) : Ω)) < 1)
    (τ : ↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q))) :
    ∃ σ : ↥(SSGRoute.decomp k A),
      SSGRoute.res k K (σ : Ω ≃ₐ[k] Ω) = (τ : K ≃ₐ[k] K) := by
  have h := decomp_map_res_eq_decompK k Ω K A hA q hAq
  have hmem : (τ : K ≃ₐ[k] K) ∈ (SSGRoute.decomp k A).map (SSGRoute.res k K) := by
    rw [h]; exact τ.2
  obtain ⟨σ, hσ, hres⟩ := Subgroup.mem_map.mp hmem
  exact ⟨⟨σ, hσ⟩, hres⟩


/-- The applied form of the invariance of an `H⁰`-element of `homCoind`: an `H⁰`-element `Ψ` of
`Hom_ℤ(M, Ωˣ)` over the decomposition group `D_A` satisfies `Ψ (ρ(σ) x) = σ • Ψ x` for
`σ ∈ D_A`. -/
lemma homCoind_invariance_apply
    {k : Type} [Field k] {Ω : Type} [Field Ω] [Algebra k Ω]
    {K : IntermediateField k Ω} [Normal k K]
    {M : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)}
    (A : ValuationSubring Ω)
    (Ψ : ↥(Work.AbsoluteKummer.H0 (SSGRoute.decomp k A) (Work.SSGRoute.homCoind k Ω K M)))
    (τ : ↥(SSGRoute.decomp k A)) (x : M.V) :
    (Ψ : Work.SSGRoute.homCoind k Ω K M) (M.ρ (SSGRoute.res k K (τ : Ω ≃ₐ[k] Ω)) x)
      = τ • ((Ψ : Work.SSGRoute.homCoind k Ω K M) x) := by
  have h2 : (τ : Ω ≃ₐ[k] Ω) • (Ψ : Work.SSGRoute.homCoind k Ω K M)
      = (Ψ : Work.SSGRoute.homCoind k Ω K M) := Ψ.2 τ
  have h := DFunLike.congr_fun h2 (M.ρ (SSGRoute.res k K (τ : Ω ≃ₐ[k] Ω)) x)
  rw [Work.SSGRoute.homCoind.smul_apply] at h
  rw [show (M.ρ ((SSGRoute.res k K (τ : Ω ≃ₐ[k] Ω))⁻¹))
      (M.ρ (SSGRoute.res k K (τ : Ω ≃ₐ[k] Ω)) x) = x from by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]] at h
  exact h.symm

end

end Work.SSGRoute.E1aClean
namespace Work.SSGRoute.E1aClean

open CategoryTheory SSGRoute.PTExt
open scoped Pointwise

noncomputable section

/-- Two `F`-algebra automorphisms of `E` agreeing on a set `S` agree on the intermediate field
generated by `S`. -/
lemma eqOn_adjoin_of_eq {F E : Type*} [Field F] [Field E] [Algebra F E]
    (S : Set E) (f g : E ≃ₐ[F] E) (h : ∀ z ∈ S, f z = g z) :
    ∀ z ∈ IntermediateField.adjoin F S, f z = g z := by
  intro z hz
  refine IntermediateField.adjoin_induction F (s := S) (p := fun z _ => f z = g z)
    ?_ ?_ ?_ ?_ ?_ hz
  · intro x hx; exact h x hx
  · intro c; rw [AlgEquiv.commutes, AlgEquiv.commutes]
  · intro x y _ _ ihx ihy; rw [map_add, map_add, ihx, ihy]
  · intro x _ ih; rw [map_inv₀, map_inv₀, ih]
  · intro x y _ _ ihx ihy; rw [map_mul, map_mul, ihx, ihy]

end

end Work.SSGRoute.E1aClean
