import Mathlib
import Submission.Work.SSGRoute.E1aClean.LocalData
import Submission.Work.SSGRoute.local_ext_h1_bridge
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The cyclotomic-dual data at the local closure

The local dictionary of the E1a node is built over the completion datum `(k_v, Ω_v, K′)` of E7a.  Its
coefficient identification `E ≅ Hom_ℤ(E′,Ω_vˣ)` — hence its naturality in `E` — needs the local
analogue of the global hypothesis `hT : IsCyclotomicDual p T (res k K) ζ`: a primitive `p`-th root
`ζ′` in the local closure and a comparison `act` from the *local* Galois group to `Gal(K/k)` making
`T` cyclotomic-dual to `ζ′`.

This file extracts that construction (the `(1)`/`(2)` blocks of the proof of
`Work.SSGRoute.local_ext_h1_bridge`) as a standalone lemma, so that the *named* assembly
`localDictFamilyNatural` can instantiate the field-generic coefficient isomorphism
`E1aClean.coeffIso_natural_generic` at the local datum.
-/

namespace Work.SSGRoute.E1aClean

open CategoryTheory SSGRoute.PTExt

noncomputable section

set_option maxHeartbeats 8000000

theorem localClosureCyclotomicDual (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsSepClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] [NumberField K] (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hAq : ∀ x : NumberField.RingOfIntegers K, x ∈ q.asIdeal ↔ A.valuation (((x : K) : Ω)) < 1) :
    ∃ (K' : IntermediateField (Work.SSGRoute.localFieldAt k A hA) (Work.SSGRoute.localClosureAt k A hA))
      (_ : FiniteDimensional (Work.SSGRoute.localFieldAt k A hA) K')
      (_ : IsGalois (Work.SSGRoute.localFieldAt k A hA) K')
      (eG : ↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)) ≃*
        (K' ≃ₐ[Work.SSGRoute.localFieldAt k A hA] K'))
      (_hRep : Nonempty (SSGRoute.PTExt.localUnitsK (k := k) (NK.GlobalCFT.Place.ofFinite q) ≅
        Rep.res eG.toMonoidHom (SSGRoute.PTExt.modRep
          (K' ≃ₐ[Work.SSGRoute.localFieldAt k A hA] K') (Additive (Units ↥K')))))
      (Φ : ↥(SSGRoute.decomp k A) ≃*
        (Work.SSGRoute.localClosureAt k A hA ≃ₐ[Work.SSGRoute.localFieldAt k A hA]
          Work.SSGRoute.localClosureAt k A hA))
      (_hΦhomeo : IsHomeomorph (Φ : ↥(SSGRoute.decomp k A) →
          (Work.SSGRoute.localClosureAt k A hA ≃ₐ[Work.SSGRoute.localFieldAt k A hA]
            Work.SSGRoute.localClosureAt k A hA)))
      (ζ' : Work.SSGRoute.localClosureAt k A hA)
      (act : (Work.SSGRoute.localClosureAt k A hA ≃ₐ[Work.SSGRoute.localFieldAt k A hA]
          Work.SSGRoute.localClosureAt k A hA) →* (K ≃ₐ[k] K)),
      (act = (SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)).subtype.comp
        (eG.symm.toMonoidHom.comp
          (AlgEquiv.restrictNormalHom (F := Work.SSGRoute.localFieldAt k A hA)
            (K₁ := Work.SSGRoute.localClosureAt k A hA) ↥K'))) ∧
      (∀ σ : ↥(SSGRoute.decomp k A), act (Φ σ) = SSGRoute.res k K (σ : Ω ≃ₐ[k] Ω)) ∧
      IsPrimitiveRoot ζ' p ∧
      SSGRoute.IsCyclotomicDual p (T := T) act ζ' := by
  classical
  letI : Algebra (Work.SSGRoute.localFieldAt k A hA)
      (NK.NeukirchUchida.placeCompletion A) :=
    (NK.NeukirchUchida.adicCompletionToPlaceCompletion (K := k) (K' := Ω)
      (Work.SSGRoute.primeUnder k A hA) A (Submission.NeukirchUchida.primeOf_spec A hA)).toAlgebra
  letI : Algebra (Work.SSGRoute.localFieldAt k A hA) (q.adicCompletion K) :=
    (Work.SSGRoute.adicCompletionMapAt k Ω K A hA q
      (Work.SSGRoute.exists_adicCompletion_algebra_compat k Ω K A hA q hAq).choose).toAlgebra
  obtain ⟨K', hfdK', hgalK', ψ, eG, Φ, e, hΦhomeo2, hRep2, hpin, hcompatΦ2, _hψ⟩ :=
    Work.SSGRoute.E1aClean.exists_localData p k Ω K A hA q hAq
  haveI : FiniteDimensional (Work.SSGRoute.localFieldAt k A hA) K' := hfdK'
  haveI : IsGalois (Work.SSGRoute.localFieldAt k A hA) K' := hgalK'
  -- ## (1) the primitive root of unity in the local closure
  let ζi : ↥K := ⟨ζ, hζK⟩
  let ζK : ↥K' := ψ.symm (algebraMap ↥K (q.adicCompletion K) ζi)
  let ζ' : Work.SSGRoute.localClosureAt k A hA :=
    algebraMap ↥K' (Work.SSGRoute.localClosureAt k A hA) ζK
  have hζi : IsPrimitiveRoot ζi p := by
    show IsPrimitiveRoot (⟨ζ, hζK⟩ : ↥K) p
    exact IsPrimitiveRoot.of_map_of_injective (f := algebraMap ↥K Ω) (by simpa using hζ)
      (RingHom.injective _)
  have hζKprim : IsPrimitiveRoot ζK p := by
    have h1 : IsPrimitiveRoot (algebraMap ↥K (q.adicCompletion K) ζi) p :=
      hζi.map_of_injective (f := algebraMap ↥K (q.adicCompletion K)) (RingHom.injective _)
    have h2 : ψ ζK = algebraMap ↥K (q.adicCompletion K) ζi := AlgEquiv.apply_symm_apply ψ ζi
    rw [← h2] at h1
    have h3 := h1.map_of_injective (f := ψ.symm.toMulEquiv)
      (fun a b hab => MulEquiv.injective ψ.symm.toMulEquiv hab)
    simpa using h3
  have hζ' : IsPrimitiveRoot ζ' p :=
    hζKprim.map_of_injective (f := algebraMap ↥K' (Work.SSGRoute.localClosureAt k A hA))
      (RingHom.injective _)
  -- ## (2) the comparison map and the cyclotomic-dual property
  let act : (Work.SSGRoute.localClosureAt k A hA ≃ₐ[Work.SSGRoute.localFieldAt k A hA]
      Work.SSGRoute.localClosureAt k A hA) →* (K ≃ₐ[k] K) :=
    (decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)).subtype.comp
      (eG.symm.toMonoidHom.comp
        (AlgEquiv.restrictNormalHom (F := Work.SSGRoute.localFieldAt k A hA)
          (K₁ := Work.SSGRoute.localClosureAt k A hA) ↥K'))
  have hcyc : SSGRoute.IsCyclotomicDual p (T := T) act ζ' := by
    refine ⟨hT.1, ?_⟩
    intro γ c hc t
    have hkey : (act γ) ζi = ζi ^ c := by
      set τ : ↥(decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)) :=
        eG.symm (AlgEquiv.restrictNormalHom (F := Work.SSGRoute.localFieldAt k A hA)
          (K₁ := Work.SSGRoute.localClosureAt k A hA) ↥K' γ) with hτ
      have hactγ : act γ = (decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)).subtype τ := rfl
      have heGτ : eG τ = AlgEquiv.restrictNormalHom (F := Work.SSGRoute.localFieldAt k A hA)
          (K₁ := Work.SSGRoute.localClosureAt k A hA) ↥K' γ := by
        rw [hτ]; exact MulEquiv.apply_symm_apply _ _
      have hψ : ψ ζK = algebraMap ↥K (q.adicCompletion K) ζi := AlgEquiv.apply_symm_apply ψ ζi
      have hgam : (γ : Work.SSGRoute.localClosureAt k A hA ≃ₐ[Work.SSGRoute.localFieldAt k A hA]
            Work.SSGRoute.localClosureAt k A hA) (ζK : Work.SSGRoute.localClosureAt k A hA)
          = ((eG τ) ζK : Work.SSGRoute.localClosureAt k A hA) := by
        rw [heGτ, AlgEquiv.restrictNormalHom_apply]
      have hstep : (γ : Work.SSGRoute.localClosureAt k A hA ≃ₐ[Work.SSGRoute.localFieldAt k A hA]
            Work.SSGRoute.localClosureAt k A hA) (ζK : Work.SSGRoute.localClosureAt k A hA)
          = ((ψ.symm (NK.HassePrinciple.localAut (K := k) (L := ↥K)
              (NK.GlobalCFT.Place.ofFinite q) τ (ψ ζK)))
            : Work.SSGRoute.localClosureAt k A hA) := by
        rw [hgam, hpin τ ζK]
      have hc' : (γ : Work.SSGRoute.localClosureAt k A hA ≃ₐ[Work.SSGRoute.localFieldAt k A hA]
            Work.SSGRoute.localClosureAt k A hA) (ζK : Work.SSGRoute.localClosureAt k A hA)
          = ((ζK : Work.SSGRoute.localClosureAt k A hA)) ^ c := hc
      have hconv : ψ.symm (NK.HassePrinciple.localAut (K := k) (L := ↥K)
            (NK.GlobalCFT.Place.ofFinite q) τ (ψ ζK)) = ζK ^ c := by
        apply Subtype.ext
        have hcoe : ∀ z : ↥K',
            (↑z : Work.SSGRoute.localClosureAt k A hA)
              = algebraMap ↥K' (Work.SSGRoute.localClosureAt k A hA) z := fun z => rfl
        rw [hcoe (ζK ^ c), map_pow (algebraMap ↥K' (Work.SSGRoute.localClosureAt k A hA)) ζK c]
        rw [hcoe ζK] at hstep
        exact hstep.symm.trans hc
      have h6 : NK.HassePrinciple.localAut (K := k) (L := ↥K) (NK.GlobalCFT.Place.ofFinite q) τ
            (algebraMap ↥K (q.adicCompletion K) ζi)
          = (algebraMap ↥K (q.adicCompletion K) ζi) ^ c := by
        have hh := congrArg (fun z : ↥K' => ψ z) hconv
        rw [map_pow] at hh
        simpa [hψ] using hh
      have h8 : algebraMap ↥K (q.adicCompletion K) (τ.1 ζi)
          = (algebraMap ↥K (q.adicCompletion K) ζi) ^ c := by
        have hlemma : NK.HassePrinciple.localAut (K := k) (L := ↥K)
              (NK.GlobalCFT.Place.ofFinite q) τ (algebraMap ↥K (q.adicCompletion K) ζi)
            = algebraMap ↥K (q.adicCompletion K) (τ.1 ζi) :=
          NK.HassePrinciple.localAut_algebraMap (K := k) (L := ↥K)
            (NK.GlobalCFT.Place.ofFinite q) τ ζi
        rw [← hlemma]
        exact h6
      have h9 : τ.1 ζi = ζi ^ c := by
        apply RingHom.injective (algebraMap ↥K (q.adicCompletion K))
        rw [map_pow]
        exact h8
      rw [hactγ]
      exact h9
    obtain ⟨σtilde, hσtilde⟩ :=
      AlgEquiv.restrictNormalHom_surjective (F := k) Ω (act γ)
    have hσζ : σtilde • ζ = ζ ^ c := by
      show σtilde ζ = ζ ^ c
      have hone : ((SSGRoute.res k K σtilde) ζi : Ω) = ζ ^ c := by
        have h : (SSGRoute.res k K σtilde) ζi = ζi ^ c := by
          rw [show SSGRoute.res k K σtilde = act γ from hσtilde]
          exact hkey
        have h2 := congrArg (fun z : ↥K => (z : Ω)) h
        simpa [ζi] using h2
      rwa [AlgEquiv.restrictNormalHom_apply] at hone
    have hfin := hT.2 σtilde c hσζ t
    simpa [SSGRoute.res, hσtilde] using hfin
  have hact_eq2 : ∀ σ : ↥(SSGRoute.decomp k A),
      act (Φ σ) = SSGRoute.res k K (σ : Ω ≃ₐ[k] Ω) := by
    intro σ
    refine AlgEquiv.ext fun x => ?_
    set τ : ↥(decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)) :=
      eG.symm (AlgEquiv.restrictNormalHom (F := Work.SSGRoute.localFieldAt k A hA)
        (K₁ := Work.SSGRoute.localClosureAt k A hA) ↥K' (Φ σ)) with hτ
    have hactσ : act (Φ σ) =
        (decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)).subtype τ := rfl
    have heGτ : eG τ = AlgEquiv.restrictNormalHom (F := Work.SSGRoute.localFieldAt k A hA)
        (K₁ := Work.SSGRoute.localClosureAt k A hA) ↥K' (Φ σ) := by
      rw [hτ]; exact MulEquiv.apply_symm_apply _ _
    have h1 : NK.HassePrinciple.localAut (K := k) (L := ↥K) (NK.GlobalCFT.Place.ofFinite q) τ
        (algebraMap ↥K (q.adicCompletion K) x) =
        algebraMap ↥K (q.adicCompletion K) ((SSGRoute.res k K (σ : Ω ≃ₐ[k] Ω)) x) := by
      have h2 := congrArg (fun z : ↥K' => (z : Work.SSGRoute.localClosureAt k A hA))
        (hpin τ (ψ.symm (algebraMap ↥K (q.adicCompletion K) x)))
      rw [AlgEquiv.apply_symm_apply] at h2
      rw [heGτ, AlgEquiv.restrictNormalHom_apply] at h2
      rw [hcompatΦ2 σ x] at h2
      exact ψ.symm.injective (Subtype.ext h2.symm)
    rw [NK.HassePrinciple.localAut_algebraMap (K := k) (L := ↥K)
      (NK.GlobalCFT.Place.ofFinite q) τ x] at h1
    have h4 : τ.1 x = (SSGRoute.res k K (σ : Ω ≃ₐ[k] Ω)) x :=
      RingHom.injective (algebraMap ↥K (q.adicCompletion K)) h1
    show (act (Φ σ)) x = _
    rw [hactσ]
    exact h4
  exact ⟨K', hfdK', hgalK', eG, hRep2, Φ, hΦhomeo2, ζ', act, rfl, hact_eq2, hζ', hcyc⟩

end

end Work.SSGRoute.E1aClean
