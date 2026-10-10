import Mathlib.RingTheory.Ideal.Norm.RelNorm
import Submission.NK.CFTLib.ArtinReciprocityIdeal.artinSym_restrict_relNorm
import Submission.Work.SSGRoute.ZDataMup.ArtinReciprocity.IdealModulus.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The Artin symbol commutes with restriction and the relative norm (ideal moduli)

Ideal-modulus version of `NK.CFTLib.ArtinReciprocityIdeal.artinSym_restrict_relNorm`: for
intermediate fields `E, L` of a finite Galois extension `M/K`, an ideal modulus `𝔪` of `K` and an
ideal modulus `𝔠` of `E` with `𝔠 ≤ 𝔪·𝓞_E`, the restriction of `ψ_{M/E}(𝔄)` to `L` is
`ψ_{L/K}(N_{E/K}𝔄)` for every `𝔄` coprime to `𝔠`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 2000000

open scoped NumberField nonZeroDivisors
open NumberField IsDedekindDomain

noncomputable section

namespace Work.SSGRoute.ZDataMup.MupAux

theorem artinSymId_restrict_relNorm {K M : Type} [Field K] [NumberField K] [Field M]
    [NumberField M] [Algebra K M] [FiniteDimensional K M] [IsGalois K M]
    (E L : IntermediateField K M) [FiniteDimensional K ↥E] [NumberField ↥E]
    [FiniteDimensional K ↥L] [NumberField ↥L] [IsGalois K ↥L]
    (hcommE : ∀ a b : M ≃ₐ[↥E] M, a * b = b * a)
    (hcommL : ∀ a b : (↥L ≃ₐ[K] ↥L), a * b = b * a)
    (𝔪 : Ideal (NumberField.RingOfIntegers K)) (𝔠 : Ideal (NumberField.RingOfIntegers ↥E))
    (hle : 𝔠 ≤ Ideal.map (algebraMap (NumberField.RingOfIntegers K)
      (NumberField.RingOfIntegers ↥E)) 𝔪)
    (hramE : ∀ 𝔮 : HeightOneSpectrum (NumberField.RingOfIntegers ↥E),
      ¬ NK.CFTLib.ArtinReciprocityIdeal.IsUnramified (K := ↥E) (L := M) 𝔮 →
        NK.CFTLib.ArtinReciprocityIdeal.DvdPrime 𝔠 𝔮)
    (hram : ∀ p : HeightOneSpectrum (NumberField.RingOfIntegers K),
      ¬ NK.CFTLib.ArtinReciprocityIdeal.IsUnramified (K := K) (L := ↥L) p →
        NK.CFTLib.ArtinReciprocityIdeal.DvdPrime 𝔪 p)
    (𝔄 : (FractionalIdeal (𝓞 ↥E)⁰ ↥E)ˣ)
    (hcopA : NK.CFTLib.ArtinReciprocityIdeal.FracCoprimeId (K := ↥E) 𝔠 𝔄) :
    AlgEquiv.restrictNormalHom (F := K) (K₁ := M) ↥L
        ((NK.CFTLib.Arl.artinSym (K := ↥E) (L := M) hcommE
            (𝔄 : FractionalIdeal (𝓞 ↥E)⁰ ↥E)).restrictScalars K)
      = NK.CFTLib.Arl.artinSym (K := K) (L := ↥L) hcommL
          (NK.CFTLib.ARL.relNormUnit (K := K) (L := ↥E) 𝔄) := by
  classical
  haveI hMC_E : IsMulCommutative (M ≃ₐ[↥E] M) := ⟨⟨hcommE⟩⟩
  haveI hMC_L : IsMulCommutative (↥L ≃ₐ[K] ↥L) := ⟨⟨hcommL⟩⟩
  letI : CommMonoid (M ≃ₐ[↥E] M) := NK.CFTLib.Arl.galCommMonoid hcommE
  letI : CommMonoid (↥L ≃ₐ[K] ↥L) := NK.CFTLib.Arl.galCommMonoid hcommL
  let Φ : (M ≃ₐ[↥E] M) →* (↥L ≃ₐ[K] ↥L) :=
    (AlgEquiv.restrictNormalHom (F := K) (K₁ := M) L).comp (AlgEquiv.restrictScalarsHom K)
  let F : NK.CFTLib.ArtinReciprocityIdeal.Frac ↥E →* (↥L ≃ₐ[K] ↥L) :=
    Φ.comp (NK.CFTLib.ArtinReciprocityIdeal.artinSymFracHom (K := ↥E) (L := M) hcommE)
  let G : NK.CFTLib.ArtinReciprocityIdeal.Frac ↥E →* (↥L ≃ₐ[K] ↥L) :=
    (NK.CFTLib.ArtinReciprocityIdeal.artinSymFracHom (K := K) (L := ↥L) hcommL).comp
      (NK.CFTLib.ARL.relNormUnit (K := K) (L := ↥E))
  have hFG : F 𝔄 = G 𝔄 := by
    set S : Finset (NK.Chebotarev.PrimeIdeal ↥E) :=
      (Filter.eventually_cofinite.mp (FractionalIdeal.finite_factors (K := ↥E)
        (𝔄 : FractionalIdeal (𝓞 ↥E)⁰ ↥E))).toFinset with hS
    have hSmem : ∀ 𝔮 : NK.Chebotarev.PrimeIdeal ↥E,
        𝔮 ∈ S ↔ FractionalIdeal.count ↥E 𝔮 (𝔄 : FractionalIdeal (𝓞 ↥E)⁰ ↥E) ≠ 0 :=
      fun 𝔮 => Set.Finite.mem_toFinset _
    have hsupp : Function.mulSupport (fun 𝔮 : NK.Chebotarev.PrimeIdeal ↥E =>
        ((𝔮.asIdeal : Ideal (𝓞 ↥E)) : FractionalIdeal (𝓞 ↥E)⁰ ↥E) ^
          FractionalIdeal.count ↥E 𝔮 (𝔄 : FractionalIdeal (𝓞 ↥E)⁰ ↥E)) ⊆ ↑S := by
      intro 𝔮 h𝔮
      exact (hSmem 𝔮).mpr fun h0 => h𝔮 (by simp only [h0, zpow_zero])
    have hfac : (∏ 𝔮 ∈ S, (NK.CFTLib.ARL.primeUnit 𝔮) ^
        FractionalIdeal.count ↥E 𝔮 (𝔄 : FractionalIdeal (𝓞 ↥E)⁰ ↥E)) = 𝔄 := by
      apply Units.ext
      rw [Units.coe_prod]
      simp only [NK.CFTLib.ARL.primeUnit_val, Units.val_zpow_eq_zpow_val]
      rw [← finprod_eq_prod_of_mulSupport_subset _ hsupp]
      exact FractionalIdeal.finprod_heightOneSpectrum_factorization' ↥E 𝔄.ne_zero
    have hprime : ∀ 𝔮 ∈ S, F (NK.CFTLib.ARL.primeUnit 𝔮)
        = G (NK.CFTLib.ARL.primeUnit 𝔮) := by
      intro 𝔮 h𝔮
      have hcount : FractionalIdeal.count ↥E 𝔮 (𝔄 : FractionalIdeal (𝓞 ↥E)⁰ ↥E) ≠ 0 :=
        (hSmem 𝔮).mp h𝔮
      have hunrE : NK.CFTLib.ArtinReciprocityIdeal.IsUnramified (K := ↥E) (L := M) 𝔮 := by
        by_contra h
        exact hcount (hcopA 𝔮 (hramE 𝔮 h))
      have hunrL : NK.CFTLib.ArtinReciprocityIdeal.IsUnramified (K := K) (L := ↥L)
          (𝔮.under (𝓞 K)) := by
        by_contra h
        have h𝔪 : 𝔪 ≤ (𝔮.under (𝓞 K)).asIdeal := hram (𝔮.under (𝓞 K)) h
        have hmap_le : Ideal.map (algebraMap (𝓞 K) (𝓞 ↥E)) 𝔪 ≤ 𝔮.asIdeal := by
          refine le_trans (Ideal.map_mono h𝔪) ?_
          rw [HeightOneSpectrum.under_asIdeal]
          exact Ideal.map_le_iff_le_comap.mpr le_rfl
        exact hcount (hcopA 𝔮 (le_trans hle hmap_le))
      have hF : F (NK.CFTLib.ARL.primeUnit 𝔮) = AlgEquiv.restrictNormalHom (F := K)
          (K₁ := M) L
          ((NK.Chebotarev.frobAtPrime (K := ↥E) (L := M) 𝔮).restrictScalars K) := by
        change Φ (NK.CFTLib.ArtinReciprocityIdeal.artinSymFracHom (K := ↥E) (L := M) hcommE
          (NK.CFTLib.ARL.primeUnit 𝔮)) = _
        rw [NK.CFTLib.ArtinReciprocityIdeal.artinSymFracHom_apply, NK.CFTLib.ARL.primeUnit_val,
          NK.CFTLib.Arl.artinSym_prime]
        rfl
      have hG : G (NK.CFTLib.ARL.primeUnit 𝔮) = (NK.Chebotarev.frobAtPrime (K := K)
          (L := ↥L) (𝔮.under (𝓞 K))) ^ (𝔮.asIdeal.inertiaDeg (𝓞 K)) := by
        haveI : 𝔮.asIdeal.IsMaximal :=
          Ring.DimensionLEOne.maximalOfPrime 𝔮.ne_bot 𝔮.isPrime
        have hqne : (𝔮.under (𝓞 K)).asIdeal ≠ ⊥ := by
          rw [HeightOneSpectrum.under_asIdeal]
          exact Ideal.under_ne_bot (𝓞 K) 𝔮.ne_bot
        haveI : ((𝔮.under (𝓞 K)).asIdeal).IsMaximal :=
          Ring.DimensionLEOne.maximalOfPrime hqne inferInstance
        haveI : 𝔮.asIdeal.LiesOver (𝔮.under (𝓞 K)).asIdeal :=
          ⟨HeightOneSpectrum.under_asIdeal (𝓞 K) 𝔮⟩
        change NK.CFTLib.ArtinReciprocityIdeal.artinSymFracHom (K := K) (L := ↥L) hcommL
          (NK.CFTLib.ARL.relNormUnit (K := K) (L := ↥E)
            (NK.CFTLib.ARL.primeUnit 𝔮)) = _
        rw [NK.CFTLib.ARL.relNormUnit_primeUnit,
          NK.CFTLib.ArtinReciprocityIdeal.artinSymFracHom_apply, Units.val_mk0,
          Ideal.relNorm_eq_pow_of_isMaximal 𝔮.asIdeal ((𝔮.under (𝓞 K)).asIdeal),
          FractionalIdeal.coeIdeal_pow,
          NK.CFTLib.ArtinReciprocityIdeal.artinSymFrac_pow hcommL
            (FractionalIdeal.coeIdeal_ne_zero.mpr ((𝔮.under (𝓞 K)).ne_bot)),
          NK.CFTLib.Arl.artinSym_prime]
      rw [hF, hG]
      exact NK.CFTLib.ArtinReciprocityIdeal.restrict_frobAtPrime_eq E L hcommE hcommL 𝔮
        hunrE hunrL
    calc F 𝔄 = F (∏ 𝔮 ∈ S, (NK.CFTLib.ARL.primeUnit 𝔮) ^
            FractionalIdeal.count ↥E 𝔮 (𝔄 : FractionalIdeal (𝓞 ↥E)⁰ ↥E)) := by rw [hfac]
      _ = ∏ 𝔮 ∈ S, F (NK.CFTLib.ARL.primeUnit 𝔮) ^
            FractionalIdeal.count ↥E 𝔮 (𝔄 : FractionalIdeal (𝓞 ↥E)⁰ ↥E) := by
          rw [map_prod]
          exact Finset.prod_congr rfl fun 𝔮 _ => map_zpow _ _ _
      _ = ∏ 𝔮 ∈ S, G (NK.CFTLib.ARL.primeUnit 𝔮) ^
            FractionalIdeal.count ↥E 𝔮 (𝔄 : FractionalIdeal (𝓞 ↥E)⁰ ↥E) :=
          Finset.prod_congr rfl fun 𝔮 h𝔮 => by rw [hprime 𝔮 h𝔮]
      _ = G (∏ 𝔮 ∈ S, (NK.CFTLib.ARL.primeUnit 𝔮) ^
            FractionalIdeal.count ↥E 𝔮 (𝔄 : FractionalIdeal (𝓞 ↥E)⁰ ↥E)) := by
          rw [map_prod]
          exact Finset.prod_congr rfl fun 𝔮 _ => (map_zpow _ _ _).symm
      _ = G 𝔄 := by rw [hfac]
  simpa only [F, G, Φ, MonoidHom.comp_apply,
    NK.CFTLib.ArtinReciprocityIdeal.artinSymFracHom_apply, AlgEquiv.restrictScalarsHom_apply]
    using hFG

end Work.SSGRoute.ZDataMup.MupAux
