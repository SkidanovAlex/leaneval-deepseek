import Mathlib
import Submission.Work.SSGRoute.ZDataMup.ArtinReciprocity.IdealModulus.Defs
import Submission.NK.NUV2.ARL.transferSelfContained
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Transport of the ideal-theoretic Artin symbol along a `K`-algebra isomorphism

Ideal-modulus version of `NK.NUV2.ARL.SC.artinSym_algEquiv`: the Artin symbol of a fractional ideal
`A` of `K` transports along `e : L₁ ≃ₐ[K] L₂` by conjugation, provided the primes occurring in `A`
are unramified (with the coprimality hypothesis `FracCoprimeId 𝔪 A` and the ramification hypothesis
`hram` supplying this).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

open scoped NumberField nonZeroDivisors
open NumberField IsDedekindDomain

noncomputable section

namespace Work.SSGRoute.ZDataMup.MupAux

/-- **The Artin symbol of a fractional ideal transports along a `K`-algebra isomorphism**, in the
ideal-modulus formulation: `ψ_{L₂/K}(A) = e ∘ ψ_{L₁/K}(A) ∘ e⁻¹`. -/
theorem artinSymId_algEquiv {K L₁ L₂ : Type} [Field K] [NumberField K] [Field L₁]
    [NumberField L₁] [Field L₂] [NumberField L₂] [Algebra K L₁] [Algebra K L₂]
    [FiniteDimensional K L₁] [FiniteDimensional K L₂] [IsGalois K L₁] [IsGalois K L₂]
    (e : L₁ ≃ₐ[K] L₂) (hc₁ : ∀ a b : L₁ ≃ₐ[K] L₁, a * b = b * a)
    (hc₂ : ∀ a b : L₂ ≃ₐ[K] L₂, a * b = b * a)
    (𝔪 : Ideal (NumberField.RingOfIntegers K))
    (hram : ∀ p : HeightOneSpectrum (NumberField.RingOfIntegers K),
      ¬ NK.CFTLib.ArtinReciprocityIdeal.IsUnramified (K := K) (L := L₁) p →
      NK.CFTLib.ArtinReciprocityIdeal.DvdPrime 𝔪 p)
    (A : FractionalIdeal (NumberField.RingOfIntegers K)⁰ K) (hA : A ≠ 0)
    (hcop : NK.CFTLib.ArtinReciprocityIdeal.FracCoprimeId 𝔪 (Units.mk0 A hA)) :
    NK.CFTLib.Arl.artinSym (K := K) (L := L₂) hc₂ A
      = NK.NUV2.ARL.SC.conjHom e (NK.CFTLib.Arl.artinSym (K := K) (L := L₁) hc₁ A) := by
  classical
  letI : CommMonoid Gal(L₁/K) := NK.CFTLib.Arl.galCommMonoid hc₁
  letI : CommMonoid Gal(L₂/K) := NK.CFTLib.Arl.galCommMonoid hc₂
  letI : IsMulCommutative Gal(L₁/K) := ⟨⟨hc₁⟩⟩
  letI : IsMulCommutative Gal(L₂/K) := ⟨⟨hc₂⟩⟩
  have hsmem : ∀ p : NK.Chebotarev.PrimeIdeal K,
      p ∈ (NK.CFTLib.Arl.exps A).support ↔ NK.CFTLib.Arl.exps A p ≠ 0 :=
    fun p => Finsupp.mem_support_iff
  have hfac : A = ((∏ p ∈ (NK.CFTLib.Arl.exps A).support,
      NK.CFTLib.ARL.primeUnit p ^ (NK.CFTLib.Arl.exps A p) :
        NK.CFTLib.ArtinReciprocityIdeal.Frac K) :
          FractionalIdeal (NumberField.RingOfIntegers K)⁰ K) := by
    rw [Units.coe_prod]
    simp only [NK.CFTLib.ARL.primeUnit_val, Units.val_zpow_eq_zpow_val]
    rw [show (∏ p ∈ (NK.CFTLib.Arl.exps A).support,
        ((p.asIdeal : Ideal (NumberField.RingOfIntegers K)) :
          FractionalIdeal (NumberField.RingOfIntegers K)⁰ K) ^ (NK.CFTLib.Arl.exps A p))
        = ∏ᶠ (p : NK.Chebotarev.PrimeIdeal K),
            ((p.asIdeal : Ideal (NumberField.RingOfIntegers K)) :
              FractionalIdeal (NumberField.RingOfIntegers K)⁰ K) ^ (NK.CFTLib.Arl.exps A p) from
      (finprod_eq_prod_of_mulSupport_subset _ (by
        intro p hp
        exact Finsupp.mem_support_iff.mpr (fun h0 => hp (by simp [h0])))).symm]
    exact (FractionalIdeal.finprod_heightOneSpectrum_factorization' K hA).symm
  have hle : ∀ p ∈ (NK.CFTLib.Arl.exps A).support,
      ¬ NK.CFTLib.ArtinReciprocityIdeal.DvdPrime 𝔪 p := fun p hp hmem =>
    (hsmem p).mp hp (hcop p hmem)
  have key : ∀ p : NK.Chebotarev.PrimeIdeal K,
      ¬ NK.CFTLib.ArtinReciprocityIdeal.DvdPrime 𝔪 p →
      NK.Chebotarev.frobAtPrime (K := K) (L := L₂) p
        = NK.NUV2.ARL.SC.conjHom e (NK.Chebotarev.frobAtPrime (K := K) (L := L₁) p) := by
    intro p hpm
    exact NK.NUV2.ARL.SC.frobAtPrime_conjHom e hc₁ p (fun P hP => by
      by_contra hne
      exact hpm (hram p fun h => hne (h P hP)))
  have hprime₁ : ∀ p : NK.Chebotarev.PrimeIdeal K,
      NK.CFTLib.ArtinReciprocityIdeal.artinSymFracHom (K := K) (L := L₁) hc₁
          (NK.CFTLib.ARL.primeUnit p : NK.CFTLib.ArtinReciprocityIdeal.Frac K)
        = NK.Chebotarev.frobAtPrime (K := K) (L := L₁) p := by
    intro p
    rw [NK.CFTLib.ArtinReciprocityIdeal.artinSymFracHom_apply,
      NK.CFTLib.ARL.primeUnit_val]
    exact NK.CFTLib.Arl.artinSym_prime (K := K) (L := L₁) hc₁ p
  have hprime₂ : ∀ p : NK.Chebotarev.PrimeIdeal K,
      NK.CFTLib.ArtinReciprocityIdeal.artinSymFracHom (K := K) (L := L₂) hc₂
          (NK.CFTLib.ARL.primeUnit p : NK.CFTLib.ArtinReciprocityIdeal.Frac K)
        = NK.Chebotarev.frobAtPrime (K := K) (L := L₂) p := by
    intro p
    rw [NK.CFTLib.ArtinReciprocityIdeal.artinSymFracHom_apply,
      NK.CFTLib.ARL.primeUnit_val]
    exact NK.CFTLib.Arl.artinSym_prime (K := K) (L := L₂) hc₂ p
  have hstep : ∀ p ∈ (NK.CFTLib.Arl.exps A).support,
      NK.CFTLib.ArtinReciprocityIdeal.artinSymFracHom (K := K) (L := L₂) hc₂
          ((NK.CFTLib.ARL.primeUnit p : NK.CFTLib.ArtinReciprocityIdeal.Frac K) ^
            (NK.CFTLib.Arl.exps A p))
        = NK.NUV2.ARL.SC.conjHom e
            (NK.CFTLib.ArtinReciprocityIdeal.artinSymFracHom (K := K) (L := L₁) hc₁
              ((NK.CFTLib.ARL.primeUnit p : NK.CFTLib.ArtinReciprocityIdeal.Frac K) ^
                (NK.CFTLib.Arl.exps A p))) := by
    intro p hp
    rw [map_zpow, map_zpow, hprime₂ p, hprime₁ p, key p (hle p hp), map_zpow]
  rw [hfac]
  rw [← NK.CFTLib.ArtinReciprocityIdeal.artinSymFracHom_apply (K := K) (L := L₂) hc₂
        (∏ p ∈ (NK.CFTLib.Arl.exps A).support,
          (NK.CFTLib.ARL.primeUnit p) ^ (NK.CFTLib.Arl.exps A p)),
    ← NK.CFTLib.ArtinReciprocityIdeal.artinSymFracHom_apply (K := K) (L := L₁) hc₁
        (∏ p ∈ (NK.CFTLib.Arl.exps A).support,
          (NK.CFTLib.ARL.primeUnit p) ^ (NK.CFTLib.Arl.exps A p))]
  calc NK.CFTLib.ArtinReciprocityIdeal.artinSymFracHom (K := K) (L := L₂) hc₂
        (∏ p ∈ (NK.CFTLib.Arl.exps A).support,
          (NK.CFTLib.ARL.primeUnit p) ^ (NK.CFTLib.Arl.exps A p))
      = ∏ p ∈ (NK.CFTLib.Arl.exps A).support,
          NK.CFTLib.ArtinReciprocityIdeal.artinSymFracHom (K := K) (L := L₂) hc₂
            ((NK.CFTLib.ARL.primeUnit p) ^ (NK.CFTLib.Arl.exps A p)) :=
        map_prod (NK.CFTLib.ArtinReciprocityIdeal.artinSymFracHom (K := K) (L := L₂) hc₂) _ _
    _ = ∏ p ∈ (NK.CFTLib.Arl.exps A).support,
          NK.NUV2.ARL.SC.conjHom e
            (NK.CFTLib.ArtinReciprocityIdeal.artinSymFracHom (K := K) (L := L₁) hc₁
              ((NK.CFTLib.ARL.primeUnit p) ^ (NK.CFTLib.Arl.exps A p))) :=
        Finset.prod_congr rfl hstep
    _ = NK.NUV2.ARL.SC.conjHom e
          (∏ p ∈ (NK.CFTLib.Arl.exps A).support,
            NK.CFTLib.ArtinReciprocityIdeal.artinSymFracHom (K := K) (L := L₁) hc₁
              ((NK.CFTLib.ARL.primeUnit p) ^ (NK.CFTLib.Arl.exps A p))) :=
        (map_prod (NK.NUV2.ARL.SC.conjHom e) _ _).symm
    _ = NK.NUV2.ARL.SC.conjHom e
          (NK.CFTLib.ArtinReciprocityIdeal.artinSymFracHom (K := K) (L := L₁) hc₁
            (∏ p ∈ (NK.CFTLib.Arl.exps A).support,
              (NK.CFTLib.ARL.primeUnit p) ^ (NK.CFTLib.Arl.exps A p))) :=
        (congrArg (NK.NUV2.ARL.SC.conjHom e)
          (map_prod (NK.CFTLib.ArtinReciprocityIdeal.artinSymFracHom (K := K) (L := L₁) hc₁)
            _ _)).symm
    _ = NK.NUV2.ARL.SC.conjHom e (NK.CFTLib.Arl.artinSym (K := K) (L := L₁) hc₁
          ((∏ p ∈ (NK.CFTLib.Arl.exps A).support,
            (NK.CFTLib.ARL.primeUnit p) ^ (NK.CFTLib.Arl.exps A p) :
              NK.CFTLib.ArtinReciprocityIdeal.Frac K) :
            FractionalIdeal (NumberField.RingOfIntegers K)⁰ K)) := by
        rw [NK.CFTLib.ArtinReciprocityIdeal.artinSymFracHom_apply]

end Work.SSGRoute.ZDataMup.MupAux
