import Mathlib.RingTheory.Ideal.Norm.RelNorm
import Submission.Work.SSGRoute.ZDataMup.ArtinReciprocity.IdealModulus.artinSym_relNorm_prime_eq_one
import Submission.Work.SSGRoute.ZDataMup.ArtinReciprocity.IdealModulus.isUnramified_of_fracCoprimeId
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open scoped NumberField nonZeroDivisors
open NumberField IsDedekindDomain

noncomputable section

namespace Work.SSGRoute.ZDataMup.ArtinReciprocity.IdealModulus

/-- **The Artin symbol of the relative norm of an ideal with unramified primes is trivial.**

If every prime `𝔮` of `𝓞 L` occurring in the ideal `I ≠ 0` is unramified over `K` (in the sense
that the prime `𝔮 ∩ 𝓞 K` below it is unramified), then the Artin symbol of the relative norm
`N_{L/K} I` is `1`.  The proof is an induction on the factorisation of `I`, using the multiplicativity
of `artinSym` and, at a prime `𝔮`, the computation `N 𝔮 = 𝔭 ^ f(𝔮|𝔭)` with `𝔭 = 𝔮 ∩ 𝓞 K`
together with the fact that the Frobenius at an unramified prime has order the inertia degree. -/
theorem artinSymFrac_relNorm_eq_one_of_unramified
    {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsMulCommutative (L ≃ₐ[K] L)]
    (hcomm : ∀ a b : L ≃ₐ[K] L, a * b = b * a) (I : Ideal (𝓞 L))
    (hunr : ∀ 𝔮 : NK.Chebotarev.PrimeIdeal L,
      FractionalIdeal.count L 𝔮 (I : FractionalIdeal (nonZeroDivisors (𝓞 L)) L) ≠ 0 →
      NK.CFTLib.ArtinReciprocityIdeal.IsUnramified (K := K) (L := L) (𝔮.under (𝓞 K))) :
    NK.CFTLib.Arl.artinSym (K := K) (L := L) hcomm
      ((Ideal.relNorm (𝓞 K) I : Ideal (𝓞 K)) :
        FractionalIdeal (nonZeroDivisors (𝓞 K)) K) = 1 := by
  classical
  refine (UniqueFactorizationMonoid.induction_on_prime (P := fun I : Ideal (𝓞 L) =>
      (∀ 𝔮 : NK.Chebotarev.PrimeIdeal L,
        FractionalIdeal.count L 𝔮 (I : FractionalIdeal (nonZeroDivisors (𝓞 L)) L) ≠ 0 →
        NK.CFTLib.ArtinReciprocityIdeal.IsUnramified (K := K) (L := L) (𝔮.under (𝓞 K))) →
      NK.CFTLib.Arl.artinSym (K := K) (L := L) hcomm
        ((Ideal.relNorm (𝓞 K) I : Ideal (𝓞 K)) :
          FractionalIdeal (nonZeroDivisors (𝓞 K)) K) = 1)
    I ?_ ?_ ?_) hunr
  · intro _
    rw [Ideal.zero_eq_bot, Ideal.relNorm_bot, FractionalIdeal.coeIdeal_bot]
    exact NK.CFTLib.ArtinReciprocityIdeal.artinSymFrac_zero hcomm
  · intro x hx _
    rw [Ideal.isUnit_iff.mp hx, Ideal.relNorm_top, FractionalIdeal.coeIdeal_top]
    exact NK.CFTLib.Arl.artinSym_one (K := K) (L := L) hcomm
  · intro a p ha hpprime iha hunr'
    have ha_bot : a ≠ ⊥ := fun h => ha (h.trans Ideal.zero_eq_bot.symm)
    have hp0 : p ≠ ⊥ := fun h => hpprime.ne_zero (h.trans Ideal.zero_eq_bot.symm)
    have hpIsPrime : p.IsPrime := (Ideal.prime_iff_isPrime hp0).mp hpprime
    let 𝔭 : NK.Chebotarev.PrimeIdeal L := ⟨p, hpIsPrime, hp0⟩
    have h𝔭 : 𝔭.asIdeal = p := rfl
    have hmul_qa : ∀ 𝔮 : NK.Chebotarev.PrimeIdeal L, FractionalIdeal.count L 𝔮
        (((p * a : Ideal (𝓞 L)) : FractionalIdeal (nonZeroDivisors (𝓞 L)) L))
        = FractionalIdeal.count L 𝔮 ((p : Ideal (𝓞 L)) :
            FractionalIdeal (nonZeroDivisors (𝓞 L)) L)
          + FractionalIdeal.count L 𝔮 ((a : Ideal (𝓞 L)) :
            FractionalIdeal (nonZeroDivisors (𝓞 L)) L) := by
      intro 𝔮
      rw [FractionalIdeal.coeIdeal_mul, FractionalIdeal.count_mul L 𝔮
        (FractionalIdeal.coeIdeal_ne_zero.mpr hp0) (FractionalIdeal.coeIdeal_ne_zero.mpr ha_bot)]
    have hunr_a : ∀ 𝔮 : NK.Chebotarev.PrimeIdeal L,
        FractionalIdeal.count L 𝔮 (a : FractionalIdeal (nonZeroDivisors (𝓞 L)) L) ≠ 0 →
        NK.CFTLib.ArtinReciprocityIdeal.IsUnramified (K := K) (L := L) (𝔮.under (𝓞 K)) := by
      intro 𝔮 h𝔮
      refine hunr' 𝔮 ?_
      rw [hmul_qa 𝔮]
      have h3 := FractionalIdeal.count_coe_nonneg L 𝔮 p
      have h4 := FractionalIdeal.count_coe_nonneg L 𝔮 a
      omega
    have hunr_p : NK.CFTLib.ArtinReciprocityIdeal.IsUnramified (K := K) (L := L)
        (𝔭.under (𝓞 K)) := by
      refine hunr' 𝔭 ?_
      have hcount_p : FractionalIdeal.count L 𝔭 ((p : Ideal (𝓞 L)) :
          FractionalIdeal (nonZeroDivisors (𝓞 L)) L) = 1 := by
        rw [← h𝔭]
        exact FractionalIdeal.count_self L 𝔭
      rw [hmul_qa 𝔭, hcount_p]
      have h4 := FractionalIdeal.count_coe_nonneg L 𝔭 a
      omega
    have hnp : ((Ideal.relNorm (𝓞 K) p : Ideal (𝓞 K)) :
        FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ≠ 0 :=
      FractionalIdeal.coeIdeal_ne_zero.mpr (fun h => hp0 ((Ideal.relNorm_eq_bot_iff).mp h))
    have hna : ((Ideal.relNorm (𝓞 K) a : Ideal (𝓞 K)) :
        FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ≠ 0 :=
      FractionalIdeal.coeIdeal_ne_zero.mpr (fun h => ha_bot ((Ideal.relNorm_eq_bot_iff).mp h))
    rw [map_mul (Ideal.relNorm (𝓞 K)) p a, FractionalIdeal.coeIdeal_mul,
        NK.CFTLib.Arl.artinSym_mul (K := K) (L := L) hcomm hnp hna, iha hunr_a, mul_one]
    exact artinSym_relNorm_prime_eq_one hcomm 𝔭 hunr_p

/-- **The Artin symbol kills the norm group `𝔑(𝔪)` of an ideal modulus** (Lang X.2, property A4):
for a finite abelian Galois extension `L / K` of number fields and an ideal modulus `𝔪 ≠ ⊥` whose
support contains all the ramified primes, the symbol of every fractional ideal in `𝔑(𝔪)` is `1`.
The norm ray is generated by the relative norms `N_{L/K} I` of the ideals `I ≠ 0` of `𝓞 L` coprime
to `𝔪 𝓞 L`; each such generator is killed by `artinSymFrac_relNorm_eq_one_of_unramified`, the
hypotheses of which are supplied by `isUnramified_of_fracCoprimeId` (coprimality plus
`ContainsRamified` forces the primes of `I` to be unramified) and by `ContainsRamified` itself. -/
theorem normKerId (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsMulCommutative (L ≃ₐ[K] L)]
    (𝔪 : Ideal (NumberField.RingOfIntegers K)) (h𝔪 : 𝔪 ≠ ⊥)
    (hram : NK.CFTLib.ArtinReciprocityIdeal.ContainsRamified (K := K) (L := L) 𝔪) :
    ∀ A : NK.CFTLib.ArtinReciprocityIdeal.Frac K,
      A ∈ NK.CFTLib.ArtinReciprocityIdeal.normRayId (K := K) (L := L) 𝔪 →
      NK.CFTLib.Arl.artinSym (K := K) (L := L)
        (fun a b : L ≃ₐ[K] L => IsMulCommutative.is_comm.comm a b) A = 1 := by
  intro A hA
  let hcomm : ∀ a b : Gal(L/K), a * b = b * a := fun a b => IsMulCommutative.is_comm.comm a b
  let f : NK.CFTLib.ArtinReciprocityIdeal.Frac K →* Gal(L/K) :=
    NK.CFTLib.ArtinReciprocityIdeal.artinSymFracHom (K := K) (L := L) hcomm
  have hle : NK.CFTLib.ArtinReciprocityIdeal.normRayId (K := K) (L := L) 𝔪 ≤ f.ker := by
    rw [show NK.CFTLib.ArtinReciprocityIdeal.normRayId (K := K) (L := L) 𝔪 =
        Subgroup.closure {A : NK.CFTLib.ArtinReciprocityIdeal.Frac K |
          ∃ (I : Ideal (𝓞 L)) (hI : I ≠ ⊥),
            NK.CFTLib.ArtinReciprocityIdeal.FracCoprimeId (K := L)
              (Ideal.map (algebraMap (𝓞 K) (𝓞 L)) 𝔪)
              (NK.CFTLib.ArtinReciprocityIdeal.idealUnit I hI) ∧
            A = NK.CFTLib.ArtinReciprocityIdeal.idealUnit (Ideal.relNorm (𝓞 K) I)
                  (fun h => hI ((Ideal.relNorm_eq_bot_iff).mp h))} from rfl]
    rw [Subgroup.closure_le]
    rintro A ⟨I, hI, hcop, rfl⟩
    show NK.CFTLib.Arl.artinSym hcomm
      ((Ideal.relNorm (𝓞 K) I : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) = 1
    exact artinSymFrac_relNorm_eq_one_of_unramified hcomm I
      (fun 𝔮 h𝔮 => isUnramified_of_fracCoprimeId 𝔪 hram I hI hcop 𝔮 h𝔮)
  exact hle hA

end Work.SSGRoute.ZDataMup.ArtinReciprocity.IdealModulus
