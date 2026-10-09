import Mathlib
import Submission.NK.CFTLib.ArtinReciprocityIdeal.Basic
import Submission.NK.CFTLib.ArtinReciprocityIdeal.Conductor
import Submission.NK.CFTLib.ArtinReciprocityIdeal.AbelianReduction
import Submission.NK.Chebotarev.exists_restrictNormalHom_eq_and_isFrobAtPrime
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The cyclotomic case of the Artin reciprocity law, for subextensions

Lang, *Algebraic Number Theory*, Ch. X §1: if `K' = k(ζ_n)` is a cyclotomic extension of the
number field `k` and `k ⊆ K ⊆ K'` with `K/k` finite (hence abelian), then the ideal-theoretic
Artin symbol kills the principal ideals `(a)` with `a ≡ 1 mod c` and `a` totally positive, for a
modulus `c` divisible by `n` (here `c = n · N(𝔡_{K/k})`).

The proof is the consistency of the Artin symbol: an Artin symbol in the subextension `K/k` is the
restriction of the corresponding one in `K'/k` (`NK.Chebotarev.exists_restrictNormalHom_eq_and_isFrobAtPrime`
lifts a Frobenius element), where it is `1` by the cyclotomic base case for `K'/k`.

The base case itself (for `K' = k(ζ_n)`, the modulus `n`) is
`NK.CFTLib.ARL.artinReciprocity_cyclotomic`; here it is taken as a hypothesis so that this
reduction is independent of it.
-/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

namespace NK.CFTLib

open NK.Chebotarev
open NumberField
open scoped NumberField

variable {k K' : Type} [Field k] [NumberField k] [Field K'] [NumberField K'] [Algebra k K']
  [FiniteDimensional k K'] [IsGalois k K']

/-- **Unramifiedness from a modulus divisible by the norm of the different**: a prime `P` of an
extension `K/k` of number fields over a prime `p ∤ N(𝔡_{K/k})` is unramified over `k`. -/
theorem ramificationIdx_eq_one_of_absNorm_differentIdeal_notMem {L : Type*} [Field L]
    [NumberField L] [Algebra k L] [FiniteDimensional k L]
    (p : PrimeIdeal k) (P : PrimeIdeal L) (hP : P.asIdeal.LiesOver p.asIdeal)
    (h : ((Ideal.absNorm (differentIdeal (𝓞 k) (𝓞 L)) : ℕ) : 𝓞 k) ∉ p.asIdeal) :
    P.asIdeal.ramificationIdx (𝓞 k) = 1 := by
  classical
  haveI : P.asIdeal.LiesOver p.asIdeal := hP
  by_contra hne
  have hdvd : P.asIdeal ∣ differentIdeal (𝓞 k) (𝓞 L) := by
    by_contra hnd
    exact hne
      ((Commons.NumberTheory.NumberField.ramificationIdx_one_iff_not_dvd_differentIdeal
        (E := k) (K := L) P.asIdeal P.2).mp hnd)
  have hmem : ((Ideal.absNorm (differentIdeal (𝓞 k) (𝓞 L)) : ℕ) : 𝓞 L) ∈ P.asIdeal :=
    Ideal.dvd_iff_le.mp hdvd (Ideal.absNorm_mem _)
  have hmemK : ((Ideal.absNorm (differentIdeal (𝓞 k) (𝓞 L)) : ℕ) : 𝓞 k) ∈ p.asIdeal := by
    rw [hP.over, Ideal.mem_comap]
    simpa using hmem
  exact h hmemK

/-- **The cyclotomic case for subextensions.**  If the cyclotomic base case holds for the
extension `k(ζ_n)/k` (modulus `n`), then it holds for every intermediate field `K` with `K/k`
finite, with modulus `n · N(𝔡_{K/k})`. -/
theorem artinKillsPrincipal_of_le_isCyclotomicExtension {n : ℕ} [NeZero n]
    [IsCyclotomicExtension {n} k K']
    (hbase : artinKillsPrincipal k K' n)
    (K : IntermediateField k K') [FiniteDimensional k K] [NumberField ↥K] [Normal k K] :
    artinKillsPrincipal k ↥K (n * Ideal.absNorm (differentIdeal (𝓞 k) (𝓞 ↥K))) := by
  haveI hab : IsAbelianGalois k K' := IsCyclotomicExtension.isAbelianGalois {n} k K'
  haveI habK : IsAbelianGalois k ↥K := inferInstance
  intro a ha hpos s e σ hs hfac hfrob
  -- the modulus is a multiple of `n`
  have hbase' := hbase.mono (dvd_mul_right n
    (Ideal.absNorm (differentIdeal (𝓞 k) (𝓞 ↥K))))
  -- primes coprime to the modulus are unramified in `K`
  have hunr : ∀ p ∈ s, ∀ P : PrimeIdeal ↥K, P.asIdeal.LiesOver p.asIdeal →
      P.asIdeal.ramificationIdx (𝓞 k) = 1 := by
    intro p hp P hP
    refine ramificationIdx_eq_one_of_absNorm_differentIdeal_notMem p P hP ?_
    intro hmem
    refine hs p hp ?_
    rw [Nat.cast_mul]
    exact p.asIdeal.mul_mem_left _ hmem
  -- a Frobenius element of `K'/k` at every prime, and its restriction to `K`
  let τ : PrimeIdeal k → Gal(K'/k) := fun p =>
    Classical.choose (exists_isFrobAtPrime (K := k) (L := K') p)
  have hτ : ∀ p : PrimeIdeal k, IsFrobAtPrime (K := k) (L := K') p (τ p) := fun p =>
    Classical.choose_spec (exists_isFrobAtPrime (K := k) (L := K') p)
  have hres_p : ∀ p ∈ s, AlgEquiv.restrictNormalHom (F := k) (K₁ := K') K (τ p) = σ p := by
    intro p hp
    obtain ⟨ρ, hρ, huniq⟩ :=
      NK.Chebotarev.ExistsUniqueIsFrobAtPrime (K := k) (L := ↥K)
        (fun x y => IsMulCommutative.is_comm.comm x y) p (hunr p hp)
    rw [huniq _ (exists_isFrobAtPrime_restrict (K := k) (L := K') K (hτ p)),
      huniq _ (hfrob p hp)]
  -- the cyclotomic base case applies to `K'/k`
  have hbase'' : (s.toList.map (fun p => τ p ^ e p)).prod = 1 :=
    hbase' a ha hpos s e τ hs hfac (fun p hp => hτ p)
  -- restriction of the product
  have hres : AlgEquiv.restrictNormalHom (F := k) (K₁ := K') K
        (s.toList.map (fun p => τ p ^ e p)).prod
      = (s.toList.map (fun p => σ p ^ e p)).prod := by
    rw [map_list_prod, List.map_map]
    congr 1
    exact List.map_congr_left fun p hp => by
      rw [Function.comp_apply, map_pow, hres_p p (Finset.mem_toList.mp hp)]
  rw [← hres, hbase'', map_one]

end NK.CFTLib
