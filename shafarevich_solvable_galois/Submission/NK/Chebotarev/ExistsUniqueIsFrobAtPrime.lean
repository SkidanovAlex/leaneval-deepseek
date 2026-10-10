import Mathlib.RingTheory.Frobenius
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
import Mathlib.RingTheory.RamificationInertia.Ramification
import Submission.NK.Chebotarev.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.Chebotarev

open IsDedekindDomain

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

/-- **A Frobenius element stabilises its prime.**  If `σ` is a Frobenius element at the prime
`P` of `𝓞 L`, then the induced automorphism of `𝓞 L` preserves `P`. -/
lemma IsFrobAt.map_eq_self {P : PrimeIdeal L} {σ : Gal(L/K)} (h : IsFrobAt P σ) :
    Ideal.map (galRestrict (NumberField.RingOfIntegers K) K L (NumberField.RingOfIntegers L) σ :
      NumberField.RingOfIntegers L →+* NumberField.RingOfIntegers L) P.asIdeal = P.asIdeal := by
  have hprime : P.asIdeal.IsPrime := P.2
  have hcomap : P.asIdeal.comap (galRestrict (NumberField.RingOfIntegers K) K L
      (NumberField.RingOfIntegers L) σ :
        NumberField.RingOfIntegers L →+* NumberField.RingOfIntegers L) = P.asIdeal :=
    AlgHom.IsArithFrobAt.comap_eq h
  have h1 := Ideal.map_comap_of_surjective
    (galRestrict (NumberField.RingOfIntegers K) K L (NumberField.RingOfIntegers L) σ :
      NumberField.RingOfIntegers L →+* NumberField.RingOfIntegers L)
    (galRestrict (NumberField.RingOfIntegers K) K L
      (NumberField.RingOfIntegers L) σ).surjective P.asIdeal
  rw [hcomap] at h1
  exact h1

/-- **The Frobenius at an unramified prime of an abelian extension is well defined.**  Let `L/K`
be a finite abelian Galois extension of number fields and let `p` be a prime of `𝓞 K` which is
unramified in `L`.  Then there is exactly one `σ ∈ Gal(L/K)` which is a Frobenius element at
*some* prime of `𝓞 L` above `p`. -/
theorem ExistsUniqueIsFrobAtPrime {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (hcomm : ∀ a b : Gal(L/K), a * b = b * a) (p : NK.Chebotarev.PrimeIdeal K)
    (hunr : ∀ P : NK.Chebotarev.PrimeIdeal L, P.asIdeal.LiesOver p.asIdeal →
      P.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) = 1) :
    ∃! σ : Gal(L/K), NK.Chebotarev.IsFrobAtPrime (K := K) (L := L) p σ := by
  obtain ⟨σ₀, hσ₀⟩ := exists_isFrobAtPrime (K := K) (L := L) p
  refine ⟨σ₀, hσ₀, ?_⟩
  intro τ hτ
  obtain ⟨P, hP, hPσ₀⟩ := hσ₀
  obtain ⟨Q, hQ, hQτ⟩ := hτ
  exact Commons.NumberTheory.NumberField.frobenius_eq_of_commute p Q P hQ hP
    (hunr Q hQ) (hunr P hP) hcomm (Nat.card (NumberField.RingOfIntegers K ⧸ p.asIdeal))
    τ σ₀ (IsFrobAt.map_eq_self hQτ) (fun x => hQτ.mk_apply hQ x)
    (IsFrobAt.map_eq_self hPσ₀) (fun x => hPσ₀.mk_apply hP x)

end NK.Chebotarev
