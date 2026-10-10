import Mathlib.RingTheory.Frobenius
import Mathlib.RingTheory.Henselian
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
import Mathlib.RingTheory.RamificationInertia.Ramification
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Commons.NumberTheory.NumberField.exists_frobenius_galRestrict
import Submission.Commons.NumberTheory.NumberField.orderOf_frobenius_eq_inertiaDeg
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Frobenius elements at primes of a number field

This file sets up the vocabulary of the Čebotarev density theorem: for a finite Galois
extension `L/K` of number fields, a prime `P` of `𝓞 L` and an element `σ : Gal(L/K)`, the
predicate `NK.Chebotarev.IsFrobAt P σ` says that `σ` is an arithmetic Frobenius at `P`, i.e.
that `σ x ≡ x ^ #(𝓞 K / P.under) (mod P)` for all `x ∈ 𝓞 L`.

The basic API proved here:

* `IsFrobAt.mk_apply` — the residue field form, with the exponent `#(𝓞 K / p) = N p`;
* `IsFrobAt.eq_of_isFrobAt` — when `P` is unramified over `p`, the Frobenius at `P` is unique;
* `exists_isFrobAt` — a Frobenius at `P` always exists.

The remaining API (`stabilizes`, `mul_inv_mem_inertia`, `conj`, `apply_of_pow_eq_one`,
`orderOf_eq_inertiaDeg`, `eq_one_iff`, and the abelian "Frobenius at a prime of `K`") is in the
companion files `Work/Chebotarev/Frobenius*.lean`.
-/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

namespace NK.Chebotarev

open IsDedekindDomain
open scoped Pointwise

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L]

/-- A nonzero prime ideal of `𝓞 K`, i.e. a finite place of the number field `K`. -/
abbrev PrimeIdeal (K : Type*) [Field K] [NumberField K] :=
  IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)

/-- **A Frobenius element at a prime.**  For a finite Galois extension `L/K` of number fields and
a nonzero prime `P` of `𝓞 L`, an element `σ : Gal(L/K)` is a Frobenius at `P` if
`σ x ≡ x ^ #(𝓞 K / P ∩ 𝓞 K) (mod P)` for every `x ∈ 𝓞 L`. -/
def IsFrobAt (P : PrimeIdeal L) (σ : Gal(L/K)) : Prop :=
  (galRestrict (NumberField.RingOfIntegers K) K L (NumberField.RingOfIntegers L) σ).toAlgHom
    |>.IsArithFrobAt P.asIdeal

lemma isFrobAt_def (P : PrimeIdeal L) (σ : Gal(L/K)) :
    IsFrobAt P σ ↔ ∀ x : NumberField.RingOfIntegers L,
      galRestrict (NumberField.RingOfIntegers K) K L (NumberField.RingOfIntegers L) σ x
        - x ^ Nat.card (NumberField.RingOfIntegers K ⧸ P.asIdeal.under
            (NumberField.RingOfIntegers K)) ∈ P.asIdeal :=
  Iff.rfl

variable {p : PrimeIdeal K} {P : PrimeIdeal L} {σ τ : Gal(L/K)}

/-- The residue-field form of the definition of a Frobenius element, for `P` lying over `p`. -/
lemma IsFrobAt.mk_apply (h : IsFrobAt P σ) (hP : P.asIdeal.LiesOver p.asIdeal)
    (x : NumberField.RingOfIntegers L) :
    Ideal.Quotient.mk P.asIdeal
        (galRestrict (NumberField.RingOfIntegers K) K L (NumberField.RingOfIntegers L) σ x) =
      (Ideal.Quotient.mk P.asIdeal x) ^ Nat.card (NumberField.RingOfIntegers K ⧸ p.asIdeal) := by
  have h' := AlgHom.IsArithFrobAt.mk_apply h x
  rw [show Nat.card (NumberField.RingOfIntegers K ⧸ p.asIdeal) =
      Nat.card (NumberField.RingOfIntegers K ⧸ P.asIdeal.under (NumberField.RingOfIntegers K))
      from by rw [hP.over]]
  exact h'

section Galois

variable [IsGalois K L]

/-- **Uniqueness of the Frobenius at an unramified prime.** -/
theorem IsFrobAt.eq_of_isFrobAt (hP : P.asIdeal.LiesOver p.asIdeal)
    (he : P.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) = 1)
    (h : IsFrobAt P σ) (h' : IsFrobAt P τ) : σ = τ :=
  Commons.NumberTheory.NumberField.FrobeniusEqOfCommute.eq_of_residue_mk_eq p P hP he σ τ
    (fun x => by rw [h.mk_apply hP x, h'.mk_apply hP x])

/-- **A Frobenius element at any prime exists.** -/
theorem exists_isFrobAt (p : PrimeIdeal K) (P : PrimeIdeal L)
    (hP : P.asIdeal.LiesOver p.asIdeal) : ∃ σ : Gal(L/K), IsFrobAt P σ := by
  obtain ⟨σ, -, hσ⟩ :=
    Commons.NumberTheory.NumberField.exists_frobenius_galRestrict p P hP
  refine ⟨σ, fun x => Ideal.Quotient.eq_zero_iff_mem.mp ?_⟩
  rw [map_sub, map_pow]
  have h := hσ x
  rw [show Nat.card (NumberField.RingOfIntegers K ⧸ p.asIdeal) =
      Nat.card (NumberField.RingOfIntegers K ⧸ P.asIdeal.under (NumberField.RingOfIntegers K))
      from by rw [hP.over]] at h
  exact sub_eq_zero.mpr h

end Galois


/-- **The Frobenius at a prime of the base field.**  `σ` is a Frobenius at `p` if some prime `P`
of `𝓞 L` above `p` realises `σ` as a Frobenius element.  For an abelian extension and an
unramified `p`, there is exactly one such `σ` (`NK.Chebotarev.existsUnique_isFrobAtPrime`). -/
def IsFrobAtPrime (p : PrimeIdeal K) (σ : Gal(L/K)) : Prop :=
  ∃ P : PrimeIdeal L, P.asIdeal.LiesOver p.asIdeal ∧ IsFrobAt P σ

lemma isFrobAtPrime_iff (p : PrimeIdeal K) (σ : Gal(L/K)) :
    IsFrobAtPrime (K := K) p σ ↔
      ∃ P : PrimeIdeal L, P.asIdeal.LiesOver p.asIdeal ∧ IsFrobAt P σ :=
  Iff.rfl

section Galois

variable [IsGalois K L]

/-- A prime of `L` above any prime of `K` exists. -/
theorem exists_primeIdeal_liesOver (p : PrimeIdeal K) :
    ∃ P : PrimeIdeal L, P.asIdeal.LiesOver p.asIdeal := by
  obtain ⟨P⟩ := (inferInstance : Nonempty (p.asIdeal.primesOver
    (NumberField.RingOfIntegers L)))
  exact ⟨⟨P.1, P.2.1, Ideal.ne_bot_of_mem_primesOver p.ne_bot P.2⟩, P.2.2⟩

/-- Some Frobenius element at any prescribed prime `p` of `K` exists. -/
theorem exists_isFrobAtPrime (p : PrimeIdeal K) : ∃ σ : Gal(L/K), IsFrobAtPrime p σ := by
  obtain ⟨P, hP⟩ := exists_primeIdeal_liesOver (K := K) (L := L) p
  obtain ⟨σ, hσ⟩ := exists_isFrobAt (K := K) (L := L) p P hP
  exact ⟨σ, P, hP, hσ⟩

end Galois


section SmulAction

variable [IsGalois K L]

/-- **The action of the Galois group on the finite places of `L`**: `τ • P` is the prime
`τ(P) = {τ x : x ∈ P}`. -/
noncomputable instance instSMulPrimeIdeal : SMul Gal(L/K) (PrimeIdeal L) where
  smul τ P :=
    ⟨Ideal.map (galRestrict (NumberField.RingOfIntegers K) K L
        (NumberField.RingOfIntegers L) τ : NumberField.RingOfIntegers L →+*
          NumberField.RingOfIntegers L) P.asIdeal,
      Ideal.map_isPrime_of_equiv _,
      fun h => P.ne_bot ((Ideal.map_eq_bot_iff_of_injective
        (galRestrict (NumberField.RingOfIntegers K) K L
          (NumberField.RingOfIntegers L) τ).injective).mp h)⟩

@[simp]
lemma smul_primeIdeal_asIdeal (τ : Gal(L/K)) (P : PrimeIdeal L) :
    (τ • P).asIdeal = Ideal.map (galRestrict (NumberField.RingOfIntegers K) K L
      (NumberField.RingOfIntegers L) τ : NumberField.RingOfIntegers L →+*
        NumberField.RingOfIntegers L) P.asIdeal := rfl

end SmulAction

end NK.Chebotarev
