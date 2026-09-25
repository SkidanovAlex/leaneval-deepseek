import Mathlib
import Submission.NK.CFTLib.ArtinIdeal
import Submission.NK.CFTLib.ArtinReciprocityIdeal.Basic

/-!
# Conductors for the ideal-theoretic Artin symbol

`NK.CFTLib.artinConductor K L m` is the property of the natural number `m` which the target
theorem `NK.CFTLib.ArtinReciprocityIdeal` asks for: `m > 0`, every prime `p ∤ m` is unramified
in `L`, and for every totally positive `a ∈ 𝓞 K` with `a ≡ 1 mod m` the product of Frobenius
elements over any factorisation of `(a)` into primes `∤ m` is `1`.

The target is `∀ K L (abelian), ∃ m, artinConductor K L m`.

The property is monotone in `m` (`artinConductor.mono`), and the abelian case is reduced to the
cyclic quotients in `artinConductor_of_cyclic_quotients`.
-/

namespace NK.CFTLib

open NK.Chebotarev
open NumberField
open scoped NumberField

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

/-- **The product condition of a conductor.**  The Artin symbol kills every principal ideal `(a)`
with `a ≡ 1 mod m` and `a` totally positive, for any choice of Frobenius elements at the primes of
a factorisation of `(a)` into primes prime to `m`.

This is the part of the reciprocity law that the cyclotomic case of the theory supplies directly
(`NK.CFTLib.ARL.artinReciprocity_cyclotomic`, which is exactly this statement for
`L = K(ζ_m)`); the ramification condition is added separately in `artinConductor`. -/
def artinKillsPrincipal (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L] (m : ℕ) : Prop :=
  ∀ (a : 𝓞 K), a - 1 ∈ Ideal.span {(m : 𝓞 K)} → (∀ φ : K →+* ℝ, 0 < φ (a : K)) →
    ∀ (s : Finset (PrimeIdeal K)) (e : PrimeIdeal K → ℕ) (σ : PrimeIdeal K → Gal(L/K)),
      (∀ p ∈ s, (m : 𝓞 K) ∉ p.asIdeal) →
      Ideal.span {a} = ∏ p ∈ s, p.asIdeal ^ e p →
      (∀ p ∈ s, IsFrobAtPrime (K := K) (L := L) p (σ p)) →
      (s.toList.map (fun p => σ p ^ e p)).prod = 1

/-- **`m` is a conductor for the ideal-theoretic Artin symbol of `L/K`.**  This is the property
asked for by `NK.CFTLib.ArtinReciprocityIdeal`: `m > 0`, every prime not dividing `(m)` is
unramified in `L`, and `m` satisfies the product condition `artinKillsPrincipal`. -/
def artinConductor (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L] (m : ℕ) : Prop :=
  0 < m ∧
  (∀ p : PrimeIdeal K, (m : 𝓞 K) ∉ p.asIdeal →
    Ideal.ramificationIdxIn p.asIdeal (𝓞 L) = 1) ∧
  artinKillsPrincipal K L m

/-- Unfolding `artinConductor`. -/
theorem artinConductor_iff {m : ℕ} :
    artinConductor K L m ↔ 0 < m ∧
      (∀ p : PrimeIdeal K, (m : 𝓞 K) ∉ p.asIdeal →
        Ideal.ramificationIdxIn p.asIdeal (𝓞 L) = 1) ∧
      artinKillsPrincipal K L m := Iff.rfl

/-- **The product condition is monotone in the modulus.**  If `m ∣ m'` then `(m') ⊆ (m)`, so the
primes occurring in a factorisation coprime to `m'` are coprime to `m`. -/
theorem artinKillsPrincipal.mono {m m' : ℕ} (h : artinKillsPrincipal K L m) (hmm : m ∣ m') :
    artinKillsPrincipal K L m' := by
  have hdvd : (m : 𝓞 K) ∣ (m' : 𝓞 K) := by
    obtain ⟨c, rfl⟩ := hmm
    exact ⟨(c : 𝓞 K), by push_cast; ring⟩
  have hspan : Ideal.span {(m' : 𝓞 K)} ≤ Ideal.span {(m : 𝓞 K)} :=
    Ideal.span_singleton_le_span_singleton.mpr hdvd
  have hprime : ∀ p : PrimeIdeal K, (m' : 𝓞 K) ∉ p.asIdeal → (m : 𝓞 K) ∉ p.asIdeal := by
    intro p hp hm_p
    apply hp
    obtain ⟨c, rfl⟩ := hmm
    push_cast
    exact p.asIdeal.mul_mem_right _ hm_p
  intro a ha hpos s e σ hs hfac hσ
  exact h a (hspan ha) hpos s e σ (fun p hp => hprime p (hs p hp)) hfac hσ

/-- **The target theorem from the existence of conductors.** -/
theorem artinReciprocityIdeal_of_forall_exists_artinConductor
    (h : ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
      [FiniteDimensional K L] [IsGalois K L], (∀ a b : Gal(L/K), a * b = b * a) →
      ∃ m : ℕ, artinConductor K L m) :
    ArtinReciprocityIdeal := by
  intro K L _ _ _ _ _ _ _ hcomm
  exact h K L hcomm

/-- **A conductor for `L/K` is a conductor for every multiple.**  Indeed `(m') ⊆ (m)` when
`m ∣ m'`, and a prime dividing `(m)` divides `(m')`. -/
theorem artinConductor.mono {m m' : ℕ} (h : artinConductor K L m) (hmm : m ∣ m')
    (hm' : 0 < m') : artinConductor K L m' := by
  obtain ⟨hm, hram, hprod⟩ := h
  -- `(m') ⊆ (m)`, so `a - 1 ∈ (m')` implies `a - 1 ∈ (m)`
  have hdvd : (m : 𝓞 K) ∣ (m' : 𝓞 K) := by
    obtain ⟨c, rfl⟩ := hmm
    exact ⟨(c : 𝓞 K), by push_cast; ring⟩
  have hspan : Ideal.span {(m' : 𝓞 K)} ≤ Ideal.span {(m : 𝓞 K)} :=
    Ideal.span_singleton_le_span_singleton.mpr hdvd
  -- a prime containing `m` contains `m'`
  have hprime : ∀ p : PrimeIdeal K, (m' : 𝓞 K) ∉ p.asIdeal → (m : 𝓞 K) ∉ p.asIdeal := by
    intro p hp hm_p
    apply hp
    obtain ⟨c, rfl⟩ := hmm
    push_cast
    exact p.asIdeal.mul_mem_right _ hm_p
  refine ⟨hm', fun p hp => hram p (hprime p hp), ?_⟩
  intro a ha hpos s e σ hs hfac hσ
  exact hprod a (hspan ha) hpos s e σ (fun p hp => hprime p (hs p hp)) hfac hσ

end NK.CFTLib
