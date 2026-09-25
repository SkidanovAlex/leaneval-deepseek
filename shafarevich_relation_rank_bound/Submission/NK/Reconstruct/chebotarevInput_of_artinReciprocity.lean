import Mathlib
import Submission.NK.Reconstruct.Basic
import Submission.NK.Chebotarev.ArtinReciprocity

/-!
# Čebotarev's theorem from Artin reciprocity

The Čebotarev density input `NK.Reconstruct.ChebotarevInput K K'` of the Neukirch–Uchida
reconstruction is the *finite-level* form of Čebotarev's density theorem: for every finite normal
(hence Galois, in characteristic zero) intermediate field `L/K` and every `τ : Gal(L/K)` there is
a prime `p` of the base field `K`, unramified in `L`, and a prime `P` of `𝓞 L` above it at which
`τ` is an arithmetic Frobenius element.

Here it is deduced from the Artin-reciprocity package `NK.Chebotarev.ArtinReciprocityInput` for
every finite Galois level `L`.  That package yields the Dirichlet density of the primes whose
Frobenius element lies in a prescribed conjugacy class
(`NK.Chebotarev.hasDirichletDensity_frobClass_of_artinReciprocity`), namely the density
`|Cl(τ)| / |Gal(L/K)|`, which is non-zero.  Since only finitely many primes of `K` ramify in `L`
(`Commons.NumberTheory.NumberField.finite_setOf_ramificationIdx_ne_one`), infinitely many primes
with Frobenius conjugate to `τ` are unramified.  For such a prime `p`, a Frobenius element `F` at a
prime `Q` above `p` together with a conjugating `c` with `c * F * c⁻¹ = τ` gives the required pair
`(p, c • Q)`: conjugating the prime conjugates the Frobenius
(`NK.Chebotarev.IsFrobAtConj`), and `c • Q` is still unramified over `p` because `p` ramifies in
no prime of `𝓞 L` at all.
-/

set_option linter.style.haveILetI false

namespace NK.Reconstruct

theorem chebotarevInput_of_artinReciprocity {K K' : Type*} [Field K] [NumberField K] [Field K']
    [Algebra K K'] [IsSepClosure K K']
    (h : ∀ (L : IntermediateField K K') [FiniteDimensional K L] [Normal K L] [NumberField ↥L]
      [IsGalois K ↥L], NK.Chebotarev.ArtinReciprocityInput K ↥L) :
    NK.Reconstruct.ChebotarevInput K K' := by
  classical
  intro L _ _ _ τ
  -- In characteristic zero a finite normal extension is Galois.
  haveI hgal : IsGalois K ↥L := Commons.FieldTheory.Galois.isGalois_of_normal_of_charZero
  -- The Artin reciprocity input for this level.
  have hA : NK.Chebotarev.ArtinReciprocityInput K ↥L := h L
  -- Čebotarev: the Frobenius class of `τ` has positive Dirichlet density.
  have hdens :=
    NK.Chebotarev.hasDirichletDensity_frobClass_of_artinReciprocity (K := K) (L := ↥L) hA τ
  let S : Set (NK.Chebotarev.PrimeIdeal K) :=
    {p | IsConj (NK.Chebotarev.frobAtPrime (K := K) (L := ↥L) p) τ}
  have hdensS : NumberField.Set.HasDirichletDensity S
      ((Nat.card {x : Gal(↥L/K) // IsConj x τ} : ℝ) / (Nat.card (Gal(↥L/K)) : ℝ)) := hdens
  have hδpos : (0 : ℝ) < (Nat.card {x : Gal(↥L/K) // IsConj x τ} : ℝ) /
      (Nat.card (Gal(↥L/K)) : ℝ) := by
    haveI : Nonempty {x : Gal(↥L/K) // IsConj x τ} := ⟨τ, IsConj.refl τ⟩
    haveI : Nonempty (Gal(↥L/K)) := ⟨1⟩
    have h1 : (0 : ℝ) < (Nat.card {x : Gal(↥L/K) // IsConj x τ} : ℝ) := by
      exact_mod_cast Nat.card_pos
    have h2 : (0 : ℝ) < (Nat.card (Gal(↥L/K)) : ℝ) := by exact_mod_cast Nat.card_pos
    exact div_pos h1 h2
  have hInf : S.Infinite := NK.Chebotarev.infinite_of_hasDirichletDensity_pos hdensS hδpos
  -- The primes of `K` that ramify in `L` form a finite set.
  let Bad : Set (NK.Chebotarev.PrimeIdeal K) :=
    {p | ∃ P : NK.Chebotarev.PrimeIdeal ↥L, P.asIdeal.LiesOver p.asIdeal ∧
      P.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) ≠ 1}
  have hBadFin : Bad.Finite := by
    have hfin : {q : NK.Chebotarev.PrimeIdeal ↥L |
        q.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) ≠ 1}.Finite :=
      Commons.NumberTheory.NumberField.finite_setOf_ramificationIdx_ne_one
    refine (hfin.image (fun q : NK.Chebotarev.PrimeIdeal ↥L =>
      IsDedekindDomain.HeightOneSpectrum.under (NumberField.RingOfIntegers K) q)).subset ?_
    rintro p ⟨P, hP, heP⟩
    exact ⟨P, heP, IsDedekindDomain.HeightOneSpectrum.ext
      (by rw [IsDedekindDomain.HeightOneSpectrum.under_asIdeal, hP.over])⟩
  -- Infinitely many primes with Frobenius conjugate to `τ` are unramified in `L`.
  obtain ⟨p, hp⟩ := (hInf.sdiff hBadFin).nonempty
  have hpS : IsConj (NK.Chebotarev.frobAtPrime (K := K) (L := ↥L) p) τ := hp.1
  have hpBad : p ∉ Bad := hp.2
  -- The chosen Frobenius element at `p` is a genuine Frobenius element at some prime above `p`.
  have hFrob : NK.Chebotarev.IsFrobAtPrime (K := K) (L := ↥L) p
      (NK.Chebotarev.frobAtPrime (K := K) (L := ↥L) p) := by
    by_cases hne : ∃ σ : Gal(↥L/K), NK.Chebotarev.IsFrobAtPrime (K := K) (L := ↥L) p σ
    · rw [NK.Chebotarev.frobAtPrime, dif_pos hne]
      exact hne.choose_spec
    · rw [NK.Chebotarev.frobAtPrime, dif_neg hne]
      exact absurd (NK.Chebotarev.exists_isFrobAtPrime (K := K) (L := ↥L) p) hne
  obtain ⟨Q, hQlies, hQ⟩ := hFrob
  -- Conjugate the Frobenius: `c * Frob_p * c⁻¹ = τ`.
  obtain ⟨c, hc⟩ := isConj_iff.mp hpS
  have hτ : NK.Chebotarev.IsFrobAt (c • Q) τ := by
    have hconj := NK.Chebotarev.IsFrobAtConj (K := K) (L := ↥L) (τ := c) hQ
    rw [hc] at hconj
    exact hconj
  have hLies : (c • Q).asIdeal.LiesOver p.asIdeal := by
    haveI : Q.asIdeal.LiesOver p.asIdeal := hQlies
    rw [NK.Chebotarev.smul_primeIdeal_asIdeal]
    exact Commons.NumberTheory.NumberField.liesOver_map_galRestrict p Q c
  have heOne : (c • Q).asIdeal.ramificationIdx (NumberField.RingOfIntegers K) = 1 := by
    by_contra hne
    exact hpBad ⟨c • Q, hLies, hne⟩
  exact ⟨p, c • Q, hLies, heOne, hτ⟩

end NK.Reconstruct
