import Mathlib
import Submission.Work.SSGRoute.ZDataMup.localGlobalMap_productFormula
import Submission.NK.NUV2.ARL.Gap.isUnramified_cyclotomicExtension
import Submission.NK.CFTLib.ARL.artinReciprocity_cyclotomic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.ZDataMup.ArtinReciprocity

open NumberField IsDedekindDomain
open scoped NumberField

/-- **`Ideal.ramificationIdxIn` and `NK.HeckeL.IsUnramifiedIn` agree.**
If the relative ramification index of `p` is one, then every prime of `𝓞 L` above `p` has
ramification index one over `𝓞 K`: `Ideal.ramificationIdxIn` is (for a Galois extension) the
ramification index of *any* prime above `p`, by `Ideal.ramificationIdxIn_eq_ramificationIdx`. -/
theorem isUnramifiedIn_of_ramificationIdxIn_eq_one {K L : Type} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (h : Ideal.ramificationIdxIn p.asIdeal (NumberField.RingOfIntegers L) = 1) :
    NK.HeckeL.IsUnramifiedIn (K := K) (L := L) p := by
  intro q hq
  haveI : q.asIdeal.IsPrime := q.isPrime
  haveI : q.asIdeal.LiesOver p.asIdeal := hq
  rw [← Ideal.ramificationIdxIn_eq_ramificationIdx (A := NumberField.RingOfIntegers K)
    (B := NumberField.RingOfIntegers L) p.asIdeal q.asIdeal (Gal(L/K))]
  exact h

/-- **The ramification hypothesis at the modulus `n` for a cyclotomic extension.**
Every prime of `𝓞 K` not dividing `(n)` has relative ramification index one in `K(ζ_n) = L`
(`NK.NUV2.ARL.Gap.isUnramified_cyclotomicExtension`, the classical fact that the only primes
ramifying in a cyclotomic extension divide `n`). -/
theorem ramificationIdxIn_eq_one_of_notMem_span_cyclotomic
    {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] (n : ℕ) [NeZero n] [IsCyclotomicExtension {n} K L]
    (p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hp : (n : NumberField.RingOfIntegers K) ∉ p.asIdeal) :
    Ideal.ramificationIdxIn p.asIdeal (NumberField.RingOfIntegers L) = 1 := by
  have hunr := NK.NUV2.ARL.Gap.isUnramified_cyclotomicExtension (k := K) (Ω := L) n p hp
  obtain ⟨P, hP⟩ := NK.Chebotarev.exists_primeIdeal_liesOver (K := K) (L := L) p
  haveI : P.asIdeal.IsPrime := P.isPrime
  haveI : P.asIdeal.LiesOver p.asIdeal := hP
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx (A := NumberField.RingOfIntegers K)
    (B := NumberField.RingOfIntegers L) p.asIdeal P.asIdeal (Gal(L/K))]
  exact hunr P hP

/-- **The cyclotomic base case of the product form of Hilbert reciprocity.**

PROOF INSTRUCTION (important): do NOT prove this by `exact localGlobalMap_productFormula …` — that
would merely import the `sorry` of the general statement and fail an axiom audit.  Descend instead
through the cyclotomic case:
`localGlobalMap_productFormula_of_ramifiedModulus (K := K) (L := L) hcyc n hn hram hsupp2 hprinc`
with `hram` = "primes `∤ (n)` are unramified in `K(ζ_n)/K`"
(`NK.NUV2.ARL.Gap.isUnramified_cyclotomicExtension`) and
`hprinc` = `NK.CFTLib.artinKillsPrincipal K L n`, obtained from
`NK.CFTLib.ARL.artinReciprocity_cyclotomic` (the explicit cyclotomic reciprocity law) through
`NK.CFTLib.ArtinReciprocityIdeal.cyclotomicKernelLe_artinKillsPrincipal` with `n ∣ n`.
Every ingredient is already in the workspace and sorry-free. -/
theorem productFormula_cyclotomic
    {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic (L ≃ₐ[K] L)]
    (n : ℕ) [NeZero n] [IsCyclotomicExtension {n} K L]
    (hsupp2 : ∀ Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      NK.HeckeL.IsUnramifiedIn (K := K) (L := L) Q →
      (n : NumberField.RingOfIntegers K) ∉ Q.asIdeal) :
    ∃ Φ : NK.GlobalCFT.Idele K →* (L ≃ₐ[K] L),
      (∀ a : Kˣ, Φ (NK.GlobalCFT.Idele.principalIdele K a) = 1) ∧
      (∀ y : NK.GlobalCFT.Idele L, Φ (NK.GlobalCFT.Idele.normIdeleHom K L y) = 1) ∧
      (∀ Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
        NK.HeckeL.IsUnramifiedIn (K := K) (L := L) Q →
        Φ (NK.HeckeL.ideleOfPrime K Q) = NK.Chebotarev.frobAtPrime (K := K) (L := L) Q) := by
  -- The ideal-theoretic reciprocity law at the modulus `n`: since `L = K(ζ_n)` is itself the
  -- cyclotomic extension, this is *verbatim* the explicit cyclotomic reciprocity law
  -- `NK.CFTLib.ARL.artinReciprocity_cyclotomic` (the subextension version
  -- `NK.CFTLib.ArtinReciprocityIdeal.cyclotomicKernelLe_artinKillsPrincipal` is the specialisation
  -- of it to an intermediate field, which is not needed when `M = ⊤`).
  have hprinc : NK.CFTLib.artinKillsPrincipal K L n := fun a ha hpos s e σ hs hfac hσ =>
    NK.CFTLib.ARL.artinReciprocity_cyclotomic K L n a ha hpos s e σ hs hfac hσ
  -- Every prime not dividing `(n)` is unramified in `K(ζ_n)/K`.
  have hram : ∀ p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      (n : NumberField.RingOfIntegers K) ∉ p.asIdeal →
      Ideal.ramificationIdxIn p.asIdeal (NumberField.RingOfIntegers L) = 1 :=
    fun p hp => ramificationIdxIn_eq_one_of_notMem_span_cyclotomic (K := K) (L := L) n p hp
  -- The support hypothesis, in the `ramificationIdxIn = 1` form used by the descent.
  have hsupp2' : ∀ Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      Ideal.ramificationIdxIn Q.asIdeal (NumberField.RingOfIntegers L) = 1 →
      (n : NumberField.RingOfIntegers K) ∉ Q.asIdeal := fun Q hQ =>
    hsupp2 Q (isUnramifiedIn_of_ramificationIdxIn_eq_one (K := K) (L := L) Q hQ)
  exact Work.SSGRoute.ZDataMup.localGlobalMap_productFormula_of_ramifiedModulus (K := K) (L := L)
    (inferInstance : IsCyclic (L ≃ₐ[K] L)) n (Nat.pos_of_ne_zero (NeZero.ne n)) hram hsupp2' hprinc

end Work.SSGRoute.ZDataMup.ArtinReciprocity
