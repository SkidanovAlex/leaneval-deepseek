import Mathlib
import Submission.NK.CFTLib.ArtinIdeal
import Submission.NK.CFTLib.Arl.Defs
import Submission.NK.CFTLib.Arl.artinSym_spanSingleton_eq_one
import Submission.NK.CFTLib.ArtinReciprocityIdeal.Conductor
import Submission.NK.CFTLib.ArtinReciprocityIdeal.artinKillsPrincipal_one_of_unramified
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The Artin symbol of a totally positive principal ideal, for an extension unramified at the
finite primes

Let `L/K` be a finite abelian extension of number fields which is **unramified at every finite
prime** (`differentIdeal (𝓞 K) (𝓞 L) = ⊤`), and assume the ideal-theoretic Artin reciprocity law
`NK.CFTLib.ArtinReciprocityIdeal`.  The main theorem of this file,

`NK.CFTLib.Existence.artinSym_spanSingleton_eq_one_of_totallyPositive_of_isUnramifiedAtFinite`,

states that the Artin symbol of the principal ideal `(b)·𝓞 K` is trivial for every *totally
positive* `b ∈ Kˣ`.

## The mathematical shape of the argument

Since `L/K` is unramified at every finite prime, the ramification condition of the reciprocity law
is vacuous for the *trivial* modulus `m = 1`, so the law at modulus `1` is exactly the statement
that the Artin symbol of every principal ideal with a totally positive generator is trivial (there
is no congruence condition, and the coprimality side condition `(1 : 𝓞 K) ∉ 𝔭.asIdeal` is
automatic because `1` lies in no proper ideal).  This is the "the finite part of the conductor is
`1`" form of the reciprocity law; it is isolated as the hypothesis of the auxiliary lemma

`artinSym_spanSingleton_eq_one_of_artinKillsPrincipal_one`

below, and supplied by the separate module
`Submission/Work/CFTLib/ArtinReciprocityIdeal/artinKillsPrincipal_one_of_unramified.lean` as
`NK.CFTLib.ArtinReciprocityIdeal.artinKillsPrincipal_one_of_unramified` (the unramified case of
the conductor theorem, via the transfer/auxiliary-field argument).

Feeding that instance of the reciprocity law into
`NK.CFTLib.Arl.artinSym_spanSingleton_eq_one` — the general "principal ideal with `b ≡ 1 mod m`
and totally positive" theorem, applied at `m = 1` — gives the claim: at `m = 1` the congruence
hypothesis is vacuous and the ramification hypothesis is the unramifiedness at every finite prime.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open scoped NumberField nonZeroDivisors
open NumberField IsDedekindDomain

noncomputable section

namespace NK.CFTLib.Existence

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

/-- **`differentIdeal = ⊤` makes every prime ramification index `1`.**

The relative different of `L/K` is the unit ideal exactly when no finite prime ramifies; the
statement is recorded here for `Ideal.ramificationIdxIn`, the form in which the reciprocity law
`NK.CFTLib.Arl.artinSym_spanSingleton_eq_one` consumes unramifiedness. -/
lemma ramificationIdxIn_eq_one_of_differentIdeal_eq_top_aux_uchida
    (hunr : differentIdeal (𝓞 K) (𝓞 L) = ⊤) (𝔭 : HeightOneSpectrum (𝓞 K)) :
    Ideal.ramificationIdxIn 𝔭.asIdeal (𝓞 L) = 1 := by
  classical
  letI hMSA : MulSemiringAction (Gal(L/K)) (𝓞 L) :=
    IsIntegralClosure.MulSemiringAction (𝓞 K) K L (𝓞 L)
  haveI hGG : IsGaloisGroup (Gal(L/K)) (𝓞 K) (𝓞 L) :=
    IsGaloisGroup.of_isFractionRing (Gal(L/K)) (𝓞 K) (𝓞 L) K L
  obtain ⟨Q, hQ⟩ := NK.Chebotarev.exists_primeIdeal_liesOver (K := K) (L := L) 𝔭
  haveI : Q.asIdeal.IsPrime := Q.isPrime
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx (A := 𝓞 K) (B := 𝓞 L) 𝔭.asIdeal Q.asIdeal
    (Gal(L/K))]
  rw [← Commons.NumberTheory.NumberField.ramificationIdx_one_iff_not_dvd_differentIdeal
    (E := K) (K := L) Q.asIdeal Q.isPrime]
  rw [Ideal.dvd_iff_le]
  intro hle
  exact Q.isPrime.ne_top (top_le_iff.mp (hunr ▸ hle))

/-- The element `1` of the ring of integers lies in no prime ideal. -/
lemma natCast_one_notMem_primeIdeal_aux_uchida (𝔭 : HeightOneSpectrum (𝓞 K)) :
    ((1 : ℕ) : 𝓞 K) ∉ 𝔭.asIdeal := by
  intro h
  exact 𝔭.isPrime.ne_top (Ideal.eq_top_iff_one _ |>.mpr (by simpa using h))

/-- **The reciprocity law at the trivial modulus.**

If the Artin symbol kills every principal ideal with a totally positive generator
(`NK.CFTLib.artinKillsPrincipal K L 1`, the product condition of the reciprocity law at modulus
`1`), then for an extension unramified at every finite prime the Artin symbol of the fractional
ideal `(b)` is trivial for every totally positive `b ∈ Kˣ`. -/
theorem artinSym_spanSingleton_eq_one_of_artinKillsPrincipal_one
    (hcomm : ∀ a b : Gal(L/K), a * b = b * a)
    (hunr : differentIdeal (𝓞 K) (𝓞 L) = ⊤)
    (hprinc : NK.CFTLib.artinKillsPrincipal K L 1)
    (b : Kˣ)
    (hpos : ∀ (w : NumberField.InfinitePlace K) (hw : w.IsReal),
      0 < (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hw)
        (algebraMap K w.Completion (b : K))) :
    NK.CFTLib.Arl.artinSym (K := K) (L := L) hcomm
      (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers K))
        ((b : Kˣ) : K)) = 1 := by
  refine NK.CFTLib.Arl.artinSym_spanSingleton_eq_one (K := K) (L := L) hcomm 1 (by norm_num)
    ?_ ?_ b ?_ hpos
  · intro 𝔭 _
    exact ramificationIdxIn_eq_one_of_differentIdeal_eq_top_aux_uchida (K := K) (L := L) hunr 𝔭
  · intro a ha hpos' s e σ hs hfac hfrob
    exact hprinc a ha hpos' s e σ hs hfac hfrob
  · intro 𝔭 h𝔭
    exact absurd h𝔭 (natCast_one_notMem_primeIdeal_aux_uchida (K := K) 𝔭)

/-- **The Artin symbol of a totally positive principal ideal is trivial, for an extension
unramified at every finite prime.**

This is the "Frobenius normalisation" statement: it says that the congruence conditions of the
reciprocity law are unnecessary at the primes dividing the modulus when those primes are
unramified — equivalently, that the finite part of the conductor of `L/K` is `1`. -/
theorem artinSym_spanSingleton_eq_one_of_totallyPositive_of_isUnramifiedAtFinite
    {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsMulCommutative (L ≃ₐ[K] L)]
    (hARL : NK.CFTLib.ArtinReciprocityIdeal)
    (hunr : differentIdeal (NumberField.RingOfIntegers K) (NumberField.RingOfIntegers L) = ⊤)
    (hcomm : ∀ a b : L ≃ₐ[K] L, a * b = b * a)
    (b : Kˣ)
    (hpos : ∀ (w : NumberField.InfinitePlace K) (hw : w.IsReal),
      0 < (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hw)
        (algebraMap K w.Completion (b : K))) :
    NK.CFTLib.Arl.artinSym (K := K) (L := L) hcomm
      (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers K)) ((b : Kˣ) : K))
      = 1 :=
  artinSym_spanSingleton_eq_one_of_artinKillsPrincipal_one (K := K) (L := L) hcomm hunr
    (NK.CFTLib.ArtinReciprocityIdeal.artinKillsPrincipal_one_of_unramified
      (K := K) (L := L) hARL hunr) b hpos

end NK.CFTLib.Existence
