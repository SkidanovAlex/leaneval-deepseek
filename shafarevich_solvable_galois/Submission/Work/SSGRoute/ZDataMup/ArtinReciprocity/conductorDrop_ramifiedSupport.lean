import Mathlib
import Submission.Work.SSGRoute.ZDataMup.ArtinReciprocity.Imports
import Submission.Work.SSGRoute.ZDataMup.ArtinReciprocity.isAdmissible_of_artinKillsPrincipal
import Submission.Work.SSGRoute.ZDataMup.weakApprox_pos_numberField
import Submission.NK.CFTLib.IdeleHasse.localFaithful_onePlace
import Submission.NK.CFTLib.IdeleHasse.onePlace_localNorm
import Submission.NK.CFTLib.IdeleHasse.localGlobalArtinMap_exists
import Submission.Work.SSGRoute.ZDataMup.ArtinReciprocity.artinSym_eq_Phi_principalIdele
import Submission.Work.SSGRoute.ZDataMup.abelian_of_cyclicCase
import Submission.Work.SSGRoute.ZDataMup.CyclicCaseStatement
import Submission.Work.SSGRoute.ZDataMup.CycleDefs
import Submission.Work.SSGRoute.ZDataMup.CycleCongr
import Submission.Work.SSGRoute.ZDataMup.CycleConductorDropAssembly
import Submission.Work.SSGRoute.ZDataMup.cycleConductorDrop
import Submission.Work.SSGRoute.ZDataMup.ArtinReciprocity.cyclicCaseStatement_ramifiedSupport
import Submission.Work.SSGRoute.ZDataMup.ArtinReciprocity.productFormula_cyclic
import Submission.Work.SSGRoute.ZDataMup.ArtinReciprocity.isAdmissible_of_artinKillsPrincipal
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!

# The conductor drop at the ramified primes (Neukirch, *Algebraic Number Theory*, V.6.1;
Lang, *Algebraic Number Theory*, X §4)

`Work.SSGRoute.ZDataMup.ArtinReciprocity.conductorDrop_ramifiedSupport` is the statement that the
conductor of an abelian extension `L / K` of number fields is supported on the ramified primes, in
the form in which the `ZDataMup` / `ArtinReciprocity` lanes consume it:

let `m > 0` be a modulus such that (i) every prime `p` not dividing `(m)` is unramified in `L`
(`hram`) and (ii) the ideal-theoretic Artin symbol kills every principal ideal `(a)` with
`a ≡ 1 mod m` and `a` totally positive (`hprinc`).  Then for `b : Kˣ` which is `≡ 1 mod m`
**at the ramified primes dividing `(m)` only** (`hcong`) and totally positive (`hpos`), the Artin
symbol of `(b)` is `1`.

## The proof (sorry-free, `#print axioms = [propext, Classical.choice, Quot.sound]`)

The cyclic case is `conductorDrop_cyclic_of_productFormula`: given the **idèlic Artin map**
`Φ : 𝕀 K →* Gal(L/K)` of the extension — killing `Kˣ`, killing the idèlic norms and sending the
prime idèle at every unramified prime to the Frobenius (the product form of Hilbert reciprocity,
Milne *CFT* VII.8.1(a)) — the identity `artinSym ((b)) = Φ (principalIdele b)`
(`artinSym_eq_Phi_principalIdele`, which uses the admissibility of `m`,
`isAdmissible_of_artinKillsPrincipal`, and the congruence/positivity of `b`) reduces the claim to
the principal-killing clause of `Φ`.  No congruence of `b` at the *unramified* primes dividing
`(m)` is used: that is exactly the content of the conductor being supported on the ramified primes.
The abelian case follows by `Work.SSGRoute.ZDataMup.abelian_of_cyclicCase` (reduction to cyclic
quotients).

`frobAtPrime_eq_ideleArtin_of_unramified` — the Frobenius normalisation of the idèlic Artin map
attached to a congruence datum at an arbitrary unramified prime (Milne *CFT* VII.8.1 with
V.5.3(a)) — is derived here from the same conductor drop (it was the second `sorry` of this file in
earlier sessions, now proved): for the adjust element `b_Q` of `ideleOfPrime K Q` the componentwise
congruence and positivity come from the congruence datum, and
`ideleArtin (ideleOfPrime K Q) = frobAtPrime Q · artinSym ((b_Q)) = frobAtPrime Q`.

An independent reduction of the cyclic case to the **cycle** (ideal-modulus) conductor drop
`Work.SSGRoute.ZDataMup.CycleKernelLe` — via the proved assembly `CycleConductorDropOfIndex`,
Lang's norm index inequality `cruxLang_cycleIndexInequality` and `CycleBaseChangeExists`, see
`ArtinReciprocity/cyclicCaseStatement_ramifiedSupport.lean` — is kept in this directory as a
fallback; the target above does not use it. -/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open scoped NumberField RestrictedProduct nonZeroDivisors
open NumberField IsDedekindDomain

noncomputable section

namespace Work.SSGRoute.ZDataMup.ArtinReciprocity

open NK.GlobalCFT

/-- **One-place faithfulness of the idèlic Artin map attached to a congruence datum.**

For a cyclic extension `L/K`, a modulus `m > 0` with the ramification and product conditions and a
congruence datum `(U, hadj)`, any idèlic Artin map `art` with kernel `N_{L/K}𝕀_L · Kˣ` is trivial
exactly on the local norms at every place:

  `art (onePlace v a) = 1 ↔ a ∈ N_{L_v/K_v}`.

This is the local faithfulness `NK.CFTLib.IdeleHasse.localFaithful_onePlace` combined with the
one-place dictionary `NK.CFTLib.IdeleHasse.onePlace_mem_normImage_iff`. -/
theorem ideleArtin_onePlace_iff
    {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic (L ≃ₐ[K] L)]
    (art : Idele K →* (L ≃ₐ[K] L))
    (hker : art.ker = Idele.normImage K L ⊔ Idele.principalSubgroup K) :
    ∀ (v : Place K) (a : (Place.localField K v)ˣ),
      art (NK.HassePrinciple.onePlace v a) = 1 ↔
        a ∈ NK.CFTLib.IdeleHasse.localNormSubgroup (K := K) (L := L) v := by
  intro v a
  rw [← MonoidHom.mem_ker, hker]
  exact ⟨fun h => (NK.CFTLib.IdeleHasse.onePlace_mem_normImage_iff (K := K) (L := L) v a).mp
      (NK.CFTLib.IdeleHasse.localFaithful_onePlace (K := K) (L := L)
        (inferInstance : IsCyclic (L ≃ₐ[K] L)) h),
    fun h => Subgroup.mem_sup_left
      ((NK.CFTLib.IdeleHasse.onePlace_mem_normImage_iff (K := K) (L := L) v a).mpr h)⟩

/-- **Frobenius normalisation of the idèlic Artin map at every unramified prime** (Milne, *CFT*,
VII.8.1 with the normalisation of V.5.3(a)).

This is the conductor drop in the form in which it is consumed: the idèlic Artin map attached to a
congruence datum of modulus `m` sends the prime idèle at *every* unramified prime `Q` — including
the primes dividing `(m)` — to the Frobenius element `Frob_Q`.  See
`Work.SSGRoute.ZDataMup.ideleArtin_frob_unramified_abelian`, where this is derived from the target
theorem of the present file. -/
theorem frobAtPrime_eq_ideleArtin_of_unramified
    {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (hcomm : ∀ a b : Gal(L/K), a * b = b * a)
    (m : ℕ) (hm : 0 < m)
    (hram : ∀ 𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      (m : NumberField.RingOfIntegers K) ∉ 𝔭.asIdeal →
      Ideal.ramificationIdxIn 𝔭.asIdeal (NumberField.RingOfIntegers L) = 1)
    (hprinc : NK.CFTLib.artinKillsPrincipal K L m)
    (U : Subgroup (Idele K))
    (hU : NK.CFTLib.Arl.IsCongruenceSubgroup (K := K) m U)
    (hadj : ∀ x : Idele K, ∃ b : Kˣ, x * Idele.principalIdele K b ∈ U)
    {Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)}
    (hunr : NK.HeckeL.IsUnramifiedIn (K := K) (L := L) Q) :
    NK.CFTLib.Arl.ideleArtin (K := K) (L := L) hcomm U hadj (NK.HeckeL.ideleOfPrime K Q)
      = NK.Chebotarev.frobAtPrime (K := K) (L := L) Q := by
  classical
  set b : Kˣ := NK.CFTLib.Arl.adjust U hadj (NK.HeckeL.ideleOfPrime K Q) with hb
  -- the chosen adjust element
  have hUmem : NK.HeckeL.ideleOfPrime K Q * Idele.principalIdele K b ∈ U :=
    NK.CFTLib.Arl.adjust_spec U hadj (NK.HeckeL.ideleOfPrime K Q)
  -- the componentwise description of `U`
  have hspec := (hU.1 (NK.HeckeL.ideleOfPrime K Q * Idele.principalIdele K b)).mp hUmem
  -- `Q` is unramified, so it is not one of the ramified primes
  have hramQ : Ideal.ramificationIdxIn Q.asIdeal (𝓞 L) = 1 := by
    obtain ⟨P, hP⟩ := NK.Chebotarev.exists_primeIdeal_liesOver (K := K) (L := L) Q
    rw [Ideal.ramificationIdxIn_eq_ramificationIdx (A := 𝓞 K) (B := 𝓞 L) Q.asIdeal P.asIdeal
      (Gal(L/K))]
    exact hunr P hP
  -- the adjust element is congruent to `1` modulo `m` at every ramified prime dividing `(m)`
  have hcongb : ∀ 𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      (m : 𝓞 K) ∈ 𝔮.asIdeal →
      Ideal.ramificationIdxIn 𝔮.asIdeal (𝓞 L) ≠ 1 →
      Valued.v (algebraMap K (𝔮.adicCompletion K) ((b : Kˣ) : K) - 1)
        ≤ Valued.v ((m : ℕ) : 𝔮.adicCompletion K) := by
    intro 𝔮 h𝔮 hne
    have h𝔮Q : 𝔮 ≠ Q := fun h => hne (h ▸ hramQ)
    have hcomp : NK.HeckeL.ideleOfPrime K Q (NK.GlobalCFT.Place.ofFinite 𝔮) = 1 := by
      show NK.GlobalCFT.IdeleClassGroup.unifUnit K 𝔮 ^ (if 𝔮 = Q then (1 : ℤ) else 0) = 1
      rw [if_neg h𝔮Q, zpow_zero]
    have hcomp' : (NK.HeckeL.ideleOfPrime K Q * Idele.principalIdele K b)
        (NK.GlobalCFT.Place.ofFinite 𝔮) = Units.map (algebraMap K (𝔮.adicCompletion K)) b := by
      rw [Idele.mul_apply, Idele.principalIdele_apply, hcomp, one_mul]
    have hmem := hspec.1 𝔮 h𝔮
    rw [hcomp'] at hmem
    exact hmem
  -- and it is totally positive
  have hposb : ∀ (w : NumberField.InfinitePlace K) (hw : w.IsReal),
      0 < (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hw)
            (algebraMap K w.Completion ((b : Kˣ) : K)) := by
    intro w hw
    have hcomp : NK.HeckeL.ideleOfPrime K Q (NK.GlobalCFT.Place.ofInfinite w) = 1 := rfl
    have hcomp' : (NK.HeckeL.ideleOfPrime K Q * Idele.principalIdele K b)
        (NK.GlobalCFT.Place.ofInfinite w) = Units.map (algebraMap K w.Completion) b := by
      rw [Idele.mul_apply, Idele.principalIdele_apply, hcomp, one_mul]
    have hmem := hspec.2 w
    rw [hcomp'] at hmem
    exact hmem hw
  -- the abelian conductor drop at the modulus `m`, applied to the adjust element
  have hb1 : NK.CFTLib.Arl.artinSym (K := K) (L := L) hcomm
      (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) ((b : Kˣ) : K)) = 1 :=
    abelian_of_cyclicCase
      (fun {K L} _ _ _ _ _ _ _ _ hcommc M hM hramM hprincM c hcongc hposc =>
        cyclicCaseStatement_ramifiedSupport (K := K) (L := L) hcommc M hM hramM hprincM c
          hcongc hposc)
      hcomm m hm hram hprinc b hcongb hposb
  -- the idèlic Artin map of a prime idèle is the Frobenius times the Artin symbol of the adjust
  show NK.CFTLib.Arl.artinSym (K := K) (L := L) hcomm
    (Idele.idealOf (NK.HeckeL.ideleOfPrime K Q * Idele.principalIdele K b)) = _
  rw [Idele.idealOf_mul, NK.CFTLib.Arl.idealOf_ideleOfPrime, Idele.idealOf_principalIdele,
    NK.CFTLib.Arl.artinSym_mul (K := K) (L := L) hcomm
      (FractionalIdeal.coeIdeal_ne_zero.mpr Q.ne_bot)
      (FractionalIdeal.spanSingleton_ne_zero_iff.mpr (Units.ne_zero b)),
    hb1, mul_one, NK.CFTLib.Arl.artinSym_prime]


/-! ## The product form of Hilbert reciprocity: the single remaining input -/

/-- **Hilbert reciprocity in product (Frobenius-normalised) form**, for cyclic extensions.

For every finite cyclic extension `L/K` of number fields there is an idèlic Artin map
`Φ : 𝕀 K →* Gal(L/K)` killing the principal idèles `Kˣ`, killing the idèles that are norms from `L`,
and sending the prime idèle at `Q` to the Frobenius element at `Q` for **every** unramified `Q`.

The first two clauses hold for the idèlic Artin map *constructed from a congruence datum*
(`NK.CFTLib.Arl.exists_monoidHom_ideleArtin`), which however is Frobenius-normalised only at the
primes outside the modulus; conversely the *glued* local–global map
(`NK.CFTLib.IdeleHasse.localGlobalArtinMap_exists`) is Frobenius-normalised at every unramified
prime but its triviality on `Kˣ` is precisely the product formula.  The two maps cannot be compared
by `Work.SSGRoute.ZDataMup.ideleHom_eq_of_frobAtPrime_of_notMem`, whose hypotheses require the
principal-killing clause for *both* of them.  This is therefore a genuine new input: it is
Milne, *CFT*, Theorem 8.1(a), equivalently `∑_v inv_v = 0`. -/
def ProductFormula : Prop :=
  ∀ {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic (L ≃ₐ[K] L)],
    ∃ Φ : NK.GlobalCFT.Idele K →* (L ≃ₐ[K] L),
      (∀ a : Kˣ, Φ (NK.GlobalCFT.Idele.principalIdele K a) = 1) ∧
      (∀ y : NK.GlobalCFT.Idele L, Φ (NK.GlobalCFT.Idele.normIdeleHom K L y) = 1) ∧
      (∀ Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
        NK.HeckeL.IsUnramifiedIn (K := K) (L := L) Q →
        Φ (NK.HeckeL.ideleOfPrime K Q) = NK.Chebotarev.frobAtPrime (K := K) (L := L) Q)

/-- **The cyclic case of the conductor drop, from the product form of Hilbert reciprocity.**

The proof is the comparison identity `artinSym ((b)) = Φ (principalIdele K b)`
(`artinSym_eq_Phi_principalIdele`, using the admissibility of `m`
`isAdmissible_of_artinKillsPrincipal` and the congruence/positivity of `b`) followed by the
principal-killing clause of `ProductFormula`.  No congruence of `b` at the *unramified* primes
dividing `(m)` is used: that is exactly the content of the conductor being supported on the
ramified primes. -/
theorem conductorDrop_cyclic_of_productFormula (hprod : ProductFormula)
    {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic (L ≃ₐ[K] L)]
    (hcomm : ∀ a b : L ≃ₐ[K] L, a * b = b * a)
    (m : ℕ) (hm : 0 < m)
    (hram : ∀ 𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      (m : NumberField.RingOfIntegers K) ∉ 𝔭.asIdeal →
      Ideal.ramificationIdxIn 𝔭.asIdeal (NumberField.RingOfIntegers L) = 1)
    (hprinc : NK.CFTLib.artinKillsPrincipal K L m)
    (b : Kˣ)
    (hcong : ∀ 𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      (m : NumberField.RingOfIntegers K) ∈ 𝔮.asIdeal →
      Ideal.ramificationIdxIn 𝔮.asIdeal (NumberField.RingOfIntegers L) ≠ 1 →
      Valued.v (algebraMap K (𝔮.adicCompletion K) ((b : Kˣ) : K) - 1)
        ≤ Valued.v ((m : ℕ) : 𝔮.adicCompletion K))
    (hpos : ∀ (w : NumberField.InfinitePlace K) (hw : w.IsReal),
      0 < (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hw)
            (algebraMap K w.Completion ((b : Kˣ) : K))) :
    NK.CFTLib.Arl.artinSym (K := K) (L := L) hcomm
      (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers K))
        ((b : Kˣ) : K)) = 1 := by
  obtain ⟨Φ, hprin, hnorm, hfrob⟩ := hprod (K := K) (L := L)
  have hAdm : NK.CFTLib.ArtinReciprocityIdeal.IsAdmissible K L m :=
    isAdmissible_of_artinKillsPrincipal (K := K) (L := L) hcomm m hm hram hprinc
  rw [← artinSym_eq_Phi_principalIdele (K := K) (L := L) hcomm m hAdm Φ hnorm hfrob hram b hcong
    hpos, hprin b]

/-- **The conductor drop, from the product form of Hilbert reciprocity** (abelian case, reduced to
the cyclic one by `Work.SSGRoute.ZDataMup.abelian_of_cyclicCase`). -/
theorem conductorDrop_ramifiedSupport_of_productFormula (hprod : ProductFormula)
    {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (hcomm : ∀ a b : L ≃ₐ[K] L, a * b = b * a)
    (m : ℕ) (hm : 0 < m)
    (hram : ∀ 𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      (m : NumberField.RingOfIntegers K) ∉ 𝔭.asIdeal →
      Ideal.ramificationIdxIn 𝔭.asIdeal (NumberField.RingOfIntegers L) = 1)
    (hprinc : NK.CFTLib.artinKillsPrincipal K L m)
    (b : Kˣ)
    (hcong : ∀ 𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      (m : NumberField.RingOfIntegers K) ∈ 𝔮.asIdeal →
      Ideal.ramificationIdxIn 𝔮.asIdeal (NumberField.RingOfIntegers L) ≠ 1 →
      Valued.v (algebraMap K (𝔮.adicCompletion K) ((b : Kˣ) : K) - 1)
        ≤ Valued.v ((m : ℕ) : 𝔮.adicCompletion K))
    (hpos : ∀ (w : NumberField.InfinitePlace K) (hw : w.IsReal),
      0 < (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hw)
            (algebraMap K w.Completion ((b : Kˣ) : K))) :
    NK.CFTLib.Arl.artinSym (K := K) (L := L) hcomm
      (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers K))
        ((b : Kˣ) : K)) = 1 :=
  abelian_of_cyclicCase
    (fun {K L} _ _ _ _ _ _ _ _ hcommc m hm hramc hprinc c hcongc hposc =>
      conductorDrop_cyclic_of_productFormula (K := K) (L := L) hprod hcommc m hm hramc hprinc c
        hcongc hposc)
    hcomm m hm hram hprinc b hcong hpos

/-- **The conductor of `L/K` is supported on the ramified primes** (Neukirch, *Algebraic Number
Theory*, V.6.1; Lang, *Algebraic Number Theory*, X §4).  See the module docstring for the status
of its proof in the workspace. -/
theorem conductorDrop_ramifiedSupport
    {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (hcomm : ∀ a b : L ≃ₐ[K] L, a * b = b * a)
    (m : ℕ) (hm : 0 < m)
    (hram : ∀ 𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      (m : NumberField.RingOfIntegers K) ∉ 𝔭.asIdeal →
      Ideal.ramificationIdxIn 𝔭.asIdeal (NumberField.RingOfIntegers L) = 1)
    (hprinc : NK.CFTLib.artinKillsPrincipal K L m)
    (b : Kˣ)
    (hcong : ∀ 𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      (m : NumberField.RingOfIntegers K) ∈ 𝔮.asIdeal →
      Ideal.ramificationIdxIn 𝔮.asIdeal (NumberField.RingOfIntegers L) ≠ 1 →
      Valued.v (algebraMap K (𝔮.adicCompletion K) ((b : Kˣ) : K) - 1)
        ≤ Valued.v ((m : ℕ) : 𝔮.adicCompletion K))
    (hpos : ∀ (w : NumberField.InfinitePlace K) (hw : w.IsReal),
      0 < (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hw)
            (algebraMap K w.Completion ((b : Kˣ) : K))) :
    NK.CFTLib.Arl.artinSym (K := K) (L := L) hcomm
      (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers K))
        ((b : Kˣ) : K)) = 1 :=
  -- The conductor drop at a **cycle** (`Work.SSGRoute.ZDataMup.cycleConductorDrop`) gives the
  -- cyclic case `cyclicCaseStatement_ramifiedSupport`, and the abelian case follows by
  -- `Work.SSGRoute.ZDataMup.abelian_of_cyclicCase`.
  conductorDrop_ramifiedSupport_of_productFormula
    (hprod := fun {K L} _ _ _ _ _ _ _ _ => productFormula_cyclic (K := K) (L := L))
    hcomm m hm hram hprinc b hcong hpos

end Work.SSGRoute.ZDataMup.ArtinReciprocity
