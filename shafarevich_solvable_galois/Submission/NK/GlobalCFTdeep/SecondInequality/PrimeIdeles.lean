import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Mathlib.Topology.Algebra.RestrictedProduct.Basic
import Submission.NK.GlobalCFTdeep.SecondInequality.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Idèles supported at a single place

For a number field `K` and a prime `𝔭` of `K`, the idèle `ideleSingle K 𝔭 z` is `z` at the finite
place `𝔭` and `1` at every other place.  The idèles `ideleOfPrime K 𝔭` and
`ideleOfIdeal K 𝔭.asIdeal` of the Hecke chapter are of this shape: they are `ideleSingle K 𝔭 u` for
the chosen local uniformiser `u` of `K_𝔭`.

The reason for introducing them separately is that the norm computation of the second inequality
requires idèles supported at a single place with an *arbitrary* local value `z`, not only with a
uniformiser.

## Main definitions

* `NK.GlobalCFTdeep.SecondInequality.ideleSingle`

## Main results

* `ideleSingle_apply_ofFinite_self`, `ideleSingle_apply_ofFinite_ne`, `ideleSingle_apply_ofInfinite`
* `ideleSingle_mul`
* `ideleOfFun_eq_ideleSingle`
* `ideleOfPrime_eq_ideleSingle`, `ideleOfIdeal_prime_eq_ideleSingle`,
  `ideleOfIdeal_prime_eq_ideleOfPrime`
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open NumberField IsDedekindDomain
open scoped BigOperators nonZeroDivisors NumberField RestrictedProduct
open NK.GlobalCFT

noncomputable section

namespace NK.GlobalCFTdeep.SecondInequality

variable {K : Type*} [Field K] [NumberField K]

/-- The idèle of `K` which is `z` at the finite place `𝔭` and `1` at every other place. -/
noncomputable def ideleSingle (K : Type*) [Field K] [NumberField K] (𝔭 : PrimeIdeal K)
    (z : (𝔭.adicCompletion K)ˣ) : Idele K := by
  classical
  exact RestrictedProduct.mulSingle (fun v : Place K => Place.localUnits K v) (Place.ofFinite 𝔭) z

@[simp] theorem ideleSingle_apply_ofFinite_self (𝔭 : PrimeIdeal K) (z : (𝔭.adicCompletion K)ˣ) :
    ideleSingle K 𝔭 z (Place.ofFinite 𝔭) = z := by
  classical
  exact RestrictedProduct.mulSingle_eq_same _ _ _

theorem ideleSingle_apply_ofFinite_ne {𝔭 Q : PrimeIdeal K} (h : Q ≠ 𝔭)
    (z : (𝔭.adicCompletion K)ˣ) :
    ideleSingle K 𝔭 z (Place.ofFinite Q) = 1 := by
  classical
  refine RestrictedProduct.mulSingle_eq_of_ne _ _ ?_
  simpa using h

theorem ideleSingle_apply_ofInfinite {𝔭 : PrimeIdeal K} (z : (𝔭.adicCompletion K)ˣ)
    (w : InfinitePlace K) :
    ideleSingle K 𝔭 z (Place.ofInfinite w) = 1 := by
  classical
  refine RestrictedProduct.mulSingle_eq_of_ne _ _ ?_
  exact fun h => Place.ofInfinite_ne_ofFinite w 𝔭 h

@[simp] theorem ideleSingle_apply_ofFinite_self' {𝔭 Q : PrimeIdeal K} (h : Q = 𝔭)
    (z : (𝔭.adicCompletion K)ˣ) :
    ideleSingle K 𝔭 z (Place.ofFinite Q) = h ▸ z := by
  subst h
  simp

theorem ideleSingle_mul (𝔭 : PrimeIdeal K) (z z' : (𝔭.adicCompletion K)ˣ) :
    ideleSingle K 𝔭 (z * z') = ideleSingle K 𝔭 z * ideleSingle K 𝔭 z' := by
  classical
  exact RestrictedProduct.mulSingle_mul _ _ _ _

theorem ideleSingle_one (𝔭 : PrimeIdeal K) : ideleSingle K 𝔭 1 = 1 := by
  classical
  exact RestrictedProduct.mulSingle_one _ _

theorem ideleSingle_inv (𝔭 : PrimeIdeal K) (z : (𝔭.adicCompletion K)ˣ) :
    ideleSingle K 𝔭 z⁻¹ = (ideleSingle K 𝔭 z)⁻¹ := by
  classical
  exact RestrictedProduct.mulSingle_inv _ _ _

variable {𝔭 : PrimeIdeal K}

/-- The local norm `localNormFinite q Q h` does not depend on the chosen proof `h` that `q` lies
over `Q`: two such proofs are equal by proof irrelevance, and `h` is a genuine argument of
`localNormFinite`. -/
theorem localNormFinite_congr {L : Type*} [Field L] [NumberField L] [Algebra K L]
    {q : PrimeIdeal L} {Q : PrimeIdeal K} {h h' : q.asIdeal.LiesOver Q.asIdeal}
    (z : (q.adicCompletion L)ˣ) :
    Place.localNormFinite q Q h z = Place.localNormFinite q Q h' z := by
  rw [Subsingleton.elim h h']

/-- An idèle with a single nonzero `𝔭`-adic exponent is the idèle supported at `𝔭` with value the
corresponding power of the chosen uniformiser. -/
theorem ideleOfFun_eq_ideleSingle {f : HeightOneSpectrum (𝓞 K) → ℤ}
    (hf : ∀ᶠ q in Filter.cofinite, f q = 0) (h : ∀ q, q ≠ 𝔭 → f q = 0) :
    IdeleClassGroup.ideleOfFun K f hf =
      ideleSingle K 𝔭 (IdeleClassGroup.unifUnit K 𝔭 ^ f 𝔭) := by
  classical
  refine Idele.ext fun v => ?_
  rcases v with w | q
  · have h1 : (IdeleClassGroup.ideleOfFun K f hf : Idele K) (Place.ofInfinite w) = 1 := rfl
    rw [h1, ideleSingle_apply_ofInfinite]
  · by_cases hq : q = 𝔭
    · have h1 : (IdeleClassGroup.ideleOfFun K f hf : Idele K) (Place.ofFinite q)
          = IdeleClassGroup.unifUnit K q ^ f q := rfl
      rw [h1, hq, ideleSingle_apply_ofFinite_self]
    · have h1 : (IdeleClassGroup.ideleOfFun K f hf : Idele K) (Place.ofFinite q)
          = IdeleClassGroup.unifUnit K q ^ f q := rfl
      rw [h1, ideleSingle_apply_ofFinite_ne hq, h q hq, zpow_zero]

theorem ideleOfPrime_eq_ideleSingle (𝔭 : PrimeIdeal K) :
    HeckeL.ideleOfPrime K 𝔭 = ideleSingle K 𝔭 (IdeleClassGroup.unifUnit K 𝔭) := by
  classical
  unfold HeckeL.ideleOfPrime
  rw [ideleOfFun_eq_ideleSingle (K := K) (𝔭 := 𝔭)
    (f := fun q => if q = 𝔭 then (1 : ℤ) else 0)
    (by rw [Filter.eventually_cofinite]
        exact (Set.finite_singleton 𝔭).subset (fun q hq => by simpa using hq))
    (fun q hq => by simp [hq])]
  rw [if_pos rfl, zpow_one]

theorem ideleOfIdeal_prime_eq_ideleSingle (𝔭 : PrimeIdeal K) :
    HeckeL.ideleOfIdeal K 𝔭.asIdeal = ideleSingle K 𝔭 (IdeleClassGroup.unifUnit K 𝔭) := by
  classical
  unfold HeckeL.ideleOfIdeal
  rw [ideleOfFun_eq_ideleSingle (K := K) (𝔭 := 𝔭)
    (f := fun q => FractionalIdeal.count K q (𝔭.asIdeal : FractionalIdeal (𝓞 K)⁰ K))
    (FractionalIdeal.finite_factors (K := K) (I := (𝔭.asIdeal : FractionalIdeal (𝓞 K)⁰ K)))
    (fun q hq => by rw [FractionalIdeal.count_maximal, if_neg (fun hh => hq hh.symm)])]
  rw [FractionalIdeal.count_maximal, if_pos rfl, zpow_one]

theorem ideleOfIdeal_prime_eq_ideleOfPrime (𝔭 : PrimeIdeal K) :
    HeckeL.ideleOfIdeal K 𝔭.asIdeal = HeckeL.ideleOfPrime K 𝔭 := by
  rw [ideleOfIdeal_prime_eq_ideleSingle, ideleOfPrime_eq_ideleSingle]

end NK.GlobalCFTdeep.SecondInequality
