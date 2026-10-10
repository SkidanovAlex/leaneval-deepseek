import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Submission.NK.Chebotarev.AbelianChebotarevOfLFunctions
import Submission.NK.GlobalCFT.IdeleClassGroup.globalCFT_idealClassMap_exists
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open NumberField IsDedekindDomain
open scoped BigOperators Classical nonZeroDivisors
open Filter

open NK.GlobalCFT (Idele IdeleClassGroup)

noncomputable section

namespace NK.HeckeL

/-! ## Primes -/

/-- A finite place of the number field `K`, i.e. a nonzero prime ideal of `𝓞 K`.  This is the
same type as `NK.Chebotarev.PrimeIdeal K`, so the Frobenius API of the sibling area applies. -/
abbrev PrimeIdeal (K : Type*) [Field K] [NumberField K] := HeightOneSpectrum (𝓞 K)

/-- `𝔭` is unramified in `L / K`. -/
def IsUnramifiedIn {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] (𝔭 : PrimeIdeal K) : Prop :=
  ∀ 𝔮 : PrimeIdeal L, 𝔮.asIdeal.LiesOver 𝔭.asIdeal →
    𝔮.asIdeal.ramificationIdx (𝓞 K) = 1

/-! ## The idèle class of an ideal -/

variable {K : Type*} [Field K] [NumberField K]

/-- The idèle which is a local uniformiser at `𝔭` and `1` at every other place.  Its attached
fractional ideal is `𝔭`. -/
noncomputable def ideleOfPrime (K : Type*) [Field K] [NumberField K] (𝔭 : PrimeIdeal K) : Idele K :=
  IdeleClassGroup.ideleOfFun K (fun q => if q = 𝔭 then 1 else 0) (by
    rw [Filter.eventually_cofinite]
    refine Set.Finite.subset (Set.finite_singleton 𝔭) ?_
    intro q hq
    simpa using hq)

/-- The idèle attached to an ideal, via its local exponents: the exponents are the multiplicities
of the primes in the factorisation of `I`. -/
noncomputable def ideleOfIdeal (K : Type*) [Field K] [NumberField K]
    (I : Ideal (𝓞 K)) : Idele K :=
  IdeleClassGroup.ideleOfFun K (fun q => FractionalIdeal.count K q (I : FractionalIdeal (𝓞 K)⁰ K))
    (FractionalIdeal.finite_factors (K := K) (I := (I : FractionalIdeal (𝓞 K)⁰ K)))

/-- The class of the ideal `I` in the ray class group of `K` modulo `U`. -/
noncomputable def classOfIdeal (K : Type*) [Field K] [NumberField K] (U : Subgroup (Idele K))
    (I : Ideal (𝓞 K)) : IdeleClassGroup.rayClassGroup K U :=
  IdeleClassGroup.rayClassGroupMk K U (IdeleClassGroup.mk K (ideleOfIdeal K I))

/-- The class of the prime ideal `𝔭` in the ray class group of `K` modulo `U`
(`rayClassGroup K U = 𝕀 K ⧸ (Kˣ · U)`): this is `χ(𝔭)` for a ray class character `χ`. -/
noncomputable def primeClass (K : Type*) [Field K] [NumberField K] (U : Subgroup (Idele K))
    (𝔭 : PrimeIdeal K) : IdeleClassGroup.rayClassGroup K U :=
  classOfIdeal K U 𝔭.asIdeal

/-! ## Characters of a ray class group -/

/-- A **character of the ray class group** `𝕀 K ⧸ (Kˣ · U)`: the analytic objects of this chapter
are the Hecke `L`-series attached to these. -/
abbrev RayChar (K : Type*) [Field K] [NumberField K] (U : Subgroup (Idele K)) : Type _ :=
  IdeleClassGroup.rayClassGroup K U →* ℂˣ

namespace RayChar

variable {U : Subgroup (Idele K)}

/-- The value of `χ` at the prime `𝔭`. -/
noncomputable def atPrime (χ : RayChar K U) (𝔭 : PrimeIdeal K) : ℂ :=
  (χ (primeClass K U 𝔭) : ℂ)

/-- The value of `χ` at the ideal `I`. -/
noncomputable def atIdeal (χ : RayChar K U) (I : Ideal (𝓞 K)) : ℂ :=
  (χ (classOfIdeal K U I) : ℂ)

/-- The complex-valued character attached to a `ℂˣ`-valued one. -/
def toComplex (χ : RayChar K U) : IdeleClassGroup.rayClassGroup K U →* ℂ :=
  (Units.coeHom ℂ).comp χ

@[simp] theorem toComplex_apply (χ : RayChar K U) (x : IdeleClassGroup.rayClassGroup K U) :
    χ.toComplex x = (χ x : ℂ) := rfl

@[simp] theorem atPrime_apply (χ : RayChar K U) (𝔭 : PrimeIdeal K) :
    χ.atPrime 𝔭 = χ.toComplex (primeClass K U 𝔭) := rfl

@[simp] theorem atIdeal_apply (χ : RayChar K U) (I : Ideal (𝓞 K)) :
    χ.atIdeal I = χ.toComplex (classOfIdeal K U I) := rfl

/-- The norm of the value of a character at any point of a finite ray class group is `1`. -/
theorem norm_toComplex_apply_eq_one [Finite (IdeleClassGroup.rayClassGroup K U)]
    (χ : RayChar K U) (x : IdeleClassGroup.rayClassGroup K U) : ‖χ.toComplex x‖ = 1 :=
  NK.Chebotarev.norm_monoidHom_units_apply_eq_one χ x

theorem norm_atPrime_eq_one [Finite (IdeleClassGroup.rayClassGroup K U)]
    (χ : RayChar K U) (𝔭 : PrimeIdeal K) : ‖χ.atPrime 𝔭‖ = 1 :=
  norm_toComplex_apply_eq_one χ _

theorem norm_atIdeal_eq_one [Finite (IdeleClassGroup.rayClassGroup K U)]
    (χ : RayChar K U) (I : Ideal (𝓞 K)) : ‖χ.atIdeal I‖ = 1 :=
  norm_toComplex_apply_eq_one χ _

end RayChar

/-! ## The `L`-series -/

/-- The Euler factor `(1 - χ(𝔭) N𝔭^{-s})⁻¹` of the Hecke `L`-series at the prime `𝔭`. -/
noncomputable def eulerFactor (K : Type*) [Field K] [NumberField K] (U : Subgroup (Idele K))
    (χ : RayChar K U) (s : ℝ) (𝔭 : PrimeIdeal K) : ℂ :=
  (1 - χ.atPrime 𝔭 * (((Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s) : ℝ) : ℂ))⁻¹

/-- **The Euler product of the Hecke `L`-series** of `χ` modulo the modulus described by the
finite set `S` of primes: `∏_{𝔭 ∉ S} (1 - χ(𝔭) N𝔭^{-s})⁻¹`. -/
noncomputable def heckeEulerProduct (K : Type*) [Field K] [NumberField K] (U : Subgroup (Idele K))
    (S : Finset (PrimeIdeal K)) (χ : RayChar K U) (s : ℝ) : ℂ :=
  ∏' 𝔭 : {𝔭 : PrimeIdeal K // 𝔭 ∉ S}, eulerFactor K U χ s 𝔭.1

/-- **The Hecke `L`-series of `χ` modulo the modulus described by `S`**: the Dirichlet series
`∑_𝔞 χ([𝔞]) · N𝔞^{-s}` over the nonzero ideals of `𝓞 K` coprime to every prime in `S`. -/
noncomputable def heckeLSeries (K : Type*) [Field K] [NumberField K] (U : Subgroup (Idele K))
    (S : Finset (PrimeIdeal K)) (χ : RayChar K U) (s : ℝ) : ℂ :=
  ∑' 𝔞 : {𝔞 : Ideal (𝓞 K) // 𝔞 ≠ 0 ∧ ∀ 𝔭 ∈ S, ¬ 𝔭.asIdeal ∣ 𝔞},
    χ.atIdeal (𝔞 : Ideal (𝓞 K)) * (((Ideal.absNorm (𝔞 : Ideal (𝓞 K)) : ℝ) ^ (-s) : ℝ) : ℂ)

/-- **The coefficient of the Hecke `L`-series at `n`**: the sum of `χ(𝔞)` over the ideals `𝔞` of
norm `n` which are coprime to the modulus `S`.  Its Dirichlet series `∑_n heckeCoeff n · n^{-s}`
is the Hecke `L`-series of `χ`. -/
noncomputable def heckeCoeff (K : Type*) [Field K] [NumberField K] (U : Subgroup (Idele K))
    (S : Finset (PrimeIdeal K)) (χ : RayChar K U) (n : ℕ) : ℂ :=
  ∑' 𝔞 : {𝔞 : Ideal (𝓞 K) // 𝔞 ≠ 0 ∧ (∀ 𝔭 ∈ S, ¬ 𝔭.asIdeal ∣ 𝔞) ∧
      Ideal.absNorm 𝔞 = n},
    χ.atIdeal (𝔞 : Ideal (𝓞 K))

/-- **The character-twisted prime sum** of a ray class character: the `k = 1` part of the
logarithm of the Euler product. -/
noncomputable def primeSum (K : Type*) [Field K] [NumberField K] (U : Subgroup (Idele K))
    (S : Finset (PrimeIdeal K)) (χ : RayChar K U) (s : ℝ) : ℂ :=
  ∑' 𝔭 : {𝔭 : PrimeIdeal K // 𝔭 ∉ S},
    χ.atPrime 𝔭.1 * (((Ideal.absNorm 𝔭.1.asIdeal : ℝ) ^ (-s) : ℝ) : ℂ)

/-- **The character-twisted prime sum** of a character of `Gal(L/K)`, over the primes outside the
modulus `S`. -/
noncomputable def artinPrimeSum (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] (S : Finset (PrimeIdeal K)) (χ : Gal(L/K) →* ℂˣ)
    (s : ℝ) : ℂ :=
  ∑' 𝔭 : {𝔭 : PrimeIdeal K // 𝔭 ∉ S},
    (χ (NK.Chebotarev.frobAtPrime (K := K) (L := L) 𝔭.1) : ℂ) *
      (((Ideal.absNorm 𝔭.1.asIdeal : ℝ) ^ (-s) : ℝ) : ℂ)

end NK.HeckeL
