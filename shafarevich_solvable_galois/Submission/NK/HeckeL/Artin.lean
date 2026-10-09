/-
Work of the Neukirch–Uchida team: the analytic input of Čebotarev's theorem.

The Hecke `L`-series of a character of a ray class group agrees, under Artin reciprocity, with the
Artin `L`-series of the corresponding character of the Galois group.  On the Galois side the
`L`-series is an honest Euler product over the primes of the base field, which is what all the
analytic work of this chapter uses.  This file sets up that side and the dictionary between the
two, together with the two *named classical inputs* of the chapter:

* `NK.HeckeL.HeckeLRegularAtOne` — Hecke's theorem that the `L`-series of a non-trivial ray
  class character converges at `s = 1`;
-/
import Submission.NK.HeckeL.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open NumberField IsDedekindDomain
open scoped BigOperators Classical nonZeroDivisors Topology
open Filter

open NK.GlobalCFT (Idele IdeleClassGroup)

noncomputable section

namespace NK.HeckeL

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L]

/-! ## The Artin `L`-series -/

/-- The Euler factor `(1 - χ(Frob_𝔭) N𝔭^{-s})⁻¹` of the Artin `L`-series of `χ` at the prime
`𝔭`, where `Frob_𝔭` is the chosen Frobenius element at `𝔭`
(`NK.Chebotarev.frobAtPrime`). -/
noncomputable def artinEulerFactor (χ : Gal(L/K) →* ℂˣ) (s : ℝ) (𝔭 : PrimeIdeal K) : ℂ :=
  (1 - (χ (NK.Chebotarev.frobAtPrime (K := K) (L := L) 𝔭) : ℂ) *
    (((Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s) : ℝ) : ℂ))⁻¹

/-- **The Artin `L`-series** of a character of `Gal(L/K)`, as an Euler product over the primes of
`K` outside the modulus `S`:
`∏_{𝔭 ∉ S} (1 - χ(Frob_𝔭) N𝔭^{-s})⁻¹`.

For `S` containing the ramified primes this is the Artin `L`-series of `χ`; for `S` containing all
`𝔭` at which the ray class character is ramified it agrees with the Hecke `L`-series under Artin
reciprocity (`NK.HeckeL.heckeLSeries_eq_artinLSeries`). -/
noncomputable def artinLSeries (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] (S : Finset (PrimeIdeal K)) (χ : Gal(L/K) →* ℂˣ)
    (s : ℝ) : ℂ :=
  ∏' 𝔭 : {𝔭 : PrimeIdeal K // 𝔭 ∉ S}, artinEulerFactor (K := K) (L := L) χ s 𝔭.1

/-- The sum of the principal logarithms `-log (1 - χ(Frob_𝔭) N𝔭^{-s})` of the Euler factors of the
Artin `L`-series, over the primes outside the modulus `S`.

For `s > 1` the series converges absolutely (since `‖1 - (1 - z)‖ = ‖z‖ = N𝔭^{-s}`), and this is a
continuous branch of the logarithm of `artinLSeries K L S χ`: `exp` of it is the `L`-series
(`NK.HeckeL.exp_artinLogEulerProduct`).  It is the object whose `k = 1` part is the
character-twisted prime sum. -/
noncomputable def artinLogEulerProduct (K L : Type*) [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] (S : Finset (PrimeIdeal K))
    (χ : Gal(L/K) →* ℂˣ) (s : ℝ) : ℂ :=
  ∑' 𝔭 : {𝔭 : PrimeIdeal K // 𝔭 ∉ S},
    -Complex.log (1 - (χ (NK.Chebotarev.frobAtPrime (K := K) (L := L) 𝔭.1) : ℂ) *
      (((Ideal.absNorm 𝔭.1.asIdeal : ℝ) ^ (-s) : ℝ) : ℂ))

/-- The complex-valued version of a `ℂˣ`-valued character of the Galois group. -/
def galoisToComplex (χ : Gal(L/K) →* ℂˣ) : Gal(L/K) →* ℂ :=
  (Units.coeHom ℂ).comp χ

@[simp] theorem galoisToComplex_apply (χ : Gal(L/K) →* ℂˣ) (g : Gal(L/K)) :
    galoisToComplex χ g = (χ g : ℂ) := rfl

/-- Every value of a character of a finite Galois group is a root of unity, hence has norm `1`. -/
theorem norm_galoisToComplex_apply_eq_one [IsGalois K L] (χ : Gal(L/K) →* ℂˣ)
    (g : Gal(L/K)) : ‖galoisToComplex χ g‖ = 1 :=
  NK.Chebotarev.norm_monoidHom_units_apply_eq_one χ g

/-! ## The named inputs -/

/-- **Hecke's theorem (1917), as an explicit input of the chapter.**

For a character `χ` of the ray class group of `K` modulo `U`, and for a modulus `S`, the Hecke
`L`-series `∑_𝔞 χ([𝔞]) N𝔞^{-s}` (over the ideals coprime to `S`) has a finite limit as `s → 1⁺`.
Equivalently: the Hecke `L`-series has *no pole* at `s = 1`.

This is classical: the partial sums `∑_{N𝔞 ≤ X} χ(𝔞)` are `O(X^{1 - 1/[K:ℚ]})` (Hecke; see
Narkiewicz, *Elementary and analytic theory of algebraic numbers*, Ch. 7, §7.1), so the Dirichlet
series converges for `Re s > 1 - 1/[K:ℚ]`, in particular at `s = 1`.

It is the only analytic input of the chapter.  Everything else — the non-vanishing `L(1,χ) ≠ 0`,
the boundedness of the logarithmic prime sum, and Čebotarev for abelian extensions — is *derived*
from it. -/
structure HeckeLRegularAtOne (K : Type*) [Field K] [NumberField K] (U : Subgroup (Idele K))
    (S : Finset (PrimeIdeal K)) (χ : RayChar K U) : Type where
  /-- the value of the `L`-series at `s = 1` -/
  value : ℂ
  /-- the convergence of the `L`-series at `s = 1` -/
  tendsto : Filter.Tendsto (fun s : ℝ => heckeLSeries K U S χ s)
    (nhdsWithin (1 : ℝ) (Set.Ioi 1)) (𝓝 value)

/-- **Hecke's theorem on the Galois side**, i.e. the same input for the Artin `L`-series.  It is
equivalent to `NK.HeckeL.HeckeLRegularAtOne` under Artin reciprocity. -/
structure ArtinLRegularAtOne (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] (S : Finset (PrimeIdeal K)) (χ : Gal(L/K) →* ℂˣ) :
    Type where
  /-- the value of the `L`-series at `s = 1` -/
  value : ℂ
  /-- the convergence of the `L`-series at `s = 1` -/
  tendsto : Filter.Tendsto (fun s : ℝ => artinLSeries K L S χ s)
    (nhdsWithin (1 : ℝ) (Set.Ioi 1)) (𝓝 value)

end NK.HeckeL
