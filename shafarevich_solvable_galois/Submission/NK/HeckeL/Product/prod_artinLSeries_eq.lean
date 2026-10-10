import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Submission.NK.HeckeL.Product.prod_monoidHom_one_sub_mul
import Submission.NK.HeckeL.Product.zetaUnramified_eq_tprod_fiber
import Submission.NK.HeckeL.Product.zeta_eulerFactor_liesOver
import Submission.NK.HeckeL.Series.hasProd_artinEulerFactor
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open NumberField IsDedekindDomain Filter
open scoped BigOperators Classical

noncomputable section

namespace NK.HeckeL.Product

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]

/-! ## The character product, in the inverted form

The Artin Euler factor at `𝔭` is the *inverse* of a linear factor in `χ(Frob_𝔭)`, so what the
product over all characters needs is the inverted form of the classical orthogonality identity
`∏_χ (1 - χ(σ) x) = (1 - x ^ orderOf σ) ^ (|G| / orderOf σ)`
(`NK.HeckeL.Product.prod_monoidHom_one_sub_mul`). -/
theorem prod_char_inv_one_sub_mul_aux (G : Type*) [CommGroup G] [Fintype G] (σ : G) (x : ℂ) :
    ∏ χ : G →* ℂˣ, (1 - (χ σ : ℂ) * x)⁻¹ =
      ((1 - x ^ orderOf σ)⁻¹) ^ (Nat.card G / orderOf σ) := by
  rw [Finset.prod_inv_distrib, prod_monoidHom_one_sub_mul, inv_pow]

/-! ## The Artin side

The finite product over the characters of `Gal(L/K)` is exchanged with the Euler product over the
primes outside `S` (`Multipliable.tprod_finsetProd`), and the inner finite product over the
characters is evaluated by `prod_char_inv_one_sub_mul_aux`.  For every `𝔭 ∉ S` the value
`Frob_𝔭` of the chosen Frobenius has order `f`, the inertia degree of `𝔭`, and the exponent
`Nat.card Gal(L/K) / orderOf (frobAtPrime 𝔭)` is therefore the number of primes of `L` above `𝔭`
(`NK.HeckeL.Product.zeta_eulerFactor_liesOver` compares the two local factors). -/
theorem artinLSeries_prod_eq (S : Finset (NK.HeckeL.PrimeIdeal K))
    (hcomm : ∀ a b : Gal(L/K), a * b = b * a)
    (_hS : ∀ 𝔭 : NK.HeckeL.PrimeIdeal K,
      ¬ NK.HeckeL.IsUnramifiedIn (K := K) (L := L) 𝔭 → 𝔭 ∈ S)
    {s : ℝ} (hs : 1 < s) :
    ∏' χ : Gal(L/K) →* ℂˣ, NK.HeckeL.artinLSeries K L S χ s =
      ∏' 𝔭 : {𝔭 : NK.HeckeL.PrimeIdeal K // 𝔭 ∉ S},
        ((1 - (((Ideal.absNorm 𝔭.1.asIdeal : ℝ) ^ (-s) : ℝ) : ℂ) ^
          orderOf (NK.Chebotarev.frobAtPrime (K := K) (L := L) 𝔭.1))⁻¹) ^
        (Nat.card Gal(L/K) / orderOf (NK.Chebotarev.frobAtPrime (K := K) (L := L) 𝔭.1)) := by
  classical
  letI : CommGroup Gal(L/K) := { (inferInstance : Group Gal(L/K)) with mul_comm := hcomm }
  -- the norm of the local weight `N𝔭^{-s}` is `< 1`, so the Euler factors do not vanish
  have hx : (∀ 𝔭 : {𝔭 : NK.HeckeL.PrimeIdeal K // 𝔭 ∉ S},
      ‖(((Ideal.absNorm 𝔭.1.asIdeal : ℝ) ^ (-s) : ℝ) : ℂ)‖ < 1) := by
    intro 𝔭
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
    exact Commons.NumberTheory.NumberField.DedekindZeta.rpow_neg_absNorm_primeIdeal_lt_one
      (K := K) (lt_trans zero_lt_one hs) 𝔭.1
  -- the outer product, over the (finite) group of characters, is a finite product
  have h1 : ∏' χ : Gal(L/K) →* ℂˣ, NK.HeckeL.artinLSeries K L S χ s
      = ∏ χ : Gal(L/K) →* ℂˣ, ∏' 𝔭 : {𝔭 : NK.HeckeL.PrimeIdeal K // 𝔭 ∉ S},
          NK.HeckeL.artinEulerFactor (K := K) (L := L) χ s 𝔭.1 := by
    rw [tprod_eq_prod (s := Finset.univ) (fun b hb => (hb (Finset.mem_univ b)).elim)]
    exact Finset.prod_congr rfl (fun χ _ => rfl)
  rw [h1]
  -- exchange the finite product over the characters with the Euler product
  rw [← Multipliable.tprod_finsetProd (s := Finset.univ)
      (f := fun χ : Gal(L/K) →* ℂˣ => fun 𝔭 : {𝔭 : NK.HeckeL.PrimeIdeal K // 𝔭 ∉ S} =>
        NK.HeckeL.artinEulerFactor (K := K) (L := L) χ s 𝔭.1)
      (fun χ _ =>
        (NK.HeckeL.Series.hasProd_artinEulerFactor (K := K) (L := L) S χ hs).multipliable)]
  -- evaluate the finite product over the characters at each prime
  refine tprod_congr fun 𝔭 => ?_
  show ∏ χ : Gal(L/K) →* ℂˣ,
      (1 - (χ (NK.Chebotarev.frobAtPrime (K := K) (L := L) 𝔭.1) : ℂ) *
        (((Ideal.absNorm 𝔭.1.asIdeal : ℝ) ^ (-s) : ℝ) : ℂ))⁻¹ = _
  exact prod_char_inv_one_sub_mul_aux (Gal(L/K))
    (NK.Chebotarev.frobAtPrime (K := K) (L := L) 𝔭.1)
    (((Ideal.absNorm 𝔭.1.asIdeal : ℝ) ^ (-s) : ℝ) : ℂ)

/-! ## The zeta side

Group the Euler product of `L` over the primes above each prime of `K` outside `S`
(`NK.HeckeL.Product.zetaUnramified_eq_tprod_fiber`), then evaluate the finite product over the
primes above `𝔭` (`NK.HeckeL.Product.zeta_eulerFactor_liesOver`). -/
theorem zetaUnramified_prod_eq (S : Finset (NK.HeckeL.PrimeIdeal K))
    (hS : ∀ 𝔭 : NK.HeckeL.PrimeIdeal K,
      ¬ NK.HeckeL.IsUnramifiedIn (K := K) (L := L) 𝔭 → 𝔭 ∈ S)
    {s : ℝ} (hs : 1 < s) :
    NK.HeckeL.zetaUnramified K L S s =
      ∏' 𝔭 : {𝔭 : NK.HeckeL.PrimeIdeal K // 𝔭 ∉ S},
        ((1 - (((Ideal.absNorm 𝔭.1.asIdeal : ℝ) ^ (-s) : ℝ) : ℂ) ^
          orderOf (NK.Chebotarev.frobAtPrime (K := K) (L := L) 𝔭.1))⁻¹) ^
        (Nat.card Gal(L/K) / orderOf (NK.Chebotarev.frobAtPrime (K := K) (L := L) 𝔭.1)) := by
  rw [zetaUnramified_eq_tprod_fiber (K := K) (L := L) S hs]
  refine tprod_congr fun 𝔭 => ?_
  -- a prime outside `S` is unramified, by hypothesis on `S`
  have hunr : NK.HeckeL.IsUnramifiedIn (K := K) (L := L) 𝔭.1 := by
    by_contra h
    exact 𝔭.2 (hS 𝔭.1 h)
  exact zeta_eulerFactor_liesOver (K := K) (L := L) 𝔭.1 hunr s

/-- **The Artin factorization of the unramified Dedekind zeta product.**

For a finite Galois extension `L/K` of number fields whose Galois group is abelian, a modulus `S`
containing all the ramified primes, and a real `s > 1`, the product of the Artin `L`-series of all
the characters of `Gal(L/K)` equals the Euler product of the Dedekind zeta function of `L` with the
Euler factors at the primes above `S` deleted.

Both sides are computed as Euler products over the primes `𝔭 ∉ S` of `K`, and at such a `𝔭` the
local factor of the Artin side is

`∏_χ (1 - χ(Frob_𝔭) N𝔭^{-s})⁻¹ = ((1 - (N𝔭^{-s}) ^ f)⁻¹) ^ (|Gal(L/K)| / f)`

(`NK.HeckeL.Product.prod_char_inv_one_sub_mul_aux`, `f = orderOf (Frob_𝔭)`), which equals

`∏_{𝔮 | 𝔭} (1 - N𝔮^{-s})⁻¹ = ((1 - (N𝔭^{-s}) ^ f)⁻¹) ^ g`

because every `𝔮 | 𝔭` is unramified with inertia degree `f`, so `N𝔮 = N𝔭 ^ f`, and the fundamental
identity `g · f = [L : K]` gives `g = |Gal(L/K)| / f`
(`NK.HeckeL.Product.zeta_eulerFactor_liesOver`). -/
theorem prod_artinLSeries_eq {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (S : Finset (NK.HeckeL.PrimeIdeal K)) (hcomm : ∀ a b : Gal(L/K), a * b = b * a)
    (hS : ∀ 𝔭 : NK.HeckeL.PrimeIdeal K, ¬ NK.HeckeL.IsUnramifiedIn (K := K) (L := L) 𝔭 → 𝔭 ∈ S)
    {s : ℝ} (hs : 1 < s) :
    ∏' χ : Gal(L/K) →* ℂˣ, NK.HeckeL.artinLSeries K L S χ s =
      NK.HeckeL.zetaUnramified K L S s :=
  (artinLSeries_prod_eq S hcomm hS hs).trans (zetaUnramified_prod_eq S hS hs).symm

end NK.HeckeL.Product
