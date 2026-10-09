/-
Work of the Neukirch–Uchida team: the analytic input of Čebotarev's theorem.

**The Artin factorization of the unramified Dedekind zeta product.**  For an abelian Galois
extension `L/K` of number fields, a finite set `S` of primes of `K` containing every prime which
ramifies in `L`, and a real `s > 1`, the product of the Artin `L`-series of all the characters of
`Gal(L/K)` equals the Euler product of the Dedekind zeta function of `L` with the Euler factors at
the primes above `S` deleted:

`∏_χ L(s, χ) = ∏_{𝔮 not over S} (1 - N𝔮^{-s})⁻¹`.

The proof is the classical computation of the local factors.  Both sides are rewritten as Euler
products over the primes `𝔭 ∉ S` of `K`:

* on the Artin side one interchanges the finite product over the characters with the Euler product
  and uses the orthogonality identity
  `∏_χ (1 - χ(σ) x)⁻¹ = ((1 - x ^ orderOf σ)⁻¹) ^ (|G| / orderOf σ)`
  (`prod_char_inv_one_sub_mul`, from `NK.HeckeL.Product.prod_monoidHom_one_sub_mul`);
* on the zeta side one groups the places of `L` by the place of `K` below them
  (`NK.HeckeL.Product.zetaUnramified_eq_tprod_fiber`, a lemma of the shared library).

At a prime `𝔭 ∉ S` the two local factors agree: `𝔭` is unramified, every prime of `L` above it has
inertia degree `f = orderOf (frobAtPrime 𝔭)`, so `N𝔮 = N𝔭 ^ f`, and the fundamental identity
`g · f = [L : K] = |Gal(L/K)|` identifies the number `g` of primes above `𝔭` with the exponent
`|Gal(L/K)| / f` (`NK.HeckeL.Product.zeta_eulerFactor_liesOver`).

The two explicitly used results of the shared library are those named above, together with
`NK.HeckeL.Series.hasProd_artinEulerFactor` (absolutely convergent Artin Euler products).
-/
import Mathlib
import Submission.NK.HeckeL.Product.prod_monoidHom_one_sub_mul
import Submission.NK.HeckeL.Product.artinLSeries_one
import Submission.NK.HeckeL.Product.zeta_eulerFactor_liesOver
import Submission.NK.HeckeL.Product.zetaUnramified_eq_tprod_fiber
import Submission.NK.HeckeL.Series.hasProd_artinEulerFactor
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open NumberField IsDedekindDomain Filter
open scoped BigOperators Classical

noncomputable section

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

namespace NK.HeckeL.Nonvanishing

/-- **Character orthogonality in the inverted form.**  For a finite abelian group `G`, an element
`σ` and a complex number `x`, the product over the characters of `G` of the inverted linear
factors `1 - χ(σ) x` is the `|G| / orderOf σ`-th power of `(1 - x ^ orderOf σ)⁻¹`.

This is `∏_χ (1 - χ(σ) x) = (1 - x ^ orderOf σ) ^ (|G| / orderOf σ)`
(`NK.HeckeL.Product.prod_monoidHom_one_sub_mul`), inverted. -/
theorem prod_char_inv_one_sub_mul (G : Type*) [CommGroup G] [Fintype G] (σ : G) (x : ℂ) :
    ∏ χ : G →* ℂˣ, (1 - (χ σ : ℂ) * x)⁻¹ =
      ((1 - x ^ orderOf σ)⁻¹) ^ (Nat.card G / orderOf σ) := by
  rw [Finset.prod_inv_distrib, NK.HeckeL.Product.prod_monoidHom_one_sub_mul, inv_pow]

theorem prod_artinLSeries_eq_zetaUnramified {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (S : Finset (NK.HeckeL.PrimeIdeal K)) (hcomm : ∀ a b : Gal(L/K), a * b = b * a)
    (hS : ∀ 𝔭 : NK.HeckeL.PrimeIdeal K, ¬ NK.HeckeL.IsUnramifiedIn (K := K) (L := L) 𝔭 → 𝔭 ∈ S)
    {s : ℝ} (hs : 1 < s) :
    ∏' χ : Gal(L/K) →* ℂˣ, NK.HeckeL.artinLSeries K L S χ s =
      NK.HeckeL.zetaUnramified K L S s := by
  classical
  -- the Galois group is abelian, so its group of characters is a finite abelian group
  letI : CommGroup Gal(L/K) := { (inferInstance : Group Gal(L/K)) with mul_comm := hcomm }
  -- **Artin side, step 1**: the (finite) product over the characters of the Euler products.
  have step1 : ∏' χ : Gal(L/K) →* ℂˣ, NK.HeckeL.artinLSeries K L S χ s
      = ∏ χ : Gal(L/K) →* ℂˣ,
          ∏' 𝔭 : {𝔭 : NK.HeckeL.PrimeIdeal K // 𝔭 ∉ S},
            NK.HeckeL.artinEulerFactor (K := K) (L := L) χ s 𝔭.1 := by
    rw [tprod_fintype]
    rfl
  -- **Artin side, step 2**: interchange the finite product over the characters with the Euler
  -- product over the primes; each Euler product converges absolutely for `s > 1`.
  have step2 : (∏ χ : Gal(L/K) →* ℂˣ,
          ∏' 𝔭 : {𝔭 : NK.HeckeL.PrimeIdeal K // 𝔭 ∉ S},
            NK.HeckeL.artinEulerFactor (K := K) (L := L) χ s 𝔭.1)
      = ∏' 𝔭 : {𝔭 : NK.HeckeL.PrimeIdeal K // 𝔭 ∉ S},
          ∏ χ : Gal(L/K) →* ℂˣ,
            NK.HeckeL.artinEulerFactor (K := K) (L := L) χ s 𝔭.1 :=
    (Multipliable.tprod_finsetProd (s := Finset.univ)
      (f := fun χ : Gal(L/K) →* ℂˣ =>
        fun 𝔭 : {𝔭 : NK.HeckeL.PrimeIdeal K // 𝔭 ∉ S} =>
          NK.HeckeL.artinEulerFactor (K := K) (L := L) χ s 𝔭.1)
      (fun χ _ =>
        (NK.HeckeL.Series.hasProd_artinEulerFactor (K := K) (L := L) S χ hs).multipliable)).symm
  -- **Artin side, step 3**: at each prime `𝔭 ∉ S` the product over the characters is the product
  -- over the primes of `L` above `𝔭` of the local Euler factors.
  have step3 : ∀ 𝔭 : {𝔭 : NK.HeckeL.PrimeIdeal K // 𝔭 ∉ S},
      (∏ χ : Gal(L/K) →* ℂˣ,
          NK.HeckeL.artinEulerFactor (K := K) (L := L) χ s 𝔭.1)
      = ∏ P : 𝔭.1.asIdeal.primesOver (𝓞 L),
          (1 - (((Ideal.absNorm P.1 : ℝ) ^ (-s) : ℝ) : ℂ))⁻¹ := by
    intro 𝔭
    -- a prime outside `S` is unramified, since `S` contains all the ramified primes
    have hunr : ∀ 𝔮 : NK.HeckeL.PrimeIdeal L, 𝔮.asIdeal.LiesOver 𝔭.1.asIdeal →
        𝔮.asIdeal.ramificationIdx (𝓞 K) = 1 := by
      intro 𝔮 h𝔮
      by_contra hne
      exact 𝔭.2 (hS 𝔭.1 fun hunr' => hne (hunr' 𝔮 h𝔮))
    -- character orthogonality at `𝔭` computed against the fundamental identity at `𝔭`
    refine (prod_char_inv_one_sub_mul (Gal(L/K))
      (NK.Chebotarev.frobAtPrime (K := K) (L := L) 𝔭.1)
      (((Ideal.absNorm 𝔭.1.asIdeal : ℝ) ^ (-s) : ℝ) : ℂ)).trans ?_
    exact (NK.HeckeL.Product.zeta_eulerFactor_liesOver (K := K) (L := L) 𝔭.1 hunr s).symm
  -- **Zeta side**: group the places of `L` outside `S` by the place of `K` below them.
  have step4 : NK.HeckeL.zetaUnramified K L S s
      = ∏' 𝔭 : {𝔭 : NK.HeckeL.PrimeIdeal K // 𝔭 ∉ S},
          ∏ P : 𝔭.1.asIdeal.primesOver (𝓞 L),
            (1 - (((Ideal.absNorm P.1 : ℝ) ^ (-s) : ℝ) : ℂ))⁻¹ :=
    NK.HeckeL.Product.zetaUnramified_eq_tprod_fiber (K := K) (L := L) S hs
  calc ∏' χ : Gal(L/K) →* ℂˣ, NK.HeckeL.artinLSeries K L S χ s
      = ∏ χ : Gal(L/K) →* ℂˣ,
          ∏' 𝔭 : {𝔭 : NK.HeckeL.PrimeIdeal K // 𝔭 ∉ S},
            NK.HeckeL.artinEulerFactor (K := K) (L := L) χ s 𝔭.1 := step1
    _ = ∏' 𝔭 : {𝔭 : NK.HeckeL.PrimeIdeal K // 𝔭 ∉ S},
          ∏ χ : Gal(L/K) →* ℂˣ,
            NK.HeckeL.artinEulerFactor (K := K) (L := L) χ s 𝔭.1 := step2
    _ = ∏' 𝔭 : {𝔭 : NK.HeckeL.PrimeIdeal K // 𝔭 ∉ S},
          ∏ P : 𝔭.1.asIdeal.primesOver (𝓞 L),
            (1 - (((Ideal.absNorm P.1 : ℝ) ^ (-s) : ℝ) : ℂ))⁻¹ := tprod_congr step3
    _ = NK.HeckeL.zetaUnramified K L S s := step4.symm

end NK.HeckeL.Nonvanishing
