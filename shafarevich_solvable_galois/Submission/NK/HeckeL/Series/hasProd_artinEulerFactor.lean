import Mathlib
import Submission.NK.HeckeL.Zeta
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.HeckeL.Series

open Filter Topology
open scoped BigOperators Classical

/-- **The Artin Euler product converges.**

For `s > 1` and any character `χ` of `Gal(L/K)` the family of Euler factors
`(1 - χ(Frob_𝔭) · N𝔭^{-s})⁻¹` over the primes `𝔭 ∉ S` is multipliable, with product the Artin
`L`-series `NK.HeckeL.artinLSeries K L S χ s`.

The point is that every value of a character of the (finite, by finite-dimensionality of `L/K`)
group `Gal(L/K)` has norm `1`, so the factor `z_𝔭 = χ(Frob_𝔭) · N𝔭^{-s}` has norm `N𝔭^{-s} < 1`.
Hence `1 - z_𝔭 ≠ 0` for every `𝔭` and `∑_𝔭 ‖z_𝔭‖ = ∑_𝔭 N𝔭^{-s}` converges for `s > 1`
(`Commons.NumberTheory.NumberField.Set.summable_primeIdealZetaSum`), which gives the convergence
of `∏_𝔭 (1 - z_𝔭)` and hence of its reciprocal. -/
theorem hasProd_artinEulerFactor {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] (S : Finset (NK.HeckeL.PrimeIdeal K))
    (χ : Gal(L/K) →* ℂˣ) {s : ℝ} (hs : 1 < s) :
    HasProd (fun 𝔭 : {𝔭 : NK.HeckeL.PrimeIdeal K // 𝔭 ∉ S} =>
      NK.HeckeL.artinEulerFactor (K := K) (L := L) χ s 𝔭.1)
      (NK.HeckeL.artinLSeries K L S χ s) := by
  classical
  have hspos : (0 : ℝ) < s := lt_trans zero_lt_one hs
  -- The values of `χ` are roots of unity, hence of norm one.
  have hchi : ∀ g : Gal(L/K), ‖(χ g : ℂ)‖ = 1 := fun g =>
    NK.Chebotarev.norm_monoidHom_units_apply_eq_one χ g
  -- The factor `1 - z_𝔭` of the Euler product.
  set z : {𝔭 : NK.HeckeL.PrimeIdeal K // 𝔭 ∉ S} → ℂ := fun 𝔭 =>
    (χ (NK.Chebotarev.frobAtPrime (K := K) (L := L) 𝔭.1) : ℂ) *
      (((Ideal.absNorm 𝔭.1.asIdeal : ℝ) ^ (-s) : ℝ) : ℂ) with hz
  -- Its norm is the prime-ideal weight `N𝔭^{-s}`.
  have hznorm : ∀ 𝔭 : {𝔭 : NK.HeckeL.PrimeIdeal K // 𝔭 ∉ S},
      ‖z 𝔭‖ = (Ideal.absNorm 𝔭.1.asIdeal : ℝ) ^ (-s) := by
    intro 𝔭
    simp only [hz, norm_mul, hchi (NK.Chebotarev.frobAtPrime (K := K) (L := L) 𝔭.1), one_mul,
      Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg (Ideal.absNorm 𝔭.1.asIdeal)) (-s))]
  -- Summability of the prime-ideal weights, outside `S`.
  have hsumN : Summable (fun 𝔭 : {𝔭 : NK.HeckeL.PrimeIdeal K // 𝔭 ∉ S} =>
      (Ideal.absNorm 𝔭.1.asIdeal : ℝ) ^ (-s)) :=
    (Commons.NumberTheory.NumberField.Set.summable_primeIdealZetaSum (K := K) hs).subtype
      (fun 𝔭 : NK.HeckeL.PrimeIdeal K => 𝔭 ∉ S)
  have hsumz : Summable (fun 𝔭 : {𝔭 : NK.HeckeL.PrimeIdeal K // 𝔭 ∉ S} => ‖z 𝔭‖) :=
    hsumN.congr fun 𝔭 => (hznorm 𝔭).symm
  -- Convergence of the product `∏ (1 - z_𝔭)`.
  have hsum_neg : Summable (fun 𝔭 : {𝔭 : NK.HeckeL.PrimeIdeal K // 𝔭 ∉ S} => ‖-(z 𝔭)‖) := by
    simpa using hsumz
  have hmult : Multipliable (fun 𝔭 : {𝔭 : NK.HeckeL.PrimeIdeal K // 𝔭 ∉ S} => 1 + (-(z 𝔭))) :=
    multipliable_one_add_of_summable hsum_neg
  -- No factor vanishes: `‖z_𝔭‖ = N𝔭^{-s} < 1`.
  have hne : ∀ 𝔭 : {𝔭 : NK.HeckeL.PrimeIdeal K // 𝔭 ∉ S}, 1 + (-(z 𝔭)) ≠ 0 := by
    intro 𝔭 hzero
    have hz1 : z 𝔭 = 1 := by
      have h1 : -(z 𝔭) = -1 := eq_neg_of_add_eq_zero_right hzero
      simpa using (neg_inj.mp h1)
    have hnorm := hznorm 𝔭
    rw [hz1, norm_one] at hnorm
    have hlt := Commons.NumberTheory.NumberField.DedekindZeta.rpow_neg_absNorm_primeIdeal_lt_one
      (K := K) hspos 𝔭.1
    linarith
  have hprodne : (∏' 𝔭 : {𝔭 : NK.HeckeL.PrimeIdeal K // 𝔭 ∉ S}, (1 + (-(z 𝔭)))) ≠ 0 :=
    tprod_one_add_ne_zero_of_summable hne hsum_neg
  -- Convergence of the reciprocal Euler product.
  have hmultinv : Multipliable (fun 𝔭 : {𝔭 : NK.HeckeL.PrimeIdeal K // 𝔭 ∉ S} =>
      (1 + (-(z 𝔭)))⁻¹) := (hmult.hasProd.inv₀ hprodne).multipliable
  -- This is the family of Euler factors of the Artin `L`-series.
  have hmult' : Multipliable (fun 𝔭 : {𝔭 : NK.HeckeL.PrimeIdeal K // 𝔭 ∉ S} =>
      NK.HeckeL.artinEulerFactor (K := K) (L := L) χ s 𝔭.1) :=
    hmultinv.congr fun 𝔭 => by
      simp only [hz, NK.HeckeL.artinEulerFactor, sub_eq_add_neg]
  simpa only [NK.HeckeL.artinLSeries] using hmult'.hasProd

end NK.HeckeL.Series
