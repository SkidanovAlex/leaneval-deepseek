import Mathlib
import Submission.Work.SSGRoute.GrunwaldEscapeCore.OrthImports
import Submission.Work.SSGRoute.GrunwaldEscapeCore.productFormula_sum
import Submission.Work.SSGRoute.n4_idele_factor
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.GrunwaldEscapeCore

set_option linter.style.haveILetI false

/-- **The Artin symbol of a fractional ideal, evaluated prime by prime.**  For an idèlic Artin map
`Φ` of a finite abelian extension `L/K` which is Frobenius-normalised at every prime unramified in
`L/K`, and a multiplicative character `χ` of `Gal(L/K)`, the value of `χ` on `Φ (fracIdele 𝔵)` is
the `ZMod p`-valued sum `∑_𝔮 count 𝔮 𝔵 · χ (Frob_𝔮)` over the primes occurring in `𝔵`
(`fracIdele 𝔵` is `ideleOfFun` of the exponents of `𝔵`, hence the product of the one-place idèles
`unifUnit 𝔮 ^ count 𝔮 𝔵` — `GrunwaldEscapeCore.ideleOfFun_eq_prod_onePlace`). -/
theorem kummerChar_artinSym_fracIdele_eq_sum
    (p : ℕ) [Fact p.Prime] {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (hcomm : ∀ a b : Gal(L/K), a * b = b * a)
    (Φ : NK.GlobalCFT.Idele K →* (L ≃ₐ[K] L))
    (hfrob : ∀ 𝔮 : NK.Chebotarev.PrimeIdeal K, NK.HeckeL.IsUnramifiedIn (K := K) (L := L) 𝔮 →
      Φ (NK.HeckeL.ideleOfPrime K 𝔮) = NK.Chebotarev.frobAtPrime (K := K) (L := L) 𝔮)
    (χ : Gal(L/K) →* Multiplicative (ZMod p))
    (𝔵 : FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers K)) K)
    (hunr : ∀ 𝔮 ∈ (FractionalIdeal.finite_factors 𝔵).toFinset,
      NK.HeckeL.IsUnramifiedIn (K := K) (L := L) 𝔮) :
    (χ (Φ (NK.NUV2.RouteB.RayModulus.fracIdele 𝔵))).toAdd =
      ∑ 𝔮 ∈ (FractionalIdeal.finite_factors 𝔵).toFinset,
        (FractionalIdeal.count K 𝔮 𝔵 : ZMod p) *
          (χ (NK.Chebotarev.frobAtPrime (K := K) (L := L) 𝔮)).toAdd := by
  classical
  -- the target of `Φ` is a commutative monoid, by hypothesis
  letI : CommMonoid (L ≃ₐ[K] L) :=
    { (inferInstance : Group (L ≃ₐ[K] L)) with mul_comm := hcomm }
  -- the (finite) support of `𝔵`
  set S : Finset (NK.Chebotarev.PrimeIdeal K) := (FractionalIdeal.finite_factors 𝔵).toFinset with hS
  have hmem : ∀ q : NK.Chebotarev.PrimeIdeal K,
      q ∈ S ↔ FractionalIdeal.count K q 𝔵 ≠ 0 := by
    intro q
    rw [hS]
    exact Set.Finite.mem_toFinset _
  have hsupp : ∀ q : NK.Chebotarev.PrimeIdeal K,
      q ∉ S → FractionalIdeal.count K q 𝔵 = 0 := by
    intro q hq
    by_contra h
    exact hq ((hmem q).mpr h)
  -- the Artin symbol of `fracIdele 𝔵` is the product of the Frobeniuses raised to the exponents
  have h1 : Φ (NK.NUV2.RouteB.RayModulus.fracIdele 𝔵) =
      ∏ q ∈ S,
        (NK.Chebotarev.frobAtPrime (K := K) (L := L) q) ^ (FractionalIdeal.count K q 𝔵) := by
    rw [show NK.NUV2.RouteB.RayModulus.fracIdele 𝔵 =
        NK.GlobalCFT.IdeleClassGroup.ideleOfFun K (fun q => FractionalIdeal.count K q 𝔵)
          (FractionalIdeal.finite_factors 𝔵) from rfl]
    rw [Work.SSGRoute.N4Escape.ideleOfFun_eq_prod_ideleOfPrime S
      (fun q => FractionalIdeal.count K q 𝔵) (FractionalIdeal.finite_factors 𝔵) hsupp, map_prod]
    refine Finset.prod_congr rfl fun q hq => ?_
    rw [map_zpow, hfrob q (hunr q hq)]
  -- applying the character and adding up the exponents
  rw [h1, map_prod,
    toAdd_prod_eq_sum p S (fun q =>
      χ (NK.Chebotarev.frobAtPrime (K := K) (L := L) q ^ FractionalIdeal.count K q 𝔵))]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [map_zpow, toAdd_zpow, zsmul_eq_mul]

end Work.SSGRoute.GrunwaldEscapeCore
