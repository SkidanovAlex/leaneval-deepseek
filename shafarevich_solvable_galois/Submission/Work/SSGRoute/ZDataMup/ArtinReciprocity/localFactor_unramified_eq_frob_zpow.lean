import Mathlib
import Submission.Work.SSGRoute.ZDataMup.NKArtinUmbrella
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.ZDataMup.ArtinReciprocity

/-!
# The local factor of an idèlic Artin map at an unramified place

Let `L / K` be a finite Galois extension of number fields and `Φ : 𝕀 K →* Gal(L/K)` a monoid
homomorphism of the idèle group which

* kills the idèle norms `N_{L/K}` (`hN`), and
* carries the idèle of every **unramified** finite place `Q` to `frobAtPrime Q` (`hF`).

The main lemma `phi_onePlace_ofFinite_eq_frob_zpow_finVal` computes the value of `Φ` on a
one-place idèle at an unramified finite place `Q`: for every `b ∈ K_Qˣ`,

  `Φ (onePlace Q b) = (frobAtPrime Q) ^ finVal K Q b`,

where `finVal K Q b` is the (`Q`-adic) valuation of `b` in additive coordinates.

The proof decomposes `b = ϖ_Q ^ n · u` into a power of a local uniformiser `ϖ_Q` and a local unit
`u` (`NK.CFTLib.HR.exists_zpow_unifUnit_mul_mem_localUnits`), uses that at an unramified place
every local unit is a local norm (`NK.CFTLib.IdeleHasse.localUnits_le_localNormSubgroup_of_unramified`)
so that `Φ` kills `onePlace Q u`, and finally converts `onePlace Q ϖ_Q` into the prime idèle
`ideleOfPrime Q` (`NK.NUV2.ARL.onePlace_unifUnit_eq_ideleOfPrime`).

The requested statement `localFactor_unramified_eq_frob_zpow` is then the specialisation
`b = localImageAt (ofFinite Q) x` of the principal idèle of `x ∈ Kˣ`, whose valuation is the
`Q`-adic `FractionalIdeal.count` of the principal ideal `(x)`.
-/

/-- **The local factor at an unramified finite place, in valuation form.**  If `Φ` kills the idèle
norms and sends the prime idèle of the unramified place `Q` to `frobAtPrime Q`, then for every
`b ∈ K_Qˣ` the image of the one-place idèle `onePlace Q b` is `frobAtPrime Q` raised to the
`Q`-adic valuation of `b` (in additive coordinates, `finVal K Q b`). -/
theorem phi_onePlace_ofFinite_eq_frob_zpow_finVal {K L : Type} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    {Φ : NK.GlobalCFT.Idele K →* (L ≃ₐ[K] L)}
    (hN : ∀ y : NK.GlobalCFT.Idele L, Φ (NK.GlobalCFT.Idele.normIdeleHom K L y) = 1)
    (hF : ∀ (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)),
      NK.HeckeL.IsUnramifiedIn (K := K) (L := L) Q →
        Φ (NK.HeckeL.ideleOfPrime K Q) = NK.Chebotarev.frobAtPrime (K := K) (L := L) Q)
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hunr : NK.HeckeL.IsUnramifiedIn (K := K) (L := L) Q) (b : (Q.adicCompletion K)ˣ) :
    Φ (NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofFinite Q) b) =
      (NK.Chebotarev.frobAtPrime (K := K) (L := L) Q) ^ (NK.CFTLib.finVal K Q b) := by
  classical
  -- write `b = ϖ_Q ^ n · u` with `u` a local unit
  obtain ⟨n, u, hu, hzu⟩ := NK.CFTLib.HR.exists_zpow_unifUnit_mul_mem_localUnits (K := K) Q b
  -- the valuation of `b` is the exponent `n`
  have hfin : NK.CFTLib.finVal K Q b = n := by
    have huval : Valued.v ((u : (Q.adicCompletion K)ˣ) : Q.adicCompletion K) = 1 :=
      (NK.GlobalCFT.Place.mem_localUnits_ofFinite_iff_valued_eq_one).mp hu
    rw [NK.CFTLib.finVal, hzu, Units.val_mul, map_mul,
      NK.GlobalCFT.IdeleClassGroup.valued_unifUnit_zpow, huval, mul_one, WithZero.log_exp, neg_neg]
  -- `onePlace Q` is multiplicative in the value
  have hmap : NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofFinite Q)
      (NK.GlobalCFT.IdeleClassGroup.unifUnit K Q ^ n) =
      (NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofFinite Q)
        (NK.GlobalCFT.IdeleClassGroup.unifUnit K Q)) ^ n :=
    map_zpow (NK.CFTLib.IdeleHasse.onePlaceHom (K := K)
      (NK.GlobalCFT.Place.ofFinite Q)) (NK.GlobalCFT.IdeleClassGroup.unifUnit K Q) n
  -- the uniformiser is sent to the Frobenius
  have h1 : Φ (NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofFinite Q)
      (NK.GlobalCFT.IdeleClassGroup.unifUnit K Q)) =
      NK.Chebotarev.frobAtPrime (K := K) (L := L) Q := by
    rw [NK.NUV2.ARL.onePlace_unifUnit_eq_ideleOfPrime]
    exact hF Q hunr
  -- a local unit is a local norm, hence killed by `Φ`
  have h2 : Φ (NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofFinite Q) u) = 1 := by
    have hmem : NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofFinite Q) u
        ∈ NK.GlobalCFT.Idele.normImage K L :=
      (NK.CFTLib.IdeleHasse.onePlace_mem_normImage_iff (K := K) (L := L)
        (NK.GlobalCFT.Place.ofFinite Q) u).mpr
        (NK.CFTLib.IdeleHasse.localUnits_le_localNormSubgroup_of_unramified (K := K) (L := L)
          Q hunr hu)
    obtain ⟨y, hy⟩ := NK.GlobalCFT.Idele.mem_normImage.mp hmem
    rw [show NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofFinite Q) u =
        NK.GlobalCFT.Idele.normIdeleHom K L y from NK.GlobalCFT.Idele.ext fun v => hy v]
    exact hN y
  rw [hfin, hzu, NK.CFTLib.IdeleHasse.onePlace_mul, map_mul, hmap, map_zpow, h1, h2, mul_one]

theorem localFactor_unramified_eq_frob_zpow {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L] {Φ : NK.GlobalCFT.Idele K →* (L ≃ₐ[K] L)} (hN : ∀ y : NK.GlobalCFT.Idele L, Φ (NK.GlobalCFT.Idele.normIdeleHom K L y) = 1) (hF : ∀ (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)), NK.HeckeL.IsUnramifiedIn (K := K) (L := L) Q → Φ (NK.HeckeL.ideleOfPrime K Q) = NK.Chebotarev.frobAtPrime (K := K) (L := L) Q) (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) (hunr : NK.HeckeL.IsUnramifiedIn (K := K) (L := L) Q) (x : Kˣ) : Φ (NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofFinite Q) (NK.CFTLib.IdeleHasse.localImageAt (NK.GlobalCFT.Place.ofFinite Q) x)) = (NK.Chebotarev.frobAtPrime (K := K) (L := L) Q) ^ (FractionalIdeal.count K Q (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers K)) ((x : Kˣ) : K))) := by
  -- `localImageAt` at `Q` is the `Q`-component of the principal idèle
  have hloc : NK.CFTLib.IdeleHasse.localImageAt (NK.GlobalCFT.Place.ofFinite Q) x
      = (NK.GlobalCFT.Idele.principalIdele K x) (NK.GlobalCFT.Place.ofFinite Q) := rfl
  -- its valuation is the `count` of the principal ideal `(x)`
  have hexp : NK.CFTLib.finVal K Q ((NK.GlobalCFT.Idele.principalIdele K x) (NK.GlobalCFT.Place.ofFinite Q))
      = FractionalIdeal.count K Q (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers K)) ((x : Kˣ) : K)) := by
    rw [NK.CFTLib.finVal_principalIdele (F := K) (K := L) Q x,
      NK.GlobalCFT.IdeleClassGroup.count_spanSingleton_eq Q (Units.ne_zero x)]
    rfl
  rw [hloc, phi_onePlace_ofFinite_eq_frob_zpow_finVal hN hF Q hunr
    ((NK.GlobalCFT.Idele.principalIdele K x) (NK.GlobalCFT.Place.ofFinite Q)), hexp]

end Work.SSGRoute.ZDataMup.ArtinReciprocity
