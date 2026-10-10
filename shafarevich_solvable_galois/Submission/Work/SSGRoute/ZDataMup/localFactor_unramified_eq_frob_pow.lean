import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Topology.Algebra.RestrictedProduct.Basic
import Submission.NK.CFTLib.HR.TransferAux.localLevelMap_injective_vanishing
import Submission.NK.CFTLib.HRdescent.localConditionCyclotomicPrime
import Submission.NK.HassePrinciple.ideleInclusion_smul_of_restrict
import Submission.NK.NUV2.ARL.HR.locUnits_inflation_eq_zero_iff
import Submission.NK.NUV2.ArtinBridge.kummerE_le_normImage_of_isGalois_exp
import Submission.NK.NUV2.ChebAux.Transfer.cycClassOf_translation
import Submission.NK.NUV2.ChebAux.Transfer.locUnits_res_inflation_eq_zero
import Submission.NK.NUV2.LC.localNormFinite_range_iff_val_pow
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The local factor at an unramified place is a power of the Frobenius

Let `L / K` be a finite Galois extension of number fields, `Q` a finite place of `K` unramified in
`L`, and `Φ : 𝕀_K →* Gal(L/K)` a homomorphism of the idèle group of `K` which

* kills the idèle norms `N_{L/K} 𝕀_L` (`hN`), and
* carries the idèle `ideleOfPrime Q` of an unramified prime to the chosen Frobenius element
  `Frob_Q` (`hF`).

The main result, `localFactor_unramified_eq_frob_pow`, computes the local factor
`Φ ∘ onePlace_Q : K_Qˣ →* Gal(L/K)` of such a `Φ` on the local image of a global unit `x ∈ Kˣ`:

  `Φ (onePlace_Q (x_Q)) = Frob_Q ^ (v_Q x)`,

where `v_Q x` is the exponent of `Q` in the principal fractional ideal `(x)`.

The arithmetic input is the structure of `K_Qˣ` at an *unramified* place: writing
`x_Q = ϖ_Q ^ n · u` with `u` a local unit,

* `ϖ_Q` is the prime idèle (`onePlace_unifUnit_eq_ideleOfPrime`), so `hF` gives `Frob_Q`;
* every local unit is a local norm (`localUnits_le_localNormSubgroup_of_unramified`), hence an
  idèle norm, hence killed by `Φ` via `hN`;
* the exponent `n` is the `Q`-adic valuation of `x`, i.e. the exponent of `Q` in `(x)`
  (`finVal_localImageAt_eq_count`).
-/

namespace Work.SSGRoute.ZDataMup

open scoped NumberField RestrictedProduct
open NumberField IsDedekindDomain

noncomputable section

/-- **The `Q`-adic valuation of the local image of `x ∈ Kˣ`.**  The `Q`-adic valuation of the
image of `x` in the completion `K_Q` is the exponent of `Q` in the principal fractional ideal
`(x)`: both are the negative of the logarithm of the `Q`-adic valuation of `x`. -/
theorem finVal_localImageAt_eq_count {K : Type} [Field K] [NumberField K]
    (Q : HeightOneSpectrum (𝓞 K)) (x : Kˣ) :
    NK.CFTLib.finVal K Q (NK.CFTLib.IdeleHasse.localImageAt (NK.GlobalCFT.Place.ofFinite Q) x) =
      FractionalIdeal.count K Q
        (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) ((x : Kˣ) : K)) := by
  rw [NK.CFTLib.finVal,
    NK.GlobalCFT.IdeleClassGroup.count_spanSingleton_eq Q (Units.ne_zero x)]
  congr 1
  simp only [NK.CFTLib.IdeleHasse.localImageAt, Units.coe_map]
  exact congrArg WithZero.log
    (Commons.NumberTheory.NumberField.val_algebraMap_adicCompletion_eq Q ((x : Kˣ) : K))

/-- **The local factor at an unramified finite place is the Frobenius raised to the `Q`-adic
valuation.**

Let `L / K` be a finite Galois extension of number fields, `Q` a finite place of `K` unramified in
`L`, and `Φ : 𝕀_K →* Gal(L/K)` a homomorphism killing the idèle norms `N_{L/K} 𝕀_L` and carrying
the idèle of the prime `Q` to the chosen Frobenius `Frob_Q`.  Then the local factor
`Φ ∘ onePlace_Q : K_Qˣ →* Gal(L/K)` at `Q` sends the local image of a global unit `x ∈ Kˣ` to
`Frob_Q ^ (v_Q x)`, where `v_Q x` is the exponent of `Q` in the principal fractional ideal `(x)`.

The proof writes `x_Q = ϖ_Q ^ n · u` with `u` a local unit.  The local units are local norms, hence
idèle norms, hence killed by `Φ`; the uniformiser is the prime idèle, which `hF` sends to `Frob_Q`;
and `n` is the `Q`-adic valuation of `x`. -/
theorem localFactor_unramified_eq_frob_pow {K L : Type} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    {Φ : NK.GlobalCFT.Idele K →* (L ≃ₐ[K] L)}
    (hN : ∀ y : NK.GlobalCFT.Idele L, Φ (NK.GlobalCFT.Idele.normIdeleHom K L y) = 1)
    (hF : ∀ Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      NK.HeckeL.IsUnramifiedIn (K := K) (L := L) Q →
      Φ (NK.HeckeL.ideleOfPrime K Q) = NK.Chebotarev.frobAtPrime (K := K) (L := L) Q)
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hunr : NK.HeckeL.IsUnramifiedIn (K := K) (L := L) Q) (x : Kˣ) :
    Φ (NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofFinite Q)
        (NK.CFTLib.IdeleHasse.localImageAt (NK.GlobalCFT.Place.ofFinite Q) x))
      = NK.Chebotarev.frobAtPrime (K := K) (L := L) Q ^
        (FractionalIdeal.count K Q (FractionalIdeal.spanSingleton
          (nonZeroDivisors (NumberField.RingOfIntegers K)) (x : K))) := by
  classical
  -- the local factor `ψ = Φ ∘ onePlace_Q : K_Qˣ →* Gal(L/K)`
  let ψ : (Q.adicCompletion K)ˣ →* (L ≃ₐ[K] L) :=
    Φ.comp (NK.CFTLib.IdeleHasse.onePlaceHom (NK.GlobalCFT.Place.ofFinite Q))
  have hψ_apply : ∀ a : (Q.adicCompletion K)ˣ,
      ψ a = Φ (NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofFinite Q) a) := fun a => rfl
  -- every local unit is a local norm, hence an idèle norm, hence killed by `Φ`
  have hψ_localUnits :
      ∀ u ∈ NK.GlobalCFT.Place.localUnits K (NK.GlobalCFT.Place.ofFinite Q), ψ u = 1 := by
    intro u hu
    rw [hψ_apply]
    have hsub := NK.CFTLib.IdeleHasse.localUnits_le_localNormSubgroup_of_unramified
      (K := K) (L := L) Q hunr hu
    have hmem : NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofFinite Q) u ∈
        NK.GlobalCFT.Idele.normImage K L :=
      (NK.CFTLib.IdeleHasse.onePlace_ofFinite_mem_normImage_iff (K := K) (L := L) Q u).mpr hsub
    obtain ⟨y, hy⟩ := NK.GlobalCFT.Idele.mem_normImage.mp hmem
    rw [show NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofFinite Q) u
        = NK.GlobalCFT.Idele.normIdeleHom K L y from NK.GlobalCFT.Idele.ext fun v => hy v]
    exact hN y
  -- the uniformiser is the prime idèle, and `hF` normalises it
  have hψ_unif : ψ (NK.GlobalCFT.IdeleClassGroup.unifUnit K Q)
      = NK.Chebotarev.frobAtPrime (K := K) (L := L) Q := by
    rw [hψ_apply, NK.NUV2.ARL.onePlace_unifUnit_eq_ideleOfPrime]
    exact hF Q hunr
  -- decompose the local image of `x` as a power of the uniformiser times a local unit
  obtain ⟨n, u, hu, hdec⟩ := NK.CFTLib.HR.exists_zpow_unifUnit_mul_mem_localUnits (K := K) Q
    (NK.CFTLib.IdeleHasse.localImageAt (NK.GlobalCFT.Place.ofFinite Q) x)
  have hψa : ψ (NK.CFTLib.IdeleHasse.localImageAt (NK.GlobalCFT.Place.ofFinite Q) x)
      = NK.Chebotarev.frobAtPrime (K := K) (L := L) Q ^ n := by
    rw [hdec, map_mul, map_zpow, hψ_unif, hψ_localUnits u hu, mul_one]
  -- and the exponent `n` is the `Q`-adic valuation of `x`
  have hn : n = NK.CFTLib.finVal K Q
      (NK.CFTLib.IdeleHasse.localImageAt (NK.GlobalCFT.Place.ofFinite Q) x) := by
    have hval : Valued.v (((NK.CFTLib.IdeleHasse.localImageAt (NK.GlobalCFT.Place.ofFinite Q) x :
        (NK.GlobalCFT.Place.localField K (NK.GlobalCFT.Place.ofFinite Q))ˣ)) :
          NK.GlobalCFT.Place.localField K (NK.GlobalCFT.Place.ofFinite Q))
        = WithZero.exp (-n) := by
      rw [hdec, Units.val_mul, map_mul, NK.GlobalCFT.IdeleClassGroup.valued_unifUnit_zpow,
        (NK.GlobalCFT.Place.mem_localUnits_ofFinite_iff_valued_eq_one).mp hu, mul_one]
    rw [NK.CFTLib.finVal, hval, WithZero.log_exp]
    ring
  rw [← hψ_apply (NK.CFTLib.IdeleHasse.localImageAt (NK.GlobalCFT.Place.ofFinite Q) x), hψa, hn,
    finVal_localImageAt_eq_count]

end

end Work.SSGRoute.ZDataMup
