import Mathlib
import Submission.NK.CFTLib.ARL.isFrobAtPrime_zeta
import Submission.NK.Chebotarev.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.CFTLib.ArtinReciprocityIdeal.AuxFamily

open NumberField IsDedekindDomain
open scoped NumberField

/-- **The Frobenius at `p` raises a primitive `M`-th root of unity to the `N(p)`-th power.**
Generalises `NK.CFTLib.ARL.isFrobAtPrime_zeta` from the canonical root
`IsCyclotomicExtension.zeta` to an arbitrary primitive root. -/
theorem frobAtPrime_apply_primitiveRoot {K F : Type} [Field K] [NumberField K]
    [Field F] [NumberField F] [Algebra K F] [FiniteDimensional K F] [IsGalois K F]
    (M : ℕ) [NeZero M] [IsCyclotomicExtension {M} K F] (ζ : F) (hζ : IsPrimitiveRoot ζ M)
    (p : NK.Chebotarev.PrimeIdeal K) (σ : Gal(F/K))
    (hs : (M : NumberField.RingOfIntegers K) ∉ p.asIdeal)
    (hfrob : NK.Chebotarev.IsFrobAtPrime (K := K) (L := F) p σ) :
    σ ζ = ζ ^ p.asIdeal.absNorm := by
  obtain ⟨P, hP, hfrobP⟩ := hfrob
  -- the integral model of `ζ`, and compatibility with the structure map `𝓞 F → F`
  have hζint : IsPrimitiveRoot hζ.toInteger M := hζ.toInteger_isPrimitiveRoot
  have hcoe : algebraMap (NumberField.RingOfIntegers F) F hζ.toInteger = ζ := hζ.coe_toInteger
  -- `M` is invertible modulo `P`, because it is so modulo the prime `p` below it
  have hMP : (M : NumberField.RingOfIntegers F) ∉ P.asIdeal := by
    intro hmem
    apply hs
    have h' : algebraMap (NumberField.RingOfIntegers K) (NumberField.RingOfIntegers F)
        (M : NumberField.RingOfIntegers K) ∈ P.asIdeal := by
      rwa [map_natCast]
    exact (Ideal.mem_of_liesOver (P := P.asIdeal) (p := p.asIdeal)
      (x := (M : NumberField.RingOfIntegers K))).mpr h'
  -- the Frobenius congruence, upgraded to an equality on the integral primitive root
  have h1 : galRestrict (NumberField.RingOfIntegers K) K F (NumberField.RingOfIntegers F) σ
        hζ.toInteger
      = hζ.toInteger ^ Nat.card (NumberField.RingOfIntegers K ⧸
          P.asIdeal.under (NumberField.RingOfIntegers K)) :=
    AlgHom.IsArithFrobAt.apply_of_pow_eq_one hfrobP hζint.pow_eq_one hMP
  -- transport along `𝓞 F → F`
  have h2 := congrArg (algebraMap (NumberField.RingOfIntegers F) F) h1
  rw [map_pow, algebraMap_galRestrict_apply] at h2
  rw [hcoe, ← hP.over] at h2
  have habs : Nat.card (NumberField.RingOfIntegers K ⧸ p.asIdeal) = p.asIdeal.absNorm := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  rwa [habs] at h2

end NK.CFTLib.ArtinReciprocityIdeal.AuxFamily
