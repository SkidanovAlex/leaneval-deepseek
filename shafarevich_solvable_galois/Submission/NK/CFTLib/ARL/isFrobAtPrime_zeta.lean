import Mathlib.RingTheory.Frobenius
import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
import Submission.NK.Chebotarev.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.CFTLib.ARL

/-- **The cyclotomic reciprocity law in Frobenius form.**

Let `L = K(ζ_n)` be a cyclotomic extension of the number field `K`, let `p` be a finite place of
`K` with `(n) ⊄ p` (i.e. `p` unramified in `K(ζ_n)`), and let `σ : Gal(L/K)` be a Frobenius at `p`,
meaning that some prime `P` of `𝓞 L` above `p` satisfies `σ x ≡ x ^ #(𝓞 K/p) (mod P)` for all
`x ∈ 𝓞 L`.  Then `σ` raises the chosen primitive `n`-th root of unity to the `#(𝓞 K/p)`-th power:

`σ (zeta n K L) = (zeta n K L) ^ #(𝓞 K/p)`.

The point is that the Frobenius *congruence* can be upgraded to an equality on roots of unity,
because the `n`-th roots of unity inject into `(𝓞 L/P)^×` when `(n) ⊄ P`
(`AlgHom.IsArithFrobAt.apply_of_pow_eq_one`). -/
theorem isFrobAtPrime_zeta {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L] (n : ℕ) [NeZero n]
    [IsCyclotomicExtension {n} K L] (p : NK.Chebotarev.PrimeIdeal K) (σ : Gal(L/K))
    (hs : (n : NumberField.RingOfIntegers K) ∉ p.asIdeal)
    (hfrob : NK.Chebotarev.IsFrobAtPrime (L := L) p σ) :
    σ (IsCyclotomicExtension.zeta n K L) =
      (IsCyclotomicExtension.zeta n K L) ^ Nat.card (NumberField.RingOfIntegers K ⧸ p.asIdeal) := by
  obtain ⟨P, hP, hfrobP⟩ := hfrob
  have hζ : IsPrimitiveRoot (IsCyclotomicExtension.zeta n K L) n :=
    IsCyclotomicExtension.zeta_spec n K L
  have hζint : IsPrimitiveRoot hζ.toInteger n := hζ.toInteger_isPrimitiveRoot
  have hcoe : algebraMap (NumberField.RingOfIntegers L) L hζ.toInteger =
      IsCyclotomicExtension.zeta n K L := hζ.coe_toInteger
  -- `P` does not divide `n`, since its restriction `p` does not.
  have hnP : (n : NumberField.RingOfIntegers L) ∉ P.asIdeal := by
    intro hmem
    apply hs
    have h' : algebraMap (NumberField.RingOfIntegers K) (NumberField.RingOfIntegers L)
        (n : NumberField.RingOfIntegers K) ∈ P.asIdeal := by
      rwa [map_natCast]
    exact (Ideal.mem_of_liesOver (P := P.asIdeal) (p := p.asIdeal)
      (x := (n : NumberField.RingOfIntegers K))).mpr h'
  -- The Frobenius congruence, applied to the integral primitive `n`-th root of unity.
  have h1 : galRestrict (NumberField.RingOfIntegers K) K L (NumberField.RingOfIntegers L) σ
        hζ.toInteger
      = hζ.toInteger ^ Nat.card (NumberField.RingOfIntegers K ⧸
          P.asIdeal.under (NumberField.RingOfIntegers K)) :=
    AlgHom.IsArithFrobAt.apply_of_pow_eq_one hfrobP hζint.pow_eq_one hnP
  -- Transport along `𝓞 L → L`.
  have h2 := congrArg (algebraMap (NumberField.RingOfIntegers L) L) h1
  rw [map_pow, algebraMap_galRestrict_apply] at h2
  rw [hcoe] at h2
  rw [← hP.over] at h2
  exact h2

end NK.CFTLib.ARL
