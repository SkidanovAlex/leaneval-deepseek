import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.NK.GlobalCFT.IdeleClassGroup.count_spanSingleton_eq
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.GrunwaldEscapeCore

/-!
# Splitting off the `𝔭`-part of a global unit whose `𝔭`-adic exponent is divisible by `p`

For a number field `K`, a finite place `𝔭` of `K`, a natural number `p ≠ 0` and a unit `y ∈ Kˣ`
whose principal fractional ideal `(y)` has `𝔭`-adic exponent divisible by `p`, the unit can be
written `y = c ^ p · u` with `c ∈ K` and with `u ∈ Kˣ` a `𝔭`-adic unit (i.e. `𝔭`-adic exponent
`0`).

The point is that the `𝔭`-adic valuation of `K` is surjective (`𝔭.valuation_surjective`): picking
`c ∈ K` with `v_𝔭(c) = exp (-q)` for `q` the `𝔭`-adic exponent of `y` divided by `p` gives a
generator of the `𝔭`-part of `(y)`; the residual unit `u = y / c ^ p` is then a local unit, and the
dictionary between `FractionalIdeal.count` and the logarithm of the `𝔭`-adic valuation
(`NK.GlobalCFT.IdeleClassGroup.count_spanSingleton_eq`) converts the divisibility hypothesis into
the statement that all exponents are integral.

The primality of `p` is *not* used: only `p ≠ 0` is needed (the statement is required in this
generality by the Grünwald escape correction, where `p` is a prime but the split is formal).
-/

/-- **Splitting a `p`-th power off the `𝔭`-part of a global unit.**

If the `𝔭`-adic exponent of the principal fractional ideal `(y)` of `y ∈ Kˣ` is divisible by `p`,
then `y = c ^ p · u` with `c ∈ K` and `u ∈ Kˣ` a `𝔭`-adic unit. -/
theorem exists_pow_mul_unit_of_dvd_count {K : Type} [Field K] [NumberField K]
    (p : ℕ) (hp : p ≠ 0) (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (y : Kˣ)
    (h : (p : ℤ) ∣ FractionalIdeal.count K 𝔭
      (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers K)) (y : K))) :
    ∃ c : K, ∃ u : Kˣ, (y : K) = c ^ p * (u : K) ∧
      FractionalIdeal.count K 𝔭
        (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers K))
          (u : K)) = 0 := by
  classical
  -- write the `𝔭`-adic exponent of `y` as `p * q`
  obtain ⟨q, hq⟩ := h
  -- the `𝔭`-adic valuation of `K` is surjective: choose `c` with `v_𝔭 c = exp (-q)`
  obtain ⟨c, hc⟩ :=
    IsDedekindDomain.HeightOneSpectrum.valuation_surjective K 𝔭 (WithZero.exp (-q))
  have hcne : c ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hc
    exact WithZero.exp_ne_zero hc.symm
  -- the `𝔭`-adic exponent of `c` is `q`
  have hcountc : FractionalIdeal.count K 𝔭
      (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers K)) c) = q := by
    rw [NK.GlobalCFT.IdeleClassGroup.count_spanSingleton_eq (K := K) 𝔭 hcne, hc,
      WithZero.log_exp]
    ring
  -- hence the `𝔭`-adic exponent of `c ^ p` is `p * q`, i.e. that of `y`
  have hcountcp : FractionalIdeal.count K 𝔭
      (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers K))
        (c ^ p)) = (p : ℤ) * q := by
    rw [← FractionalIdeal.spanSingleton_pow, FractionalIdeal.count_pow, hcountc]
  -- the residual unit `u = y / c ^ p`
  set uval : K := (y : K) * ((c : K) ^ p)⁻¹ with huval
  have hune : uval ≠ 0 :=
    mul_ne_zero (Units.ne_zero y) (inv_ne_zero (pow_ne_zero p hcne))
  refine ⟨c, Units.mk0 uval hune, ?_, ?_⟩
  · -- `y = c ^ p * u`
    rw [Units.val_mk0, huval]
    rw [← mul_assoc, mul_comm ((c : K) ^ p) (y : K), mul_assoc,
      mul_inv_cancel₀ (pow_ne_zero p hcne), mul_one]
  · -- the `𝔭`-adic exponent of `u` is `0`
    rw [Units.val_mk0, huval]
    have hsp : FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers K))
        ((y : K) * ((c : K) ^ p)⁻¹)
        = FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers K)) (y : K)
          * (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers K))
              ((c : K) ^ p))⁻¹ := by
      rw [← FractionalIdeal.spanSingleton_mul_spanSingleton,
        ← FractionalIdeal.spanSingleton_inv K]
    rw [hsp, FractionalIdeal.count_mul K 𝔭
        (FractionalIdeal.spanSingleton_ne_zero_iff.mpr (Units.ne_zero y))
        (inv_ne_zero (FractionalIdeal.spanSingleton_ne_zero_iff.mpr (pow_ne_zero p hcne))),
      FractionalIdeal.count_inv, hcountcp, hq]
    ring

end Work.SSGRoute.GrunwaldEscapeCore
