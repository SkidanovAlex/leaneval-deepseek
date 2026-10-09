import Mathlib
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The `q`-adic `count` of a principal fractional ideal

For a number field `K`, a finite place `q` of `K` and a nonzero `a ∈ K`, the `q`-adic
`FractionalIdeal.count` of the principal fractional ideal `(a)` is the negative of the
`q`-adic valuation of `a`, in the additive `WithZero.log` coordinates.
-/

namespace NK.GlobalCFT.IdeleClassGroup

open scoped nonZeroDivisors
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

theorem count_spanSingleton_eq {K : Type*} [Field K] [NumberField K]
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) {a : K} (ha : a ≠ 0) :
    FractionalIdeal.count K q
        (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers K)) a) =
      -WithZero.log (IsDedekindDomain.HeightOneSpectrum.valuation K q a) := by
  obtain ⟨n, d, hnd⟩ :=
    IsLocalization.exists_mk'_eq (M := nonZeroDivisors (NumberField.RingOfIntegers K)) (S := K) a
  have hd0 : ((d : NumberField.RingOfIntegers K)) ≠ 0 := nonZeroDivisors.coe_ne_zero d
  have hn0 : n ≠ 0 := by
    rintro rfl
    rw [IsFractionRing.mk'_eq_div, map_zero, zero_div] at hnd
    exact ha hnd.symm
  have hI : FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers K)) a ≠ 0 :=
    FractionalIdeal.spanSingleton_ne_zero_iff.mpr ha
  have hker : ((algebraMap (NumberField.RingOfIntegers K) K)
        (d : NumberField.RingOfIntegers K))⁻¹ *
      (algebraMap (NumberField.RingOfIntegers K) K) n = a := by
    rw [mul_comm, ← div_eq_mul_inv, ← IsFractionRing.mk'_eq_div, hnd]
  have hI_eq : FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers K)) a =
      FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers K))
          ((algebraMap (NumberField.RingOfIntegers K) K)
            (d : NumberField.RingOfIntegers K))⁻¹ *
        ↑(Ideal.span {n} : Ideal (NumberField.RingOfIntegers K)) := by
    rw [← hker, ← FractionalIdeal.spanSingleton_mul_spanSingleton,
      ← FractionalIdeal.coeIdeal_span_singleton]
  rw [FractionalIdeal.count_well_defined K q hI hI_eq]
  have hval : q.valuation K a = WithZero.exp
      ((-((Associates.mk q.asIdeal).count (Associates.mk
            (Ideal.span {n} : Ideal (NumberField.RingOfIntegers K))).factors : ℤ)) -
        (-((Associates.mk q.asIdeal).count (Associates.mk
            (Ideal.span {(d : NumberField.RingOfIntegers K)} :
              Ideal (NumberField.RingOfIntegers K))).factors : ℤ))) := by
    rw [← hnd, q.valuation_of_mk', q.intValuation_if_neg hn0, q.intValuation_if_neg hd0,
      ← WithZero.exp_sub]
  rw [hval, WithZero.log_exp]
  ring

end NK.GlobalCFT.IdeleClassGroup
