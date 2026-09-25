import Mathlib

namespace Work.Tower.FrattiniLayer

theorem count_spanSingleton_eq_neg_log {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] (v : IsDedekindDomain.HeightOneSpectrum R) (x : K) :
    FractionalIdeal.count K v (FractionalIdeal.spanSingleton (nonZeroDivisors R) x) =
      -(v.valuation K x).log := by
  by_cases hx : x = 0
  · rw [hx, FractionalIdeal.spanSingleton_zero, FractionalIdeal.count_zero,
      map_zero, WithZero.log_zero, neg_zero]
  · obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective (nonZeroDivisors R) x
    have hr : r ≠ 0 := by
      rintro rfl
      exact hx (IsLocalization.mk'_zero s)
    have hs : (s : R) ≠ 0 := nonZeroDivisors.ne_zero s.property
    have hI : FractionalIdeal.spanSingleton (nonZeroDivisors R) (IsLocalization.mk' K r s) =
        FractionalIdeal.spanSingleton (nonZeroDivisors R) ((algebraMap R K) ↑s)⁻¹ *
          ((Ideal.span {r} : Ideal R) : FractionalIdeal (nonZeroDivisors R) K) := by
      rw [IsFractionRing.mk'_eq_div, div_eq_mul_inv,
        ← FractionalIdeal.spanSingleton_mul_spanSingleton,
        ← FractionalIdeal.coeIdeal_span_singleton, mul_comm]
    have hI0 : FractionalIdeal.spanSingleton (nonZeroDivisors R) (IsLocalization.mk' K r s) ≠ 0 :=
      by rwa [Ne, FractionalIdeal.spanSingleton_eq_zero_iff]
    rw [FractionalIdeal.count_well_defined K v hI0 hI,
      IsDedekindDomain.HeightOneSpectrum.valuation_of_mk',
      v.intValuation_if_neg hr,
      v.intValuation_if_neg hs,
      ← WithZero.exp_sub, WithZero.log_exp]
    ring

end Work.Tower.FrattiniLayer
