import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Submission.Commons.RingTheory.PowerSeries.constantCoeff_subst_of_constantCoeff_eq_zero

namespace Commons.RingTheory.PowerSeries

/-- If `φ` is a nonzero power series over `ℚ` with vanishing constant coefficient, then the
substitution `f ↦ f.subst φ` is injective.

Indeed, writing `f = X ^ m * f₀` and `φ = X ^ v * φ₀` with `f₀`, `φ₀` of nonzero constant
coefficient (such decompositions always exist, with `m = f.order`, `v = φ.order`), one gets
`f.subst φ = X ^ (v * m) * (φ₀ ^ m * f₀.subst φ)`, where the second factor still has nonzero
constant coefficient. Since `ℚ⟦X⟧` is an integral domain and `X ≠ 0`, this is nonzero as soon as
`f ≠ 0`; hence `subst φ` has trivial kernel and is injective. -/
theorem subst_injective_of_constantCoeff_zero {φ : PowerSeries ℚ}
    (h0 : PowerSeries.constantCoeff φ = 0) (hne : φ ≠ 0) :
    Function.Injective (fun f : PowerSeries ℚ => f.subst φ) := by
  have hφ : PowerSeries.HasSubst φ := PowerSeries.HasSubst.of_constantCoeff_zero' h0
  have key : ∀ f : PowerSeries ℚ, f ≠ 0 → f.subst φ ≠ 0 := by
    intro f hf
    have hfdec : (PowerSeries.X : PowerSeries ℚ) ^ f.order.toNat * PowerSeries.divXPowOrder f
        = f := PowerSeries.X_pow_order_mul_divXPowOrder
    have hφdec : (PowerSeries.X : PowerSeries ℚ) ^ φ.order.toNat * PowerSeries.divXPowOrder φ
        = φ := PowerSeries.X_pow_order_mul_divXPowOrder
    have hf0 : PowerSeries.constantCoeff (PowerSeries.divXPowOrder f) ≠ 0 := by
      rw [PowerSeries.constantCoeff_divXPowOrder]; exact PowerSeries.coeff_order hf
    have hφ0 : PowerSeries.constantCoeff (PowerSeries.divXPowOrder φ) ≠ 0 := by
      rw [PowerSeries.constantCoeff_divXPowOrder]; exact PowerSeries.coeff_order hne
    have hdec : f.subst φ = φ ^ f.order.toNat * (PowerSeries.divXPowOrder f).subst φ := by
      conv_lhs => rw [← hfdec]
      rw [PowerSeries.subst_mul hφ, PowerSeries.subst_pow hφ, PowerSeries.subst_X hφ]
    have hpow : φ ^ f.order.toNat
        = (PowerSeries.X : PowerSeries ℚ) ^ (φ.order.toNat * f.order.toNat)
          * (PowerSeries.divXPowOrder φ) ^ f.order.toNat := by
      conv_lhs => rw [← hφdec]
      rw [mul_pow, ← pow_mul]
    have hconst : PowerSeries.constantCoeff ((PowerSeries.divXPowOrder φ) ^ f.order.toNat
        * (PowerSeries.divXPowOrder f).subst φ) ≠ 0 := by
      rw [map_mul, map_pow, constantCoeff_subst_of_constantCoeff_eq_zero h0]
      exact mul_ne_zero (pow_ne_zero _ hφ0) hf0
    have hne0 : (PowerSeries.divXPowOrder φ) ^ f.order.toNat
        * (PowerSeries.divXPowOrder f).subst φ ≠ 0 := fun hh => hconst (by rw [hh, map_zero])
    rw [hdec, hpow, mul_assoc]
    exact mul_ne_zero (pow_ne_zero _ PowerSeries.X_ne_zero) hne0
  intro f g hfg
  by_contra h
  have hsub : (f - g).subst φ = 0 := by
    rw [PowerSeries.subst_sub hφ, sub_eq_zero]
    exact hfg
  exact key (f - g) (sub_ne_zero.mpr h) hsub

end Commons.RingTheory.PowerSeries