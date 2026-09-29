import Mathlib.GroupTheory.GroupAction.Ring
import Mathlib.RingTheory.PowerSeries.Substitution

/-!
# The constant coefficient of a substituted power series

If `φ` is a power series with `constantCoeff φ = 0`, then substituting `φ` into
any power series `f` does not change its constant coefficient:

`constantCoeff (f.subst φ) = constantCoeff f`.

This follows from the formula
`constantCoeff (f.subst φ) = ∑ᶠ d, coeff d f • constantCoeff (φ ^ d)`
(Mathlib's `PowerSeries.constantCoeff_subst`): the `d = 0` term is
`coeff 0 f = constantCoeff f`, while for `d ≠ 0` the term vanishes because
`constantCoeff (φ ^ d) = (constantCoeff φ) ^ d = 0`.
-/

namespace Commons.RingTheory.PowerSeries

open _root_.PowerSeries

theorem constantCoeff_subst_of_constantCoeff_eq_zero {R : Type*} [CommRing R]
    {φ f : PowerSeries R} (h0 : PowerSeries.constantCoeff φ = 0) :
    PowerSeries.constantCoeff (f.subst φ) = PowerSeries.constantCoeff f := by
  have h0' : MvPowerSeries.constantCoeff φ = 0 := h0
  have hφ : HasSubst φ := HasSubst.of_constantCoeff_zero' h0
  rw [PowerSeries.constantCoeff_eq, PowerSeries.constantCoeff_subst hφ,
    finsum_eq_single _ 0]
  · simp [PowerSeries.constantCoeff_eq]
  · intro d hd
    rw [map_pow, h0', zero_pow hd, smul_zero]

end Commons.RingTheory.PowerSeries