import Mathlib.Algebra.Polynomial.Div
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.RingTheory.SimpleRing.Principal

namespace Commons.RingTheory.PowerSeries

open Polynomial

/-- The constant coefficient of `Polynomial.aeval g W` is the constant coefficient of `W`,
whenever `g` has zero constant coefficient. -/
theorem constantCoeff_aeval_eq_coeff_zero {K : Type*} [Field K] (g : PowerSeries K)
    (hg0 : PowerSeries.constantCoeff g = 0) (W : Polynomial K) :
    PowerSeries.constantCoeff (Polynomial.aeval g W) = W.coeff 0 := by
  have h := Polynomial.map_aeval_eq_aeval_map (R := K) (S := PowerSeries K) (T := K) (U := K)
      (φ := RingHom.id K) (ψ := PowerSeries.constantCoeff) ?_ W g
  · rw [h, hg0, Polynomial.map_id]
    exact (Polynomial.coeff_zero_eq_aeval_zero (R := K) W).symm
  · ext r
    simp [PowerSeries.algebraMap_eq]

/-- Substitution of a nonzero power series with zero constant coefficient into a nonzero
polynomial gives a nonzero power series. -/
theorem subst_polynomial_ne_zero {K : Type*} [Field K] {g : PowerSeries K} (hg : g ≠ 0)
    (hg0 : PowerSeries.constantCoeff g = 0) {V : Polynomial K} (hV : V ≠ 0) :
    (V.toPowerSeries).subst g ≠ 0 := by
  have hcoe : (V.toPowerSeries).subst g = Polynomial.aeval g V := by
    rw [PowerSeries.subst_coe (PowerSeries.HasSubst.of_constantCoeff_zero' hg0) V]
  rw [hcoe]
  -- Write `V = X^t * W` with `t = V.natTrailingDegree`; then `W.coeff 0 = V.coeff t ≠ 0`.
  obtain ⟨W, hW⟩ : (Polynomial.X : Polynomial K) ^ V.natTrailingDegree ∣ V := by
    rw [Polynomial.X_pow_dvd_iff]
    intro d hd
    by_contra hc
    have := Polynomial.natTrailingDegree_le_of_ne_zero hc
    omega
  have hW0 : W.coeff 0 ≠ 0 := by
    have hcoeff : W.coeff 0 = V.coeff V.natTrailingDegree := by
      have := Polynomial.coeff_X_pow_mul W V.natTrailingDegree 0
      rw [← hW, zero_add] at this
      exact this.symm
    rw [hcoeff]
    exact Polynomial.coeff_natTrailingDegree_ne_zero.mpr hV
  -- `aeval g W` has nonzero constant coefficient, hence is nonzero.
  have hWaeval : Polynomial.aeval g W ≠ 0 := by
    intro h
    exact hW0 (by rw [← constantCoeff_aeval_eq_coeff_zero g hg0 W, h, map_zero])
  -- `aeval g V = g^t * aeval g W` with both factors nonzero in the domain `K⟦X⟧`.
  have hfac : Polynomial.aeval g V = g ^ V.natTrailingDegree * Polynomial.aeval g W := by
    conv_lhs => rw [hW]
    rw [Polynomial.aeval_mul, Polynomial.aeval_X_pow]
  rw [hfac]
  exact mul_ne_zero (pow_ne_zero _ hg) hWaeval

end Commons.RingTheory.PowerSeries