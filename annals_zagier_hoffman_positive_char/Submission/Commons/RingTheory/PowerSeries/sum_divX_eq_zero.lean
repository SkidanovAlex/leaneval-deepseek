import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

namespace Commons.RingTheory.PowerSeries

/-- If `∑ p j * g j = 0` in `K⟦X⟧` and every `p j` has zero constant coefficient,
then also `∑ (p j).divX * g j = 0`: the two sums differ by the nonzerodivisor `X`. -/
theorem sum_divX_eq_zero {K : Type*} [Field K] {ι : Type*} [Fintype ι]
    {p : ι → Polynomial K} {g : ι → PowerSeries K} (h0 : ∀ j, (p j).coeff 0 = 0)
    (h : ∑ j, ((p j : Polynomial K) : PowerSeries K) * g j = 0) :
    ∑ j, (((p j).divX : Polynomial K) : PowerSeries K) * g j = 0 := by
  -- Since the constant coefficient of `p j` vanishes, `X * (p j).divX = p j`.
  have hXdiv : ∀ j, Polynomial.X * (p j).divX = p j := by
    intro j
    have := Polynomial.X_mul_divX_add (p j)
    rw [h0 j, Polynomial.C_0, add_zero] at this
    exact this
  -- Multiply the target sum by `X`; each term becomes `p j * g j`, so the total is `0`.
  have hXS : (PowerSeries.X : PowerSeries K) *
      (∑ j, (((p j).divX : Polynomial K) : PowerSeries K) * g j)
      = ∑ j, ((p j : Polynomial K) : PowerSeries K) * g j := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    calc (PowerSeries.X : PowerSeries K) *
            ((((p j).divX : Polynomial K) : PowerSeries K) * g j)
        = (((Polynomial.X : Polynomial K) : PowerSeries K)) *
            ((((p j).divX : Polynomial K) : PowerSeries K) * g j) := by
              rw [Polynomial.coe_X]
      _ = (((Polynomial.X : Polynomial K) : PowerSeries K) *
            (((p j).divX : Polynomial K) : PowerSeries K)) * g j := by
              rw [mul_assoc]
      _ = (((Polynomial.X * (p j).divX : Polynomial K)) : PowerSeries K) * g j := by
              rw [← Polynomial.coe_mul]
      _ = ((p j : Polynomial K) : PowerSeries K) * g j := by
              rw [hXdiv j]
  have hXS0 : (PowerSeries.X : PowerSeries K) *
      (∑ j, (((p j).divX : Polynomial K) : PowerSeries K) * g j) = 0 := by
    rw [hXS, h]
  -- `X` is not a zero divisor in `K⟦X⟧`.
  rcases mul_eq_zero.mp hXS0 with hx | hs
  · exact absurd hx PowerSeries.X_ne_zero
  · exact hs

end Commons.RingTheory.PowerSeries