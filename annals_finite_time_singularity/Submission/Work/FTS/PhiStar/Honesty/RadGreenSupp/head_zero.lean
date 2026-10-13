import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set

namespace Work.FTS.PhiStar.Honesty.RadGreenSupp

/-- If `c` vanishes off `[a,b]` with `a > 0`, and `0 < z ≤ a`, then the head integral
`∫_0^z c t · t^e` vanishes: the integrand is zero on the open interval `(0,z)`, and the
remaining point `t = z` (which may lie in the support when `z = a`) is null. -/
theorem head_zero {c : ℝ → ℝ} {a b e z : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hsupp : ∀ t : ℝ, t ∉ Set.Icc a b → c t = 0) (hz : 0 < z) (hza : z ≤ a) :
    ∫ t in (0 : ℝ)..z, c t * t ^ e = 0 := by
  -- the integrand vanishes identically on the open interval `(0,z)`
  have hzero : ∀ t ∈ Set.Ioo (0 : ℝ) z, c t * t ^ e = 0 := by
    intro t ht
    have hta : t < a := lt_of_lt_of_le ht.2 hza
    rw [hsupp t (by intro h; exact (not_le.mpr hta) h.1), zero_mul]
  -- hence it vanishes a.e. on `uIoc 0 z`, the only possible exception being `t = z`
  have hne : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ z := by
    rw [MeasureTheory.ae_iff]
    simpa using measure_singleton z
  have hae : ∀ᵐ t ∂(volume : Measure ℝ),
      t ∈ Set.uIoc (0 : ℝ) z → c t * t ^ e = (0 : ℝ) := by
    filter_upwards [hne] with t htz htI
    rw [Set.uIoc_of_le (le_of_lt hz)] at htI
    exact hzero t ⟨htI.1, lt_of_le_of_ne htI.2 htz⟩
  rw [intervalIntegral.integral_congr_ae hae]
  simp

end Work.FTS.PhiStar.Honesty.RadGreenSupp
