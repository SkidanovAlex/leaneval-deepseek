/-
# `Work.FTS.PhiStar.Series.acoeff_zero_of_fstar` — the `m = 0` radial coefficient vanishes

The mode-`0` coefficient `acoeff α 0 F = radGreen α 0 (cmode 0 F)` vanishes as soon as the source
moment `Fstar F` does (on the positive half-line).

Indeed `cmode 0 F t = 0` for every `t > 0` (`eFam_zero_moment`, because the `m = 0` eigenfunction
is `e_0 = 3 sin θ cos θ` and the self-adjoint weight is `cos θ dθ`, so the `m = 0` coefficient is
`3·Fstar F z` up to the normalisation), and both integrals defining `radGreen α 0 c z` for
`z > 0` are taken over the region `t > 0` (`(0, z]` resp. `(z, ∞)`), where the integrand vanishes
pointwise.  The values of `cmode 0 F` at `t ≤ 0` are irrelevant.
-/
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.PhiStar.Series.eFam_zero_moment

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Series

theorem acoeff_zero_of_fstar (α : ℝ) (F : ℝ → ℝ → ℝ)
    (h : ∀ t, 0 < t → Work.Elliptic.Fstar F t = 0) :
    ∀ z, 0 < z → Work.FTS.PhiStar.Series.acoeff α 0 F z = 0 := by
  intro z hz
  have hcm : ∀ t, 0 < t → Work.FTS.PhiStar.Series.cmode 0 F t = 0 :=
    fun t ht => Work.FTS.PhiStar.Series.eFam_zero_moment F (h t ht)
  rw [Work.FTS.PhiStar.Series.acoeff, Work.FTS.PhiStar.Radial.radGreen]
  -- the integral `∫_0^z` lives on `Ioc 0 z ⊆ Ioi 0`
  have h1 : (∫ t in (0 : ℝ)..z,
      Work.FTS.PhiStar.Series.cmode 0 F t
        * t ^ ((2 * ((0 : ℕ) : ℝ) + 5) / α - 1)) = 0 := by
    rw [intervalIntegral.integral_of_le hz.le]
    trans ∫ t in Set.Ioc (0 : ℝ) z, (0 : ℝ)
    · apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
      intro t ht
      simp only [hcm t ht.1, zero_mul]
    · simp
  -- the integral `∫_{Ioi z}` lives on `Ioi z ⊆ Ioi 0`
  have h2 : (∫ t in Set.Ioi z,
      Work.FTS.PhiStar.Series.cmode 0 F t * t ^ (-(2 * ((0 : ℕ) : ℝ) / α) - 1)) = 0 := by
    trans ∫ t in Set.Ioi z, (0 : ℝ)
    · apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      simp only [hcm t (lt_trans hz ht), zero_mul]
    · simp
  rw [h1, h2]
  simp

end Work.FTS.PhiStar.Series
