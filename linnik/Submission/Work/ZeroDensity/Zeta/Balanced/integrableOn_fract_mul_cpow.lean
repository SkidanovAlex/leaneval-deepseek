import Mathlib

namespace Work.ZeroDensity.Zeta.Balanced

/-- Norm of the coercion of a real number into `ℂ` (Mathlib only records the squared
version through `Complex.normSq`). -/
private lemma norm_ofReal_complex (r : ℝ) : ‖(r : ℂ)‖ = |r| := by simp

/-- The sawtooth defect `({u}² - {u})/2` is bounded by `1/8` in absolute value, so the
product with `u^{-s-2}` is dominated by the integrable function `u^{-Re s - 2}` on `(c, ∞)`.

The square-bracket polynomial `t ↦ (t² - t)/2` on `[0,1)` lies in `[-1/8, 0]`, hence its
absolute value is at most `1/8`; the complex power `u ^ (-s-2)` has modulus
`u ^ (-s.re - 2)`, and the latter is integrable on `Ioi c` because `-s.re - 2 < -1`
(here we use `0 < s.re`) and `c > 0`. -/
theorem integrableOn_fract_mul_cpow {s : ℂ} (hs : 0 < s.re) {c : ℝ} (hc : 0 < c) :
    MeasureTheory.IntegrableOn (fun u : ℝ => ((((Int.fract u) ^ 2 - Int.fract u) / 2 : ℝ) : ℂ) * (u : ℂ) ^ (-s - 2))
      (Set.Ioi c) := by
  have hg : MeasureTheory.IntegrableOn (fun u : ℝ => u ^ (-s.re - 2)) (Set.Ioi c) :=
    integrableOn_Ioi_rpow_of_lt (by linarith [hs]) hc
  have hgb : MeasureTheory.IntegrableOn (fun u : ℝ => (1 / 8 : ℝ) * u ^ (-s.re - 2)) (Set.Ioi c) :=
    hg.const_mul (1 / 8)
  refine MeasureTheory.Integrable.mono' hgb ?_ ?_
  · have h1 : MeasureTheory.AEStronglyMeasurable
        (fun u : ℝ => ((((Int.fract u) ^ 2 - Int.fract u) / 2 : ℝ) : ℂ))
        (MeasureTheory.volume.restrict (Set.Ioi c)) :=
      (Complex.measurable_ofReal.comp
        (((measurable_fract.pow_const 2).sub measurable_fract).div_const 2)).aestronglyMeasurable
    have h2 : MeasureTheory.AEStronglyMeasurable
        (fun u : ℝ => (u : ℂ) ^ (-s - 2)) (MeasureTheory.volume.restrict (Set.Ioi c)) :=
      (ContinuousOn.cpow_const Complex.continuous_ofReal.continuousOn (fun a ha => by
        left
        rw [Complex.ofReal_re]
        exact lt_trans hc ha)).aestronglyMeasurable measurableSet_Ioi
    exact h1.mul h2
  · filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with u hu
    have hu0 : (0 : ℝ) < u := lt_trans hc hu
    have hfr0 : (0 : ℝ) ≤ Int.fract u := Int.fract_nonneg u
    have hfr1 : Int.fract u < 1 := Int.fract_lt_one u
    rw [norm_mul, norm_ofReal_complex, Complex.norm_cpow_eq_rpow_re_of_pos hu0]
    have hre : (-s - 2).re = -s.re - 2 := by simp [Complex.sub_re]
    rw [hre]
    have hnn : (0 : ℝ) ≤ u ^ (-s.re - 2) := Real.rpow_nonneg (le_of_lt hu0) _
    have hbnd : |((Int.fract u) ^ 2 - Int.fract u) / 2| ≤ 1 / 8 := by
      rw [abs_le]
      constructor
      · nlinarith [sq_nonneg (Int.fract u - 1 / 2)]
      · nlinarith [hfr0, hfr1]
    exact mul_le_mul_of_nonneg_right hbnd hnn

end Work.ZeroDensity.Zeta.Balanced
