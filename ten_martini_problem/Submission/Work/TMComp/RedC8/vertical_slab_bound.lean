import Mathlib

open MeasureTheory
open scoped Interval

namespace Work.TMComp.RedC8

/-- Auxiliary bound: on the vertical segment `{c + y·I : |y| ≤ ε}` (with `c ∈ [a,b]`,
`c ≠ z.re`), the Cauchy integrand `(w - z)⁻¹ * g w` has, except on the single point
`y = 0` (which has measure zero), norm at most `M / |c - z.re|`; hence the interval
integral has norm at most `(M / |c - z.re|) · 2ε`.

The point `y = 0` is the only place where the hypothesis `w.im ≠ 0` of `hbound` can fail,
and it does not affect the value of the interval integral. -/
theorem vertical_slab_bound_aux {a b h M c : ℝ} {g : ℂ → ℂ} {z : ℂ}
    (hbound : ∀ w : ℂ, w.re ∈ Set.Icc a b → w.im ∈ Set.Icc (-h) h → w.im ≠ 0 → ‖g w‖ ≤ M)
    (hc : c ∈ Set.Icc a b) (hcne : c ≠ z.re)
    {ε : ℝ} (hε0 : 0 < ε) (hεh : ε < h) :
    ‖∫ y in (-ε)..ε, ((c : ℂ) + (y : ℂ) * Complex.I - z)⁻¹ * g ((c : ℂ) + (y : ℂ) * Complex.I)‖
      ≤ (M / |c - z.re| * 2) * ε := by
  have hCpos : 0 < |c - z.re| := abs_pos.mpr (sub_ne_zero.mpr hcne)
  have hae : ∀ᵐ y ∂(volume : Measure ℝ),
      y ∈ Ι (-ε) ε → ‖((c : ℂ) + (y : ℂ) * Complex.I - z)⁻¹ * g ((c : ℂ) + (y : ℂ) * Complex.I)‖
        ≤ M / |c - z.re| := by
    have hne0 : ∀ᵐ y ∂(volume : Measure ℝ), y ≠ 0 := by
      rw [MeasureTheory.ae_iff]
      simp
    filter_upwards [hne0] with y hy
    intro hyI
    have hyIoc : y ∈ Set.Ioc (-ε) ε := by
      have h : Ι (-ε) ε = Set.Ioc (-ε) ε := Set.uIoc_of_le (by linarith)
      rwa [h] at hyI
    set w : ℂ := (c : ℂ) + (y : ℂ) * Complex.I with hwdef
    have hwre : w.re = c := by simp [hwdef, Complex.add_re, Complex.mul_re]
    have hwim : w.im = y := by
      simp [hwdef, Complex.add_im, Complex.mul_im]
    have hyIcc : y ∈ Set.Icc (-h) h := by
      refine ⟨?_, ?_⟩
      · have : -h < y := lt_trans (by linarith) hyIoc.1
        linarith
      · have : y ≤ h := le_trans hyIoc.2 (le_of_lt hεh)
        linarith
    have hgw : ‖g w‖ ≤ M :=
      hbound w (by rw [hwre]; exact hc) (by rw [hwim]; exact hyIcc) (by rw [hwim]; exact hy)
    have hdist : |c - z.re| ≤ ‖w - z‖ := by
      have hre : (w - z).re = c - z.re := by rw [Complex.sub_re, hwre]
      calc |c - z.re| = |(w - z).re| := by rw [hre]
        _ ≤ ‖w - z‖ := Complex.abs_re_le_norm _
    calc ‖(w - z)⁻¹ * g w‖ ≤ ‖(w - z)⁻¹‖ * ‖g w‖ := norm_mul_le _ _
      _ = (1 / ‖w - z‖) * ‖g w‖ := by rw [norm_inv, one_div]
      _ ≤ (1 / |c - z.re|) * M := by
            apply mul_le_mul
            · exact one_div_le_one_div_of_le hCpos hdist
            · exact hgw
            · exact norm_nonneg _
            · positivity
      _ = M / |c - z.re| := by ring
  calc ‖∫ y in (-ε)..ε, ((c : ℂ) + (y : ℂ) * Complex.I - z)⁻¹ * g ((c : ℂ) + (y : ℂ) * Complex.I)‖
      ≤ (M / |c - z.re|) * |ε - (-ε)| := intervalIntegral.norm_integral_le_of_norm_le_const_ae hae
    _ = (M / |c - z.re| * 2) * ε := by
        rw [show ε - (-ε) = 2 * ε by ring, abs_of_pos (by linarith : (0:ℝ) < 2 * ε)]
        ring

theorem vertical_slab_bound {a b h M : ℝ} (hab : a < b) {g : ℂ → ℂ} {z : ℂ}
    (hzre : z.re ∈ Set.Ioo a b) (hzim : z.im ≠ 0)
    (hbound : ∀ w : ℂ, w.re ∈ Set.Icc a b → w.im ∈ Set.Icc (-h) h → w.im ≠ 0 → ‖g w‖ ≤ M)
    {ε : ℝ} (hε0 : 0 < ε) (hεh : ε < h) :
    ‖∫ y in (-ε)..ε, ((b : ℂ) + (y : ℂ) * Complex.I - z)⁻¹ * g ((b : ℂ) + (y : ℂ) * Complex.I)‖
      ≤ (M / (b - z.re) * 2) * ε ∧
    ‖∫ y in (-ε)..ε, ((a : ℂ) + (y : ℂ) * Complex.I - z)⁻¹ * g ((a : ℂ) + (y : ℂ) * Complex.I)‖
      ≤ (M / (z.re - a) * 2) * ε := by
  constructor
  · have h := vertical_slab_bound_aux (hbound := hbound) (c := b)
      ⟨hab.le, le_rfl⟩ (ne_of_gt hzre.2) hε0 hεh
    have hb1 : |b - z.re| = b - z.re := abs_of_pos (sub_pos.mpr hzre.2)
    rwa [hb1] at h
  · have h := vertical_slab_bound_aux (hbound := hbound) (c := a)
      ⟨le_rfl, hab.le⟩ (ne_of_lt hzre.1) hε0 hεh
    have hb2 : |a - z.re| = z.re - a := by
      rw [abs_of_neg (sub_neg.mpr hzre.1)]; ring
    rwa [hb2] at h

end Work.TMComp.RedC8
