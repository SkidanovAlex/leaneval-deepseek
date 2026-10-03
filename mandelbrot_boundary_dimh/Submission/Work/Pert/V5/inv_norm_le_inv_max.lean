import Mathlib

namespace Work.Pert.V5

/-- Pure real fact used in the geometric estimate: for `t ∈ [0, ℓ]`, the point
`min (max p 0) ℓ` (the projection of `p` onto `[0, ℓ]`) is no farther from `t`
than `p` is. -/
lemma abs_sub_clamp_le {p t ℓ : ℝ} (ht0 : 0 ≤ t) (htℓ : t ≤ ℓ) :
    |t - min (max p 0) ℓ| ≤ |t - p| := by
  have hℓ0 : 0 ≤ ℓ := le_trans ht0 htℓ
  rcases lt_or_ge p 0 with hp | hp
  · have hmax : max p 0 = 0 := max_eq_right (le_of_lt hp)
    have hmin : min 0 ℓ = 0 := min_eq_left hℓ0
    rw [hmax, hmin, sub_zero, abs_of_nonneg ht0]
    rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ t - p)]
    linarith
  · have hmax : max p 0 = p := max_eq_left hp
    rw [hmax]
    rcases lt_or_ge p ℓ with hlp | hlp
    · have hmin : min p ℓ = p := min_eq_left (le_of_lt hlp)
      rw [hmin]
    · have hmin : min p ℓ = ℓ := min_eq_right hlp
      rw [hmin, abs_of_nonpos (by linarith : t - ℓ ≤ 0),
        abs_of_nonpos (by linarith : t - p ≤ 0)]
      linarith

/-- For `‖v‖ = 1` the real part of `⋆v · (r + t·v)` equals `t + Re(⋆v · r)`, so
`|t + (⋆v · r).re| ≤ ‖r + t·v‖`. -/
lemma abs_re_add_le_norm (r v : ℂ) (t : ℝ) (hv : ‖v‖ = 1) :
    |t + (star v * r).re| ≤ ‖r + (t:ℂ) • v‖ := by
  have hvv : star v * v = 1 := by
    have := Complex.conj_mul' v
    rw [Complex.star_def, this, hv]
    norm_num
  have h2 : star v * ((t:ℂ) * v) = (t:ℂ) := by
    rw [← mul_assoc, mul_comm (star v) (t:ℂ), mul_assoc, hvv, mul_one]
  have key : star v * (r + (t:ℂ) • v) = (star v * r) + (t:ℂ) := by
    rw [smul_eq_mul, mul_add, h2]
  have hre : (star v * (r + (t:ℂ) • v)).re = (star v * r).re + t := by
    rw [key, Complex.add_re, Complex.ofReal_re]
  have h1 : |t + (star v * r).re| = |(star v * (r + (t:ℂ) • v)).re| := by
    rw [hre, add_comm]
  rw [h1]
  calc |(star v * (r + (t:ℂ) • v)).re| ≤ ‖star v * (r + (t:ℂ) • v)‖ := Complex.abs_re_le_norm _
    _ = ‖star v‖ * ‖r + (t:ℂ) • v‖ := norm_mul _ _
    _ = ‖v‖ * ‖r + (t:ℂ) • v‖ := by rw [norm_star]
    _ = ‖r + (t:ℂ) • v‖ := by rw [hv, one_mul]

theorem inv_norm_le_inv_max {r v : ℂ} {ℓ δ : ℝ} (hℓ : 0 ≤ ℓ) (hδ : 0 < δ) (hv : ‖v‖ = 1)
    (h : ∀ t ∈ Set.Icc (0:ℝ) ℓ, δ ≤ ‖r + (t : ℂ) • v‖) :
    ∀ t ∈ Set.Icc (0:ℝ) ℓ,
      1 / ‖r + (t : ℂ) • v‖ ≤ 1 / max δ |t - min (max (-(star v * r).re) 0) ℓ| := by
  intro t ht
  have hgδ : δ ≤ ‖r + (t:ℂ) • v‖ := h t ht
  obtain ⟨ht0, htℓ⟩ := ht
  have hgc : |t - min (max (-(star v * r).re) 0) ℓ| ≤ ‖r + (t:ℂ) • v‖ := by
    have hclamp := abs_sub_clamp_le (p := -(star v * r).re) ht0 htℓ
    have hb := abs_re_add_le_norm r v t hv
    calc |t - min (max (-(star v * r).re) 0) ℓ| ≤ |t - (-(star v * r).re)| := hclamp
      _ = |t + (star v * r).re| := by
            congr 1
            ring
      _ ≤ ‖r + (t:ℂ) • v‖ := hb
  have hMpos : 0 < max δ |t - min (max (-(star v * r).re) 0) ℓ| :=
    lt_of_lt_of_le hδ (le_max_left _ _)
  have hMle : max δ |t - min (max (-(star v * r).re) 0) ℓ| ≤ ‖r + (t:ℂ) • v‖ :=
    max_le hgδ hgc
  exact one_div_le_one_div_of_le hMpos hMle

end Work.Pert.V5
