import Mathlib
import Submission.Work.EQ.FatouDefs

/-!
# The tail of the angular Poisson-kernel derivative integral

`Work.EQ.pkS r s = -(d/ds) pk r s = 2 r (1 - r²) sin s / (1 - 2 r cos s + r²)²` is the
(negated) `s`-derivative of the angular Poisson kernel `pk r s = (1 - r²)/(1 - 2 r cos s + r²)`.
As `r → 1⁻` the kernel concentrates at `s = 0`: for any fixed `δ > 0` the integral
`∫_δ^π pkS r s · 2s ds` tends to `0`.

The proof is a direct uniform bound: on `s ∈ (δ, π]` and `r ≥ 1/2` the denominator
`1 - 2 r cos s + r²` is bounded below by `1 - cos δ > 0`, so
`|pkS r s| ≤ 2 (1 - r²)/(1 - cos δ)²`, and hence
`|∫_δ^π pkS r s · 2s ds| ≤ (4π (1-r²)/(1-cos δ)²) · |π - δ| → 0`.
-/

namespace Work.EQ.Fatou

open MeasureTheory Set Filter

/-- `1 - cos δ > 0` for `0 < δ < π`. -/
private lemma one_sub_cos_delta_pos {δ : ℝ} (hδ : 0 < δ) (hδπ : δ < Real.pi) :
    0 < 1 - Real.cos δ := by
  have h := Real.cos_lt_cos_of_nonneg_of_le_pi (le_refl (0:ℝ)) (le_of_lt hδπ) hδ
  simpa using h

/-- On `s ∈ (δ, π]` (with `0 < δ < π`) and `r ≥ 1/2` the denominator of `pkS` is bounded
below by `1 - cos δ`. -/
private lemma one_sub_cos_le_denom (r s δ : ℝ) (hδ : 0 < δ) (hδπ : δ < Real.pi)
    (hr : 1/2 ≤ r) (hs : s ∈ Set.Ioc δ Real.pi) :
    1 - Real.cos δ ≤ 1 - 2 * r * Real.cos s + r ^ 2 := by
  have hδ0 : 0 ≤ δ := le_of_lt hδ
  have hdeltas : δ ≤ s := le_of_lt hs.1
  have hsle : s ≤ Real.pi := hs.2
  have hrpos : 0 < r := by linarith
  have hcos : Real.cos s ≤ Real.cos δ :=
    Real.cos_le_cos_of_nonneg_of_le_pi hδ0 hsle hdeltas
  have hcpos : 0 < 1 - Real.cos δ := one_sub_cos_delta_pos hδ hδπ
  have h1 : 1 - 2 * r * Real.cos δ ≤ 1 - 2 * r * Real.cos s := by nlinarith [hcos, hrpos]
  have h2 : 2 * r * (1 - Real.cos δ) ≤ 1 - 2 * r * Real.cos δ + r ^ 2 := by
    nlinarith [sq_nonneg (1 - r)]
  have h3 : 1 - Real.cos δ ≤ 2 * r * (1 - Real.cos δ) := by nlinarith [hcpos, hr]
  linarith

/-- Pointwise bound for `pkS` away from the singular direction. -/
private lemma abs_pkS_le (r s δ : ℝ) (hδ : 0 < δ) (hδπ : δ < Real.pi)
    (hr : 1/2 ≤ r) (hr1 : r < 1) (hs : s ∈ Set.Ioc δ Real.pi) :
    |Work.EQ.pkS r s| ≤ 2 * (1 - r ^ 2) / (1 - Real.cos δ) ^ 2 := by
  have hcpos : 0 < 1 - Real.cos δ := one_sub_cos_delta_pos hδ hδπ
  have hD := one_sub_cos_le_denom r s δ hδ hδπ hr hs
  have hDpos : 0 < 1 - 2 * r * Real.cos s + r ^ 2 := lt_of_lt_of_le hcpos hD
  have hδ0 : 0 ≤ δ := le_of_lt hδ
  have hs0 : 0 ≤ s := le_trans hδ0 (le_of_lt hs.1)
  have hsin0 : 0 ≤ Real.sin s := Real.sin_nonneg_of_mem_Icc ⟨hs0, hs.2⟩
  have hsin1 : Real.sin s ≤ 1 := Real.sin_le_one s
  have hrpos : 0 < r := by linarith
  have hr1' : r ≤ 1 := le_of_lt hr1
  have hone : 0 ≤ 1 - r ^ 2 := by nlinarith
  have hnum_nonneg : 0 ≤ 2 * r * (1 - r ^ 2) * Real.sin s :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hrpos.le) hone) hsin0
  have hnum_le : 2 * r * (1 - r ^ 2) * Real.sin s ≤ 2 * (1 - r ^ 2) := by
    have h2r : 0 ≤ 2 * r * (1 - r ^ 2) := mul_nonneg (mul_nonneg (by norm_num) hrpos.le) hone
    have hstep : 2 * r * (1 - r ^ 2) * Real.sin s ≤ 2 * r * (1 - r ^ 2) * 1 :=
      mul_le_mul_of_nonneg_left hsin1 h2r
    have hstep2 : 2 * r * (1 - r ^ 2) ≤ 2 * (1 - r ^ 2) := by nlinarith [hone, hr1', hrpos]
    linarith
  have hden_le : (1 - Real.cos δ) ^ 2 ≤ (1 - 2 * r * Real.cos s + r ^ 2) ^ 2 :=
    pow_le_pow_left₀ hcpos.le hD 2
  unfold Work.EQ.pkS
  rw [abs_div, abs_of_nonneg hnum_nonneg, abs_of_pos (pow_pos hDpos 2)]
  calc 2 * r * (1 - r ^ 2) * Real.sin s / (1 - 2 * r * Real.cos s + r ^ 2) ^ 2
      ≤ 2 * (1 - r ^ 2) / (1 - 2 * r * Real.cos s + r ^ 2) ^ 2 :=
        div_le_div_of_nonneg_right hnum_le (pow_pos hDpos 2).le
    _ ≤ 2 * (1 - r ^ 2) / (1 - Real.cos δ) ^ 2 :=
        div_le_div_of_nonneg_left (by linarith) (pow_pos hcpos 2) hden_le

/-- The integrand `s ↦ pkS r s · 2s` is uniformly bounded by `4π (1-r²)/(1-cos δ)²`
on `(δ, π]`. -/
private lemma norm_pkS_mul_two_le (r s δ : ℝ) (hδ : 0 < δ) (hδπ : δ < Real.pi)
    (hr : 1/2 ≤ r) (hr1 : r < 1) (hs : s ∈ Set.Ioc δ Real.pi) :
    ‖Work.EQ.pkS r s * (2 * s)‖ ≤ 4 * Real.pi * (1 - r ^ 2) / (1 - Real.cos δ) ^ 2 := by
  have hkey := abs_pkS_le r s δ hδ hδπ hr hr1 hs
  have hδ0 : 0 ≤ δ := le_of_lt hδ
  have hs0 : 0 ≤ s := le_trans hδ0 (le_of_lt hs.1)
  have hsπ : s ≤ Real.pi := hs.2
  have hb1nn : 0 ≤ 2 * (1 - r ^ 2) / (1 - Real.cos δ) ^ 2 := by
    apply div_nonneg _ (by positivity)
    have hr1' : r ≤ 1 := le_of_lt hr1
    nlinarith
  have h2s : |2 * s| ≤ 2 * Real.pi := by
    rw [abs_of_nonneg (by linarith)]
    linarith
  rw [Real.norm_eq_abs, abs_mul]
  calc |Work.EQ.pkS r s| * |2 * s|
      ≤ (2 * (1 - r ^ 2) / (1 - Real.cos δ) ^ 2) * (2 * Real.pi) :=
        mul_le_mul hkey h2s (abs_nonneg _) hb1nn
    _ = 4 * Real.pi * (1 - r ^ 2) / (1 - Real.cos δ) ^ 2 := by ring

theorem pkS_tail_tendsto (δ : ℝ) (hδ : 0 < δ) (hδπ : δ < Real.pi) :
    Filter.Tendsto (fun r : ℝ => ∫ s in δ..Real.pi, Work.EQ.pkS r s * (2 * s))
      (nhdsWithin 1 (Set.Iio 1)) (nhds 0) := by
  have hcpos : 0 < 1 - Real.cos δ := one_sub_cos_delta_pos hδ hδπ
  set C : ℝ := 4 * Real.pi / (1 - Real.cos δ) ^ 2 * |Real.pi - δ| with hC
  -- the eventual pointwise bound on the integral
  have hpoint : ∀ᶠ r in nhdsWithin (1:ℝ) (Set.Iio 1),
      ‖∫ s in δ..Real.pi, Work.EQ.pkS r s * (2 * s)‖ ≤ C * (1 - r ^ 2) := by
    have hr_lt : ∀ᶠ r in nhdsWithin (1:ℝ) (Set.Iio 1), r < 1 := by
      filter_upwards [self_mem_nhdsWithin] with r hr using hr
    have hr_gt : ∀ᶠ r in nhdsWithin (1:ℝ) (Set.Iio 1), (1:ℝ)/2 ≤ r := by
      filter_upwards [nhdsWithin_le_nhds
        (Ioi_mem_nhds (show (1:ℝ)/2 < 1 by norm_num))] with r hr
      exact le_of_lt hr
    filter_upwards [hr_lt, hr_gt] with r hr1 hr12
    have hbd : ∀ s ∈ Set.uIoc δ Real.pi,
        ‖Work.EQ.pkS r s * (2 * s)‖ ≤ 4 * Real.pi * (1 - r ^ 2) / (1 - Real.cos δ) ^ 2 := by
      intro s hs
      rw [Set.uIoc_of_le (le_of_lt hδπ)] at hs
      exact norm_pkS_mul_two_le r s δ hδ hδπ hr12 hr1 hs
    calc ‖∫ s in δ..Real.pi, Work.EQ.pkS r s * (2 * s)‖
        ≤ (4 * Real.pi * (1 - r ^ 2) / (1 - Real.cos δ) ^ 2) * |Real.pi - δ| :=
          intervalIntegral.norm_integral_le_of_norm_le_const hbd
      _ = C * (1 - r ^ 2) := by rw [hC]; ring
  -- the bound tends to zero
  have htend : Filter.Tendsto (fun r : ℝ => C * (1 - r ^ 2))
      (nhdsWithin (1:ℝ) (Set.Iio 1)) (nhds 0) := by
    have hcont : Continuous fun r : ℝ => C * (1 - r ^ 2) := by fun_prop
    have h1 : Filter.Tendsto (fun r : ℝ => C * (1 - r ^ 2)) (nhds (1:ℝ)) (nhds 0) := by
      have h0 : C * (1 - (1:ℝ) ^ 2) = 0 := by ring
      simpa [h0] using (hcont.continuousAt (x := (1:ℝ))).tendsto
    exact h1.mono_left nhdsWithin_le_nhds
  rw [tendsto_zero_iff_norm_tendsto_zero]
  exact squeeze_zero' (Eventually.of_forall fun r => norm_nonneg _) hpoint htend

end Work.EQ.Fatou
