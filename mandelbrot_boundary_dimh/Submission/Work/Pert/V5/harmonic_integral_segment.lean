import Mathlib
import Submission.Work.Pert.V5.iInf_norm_sub_int_eq_min
import Submission.Work.Pert.V5.re_part_mem_floor_min
import Submission.Work.Pert.V5.line_integral_inv_norm_le

open MeasureTheory

/-!
# `Work.Pert.V5.harmonic_integral_segment`

Integral bound for the reciprocal of the distance to the lattice `ℤ ⊂ ℂ`, along a straight
unit-speed segment of length `ℓ ≤ 1/2` that keeps distance at least `δ` from every integer:

`∫ t in 0..ℓ, 1 / ⨅ k : ℤ, ‖(p + t·v) - k‖ ≤ 4 (1 + log (2 + ℓ/δ))`.

Route.  Write `γ t = p + t·v` and `m = ⌊min (γ 0).re (γ ℓ).re⌋`.  Since `Re γ` is affine with
`|Re (γ t) - Re (γ 0)| ≤ t ‖v‖ ≤ ℓ ≤ 1/2`, the real part of `γ t` stays in `[m, m + 3/2]`, so
the nearest integer to `Re (γ t)` is `m` or `m + 1` and consequently

`⨅ k, ‖γ t - k‖ = min ‖γ t - m‖ ‖γ t - (m+1)‖`,

hence `1 / ⨅ k, ‖γ t - k‖ ≤ 1/‖γ t - m‖ + 1/‖γ t - (m+1)‖`.  Integrating and using the
single-integer estimate `∫ 0..ℓ 1/‖r + t·v‖ ≤ 2 (1 + log (2 + ℓ/δ))` twice gives the claim.
-/

namespace Work.Pert.V5

theorem harmonic_integral_segment {p v : ℂ} {δ ℓ : ℝ} (hδ : 0 < δ) (hℓ : 0 < ℓ)
    (hv : ‖v‖ = 1)
    (hclear : ∀ t ∈ Set.Icc (0:ℝ) ℓ, ∀ k : ℤ, δ ≤ ‖(p + (t : ℂ) • v) - (k : ℂ)‖)
    (hshort : ℓ ≤ 1 / 2) :
    ∫ t in (0:ℝ)..ℓ, 1 / (⨅ k : ℤ, ‖(p + (t : ℂ) • v) - (k : ℂ)‖)
      ≤ 4 * (1 + Real.log (2 + ℓ / δ)) := by
  have hℓ0 : (0:ℝ) ≤ ℓ := le_of_lt hℓ
  let m : ℤ := ⌊min p.re (p.re + ℓ * v.re)⌋
  -- Step 1: the integrand is, pointwise on `[0,ℓ]`, `1 / min (‖γ t - m‖) (‖γ t - (m+1)‖)`.
  have hcongr : (∫ t in (0:ℝ)..ℓ, 1 / (⨅ k : ℤ, ‖(p + (t : ℂ) • v) - (k : ℂ)‖))
      = ∫ t in (0:ℝ)..ℓ,
          1 / min (‖(p + (t : ℂ) • v) - (m : ℂ)‖) (‖(p + (t : ℂ) • v) - ((m + 1 : ℤ) : ℂ)‖) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hℓ0] at ht
    show 1 / (⨅ k : ℤ, ‖(p + (t : ℂ) • v) - (k : ℂ)‖)
      = 1 / min (‖(p + (t : ℂ) • v) - (m : ℂ)‖) (‖(p + (t : ℂ) • v) - ((m + 1 : ℤ) : ℂ)‖)
    have hb := re_part_mem_floor_min (p := p) (v := v) (ℓ := ℓ) hℓ0 hshort hv ht
    rw [iInf_norm_sub_int_eq_min hb.1 hb.2]
  -- Step 2: pointwise domination by the sum of the two reciprocals.
  have hpt : ∀ t ∈ Set.Icc (0:ℝ) ℓ,
      1 / min (‖(p + (t : ℂ) • v) - (m : ℂ)‖) (‖(p + (t : ℂ) • v) - ((m + 1 : ℤ) : ℂ)‖)
        ≤ 1 / ‖(p + (t : ℂ) • v) - (m : ℂ)‖
          + 1 / ‖(p + (t : ℂ) • v) - ((m + 1 : ℤ) : ℂ)‖ := by
    intro t ht
    have hA0 : 0 < ‖(p + (t : ℂ) • v) - (m : ℂ)‖ := lt_of_lt_of_le hδ (hclear t ht m)
    have hB0 : 0 < ‖(p + (t : ℂ) • v) - ((m + 1 : ℤ) : ℂ)‖ :=
      lt_of_lt_of_le hδ (hclear t ht (m + 1))
    rcases le_total (‖(p + (t : ℂ) • v) - (m : ℂ)‖)
      (‖(p + (t : ℂ) • v) - ((m + 1 : ℤ) : ℂ)‖) with h | h
    · rw [min_eq_left h]
      have := one_div_pos.mpr hB0
      linarith
    · rw [min_eq_right h]
      have := one_div_pos.mpr hA0
      linarith
  -- Step 3: continuity / integrability of the three auxiliary functions.
  have hcontA : ContinuousOn (fun t : ℝ => ‖(p + (t : ℂ) • v) - (m : ℂ)‖)
      (Set.uIcc (0:ℝ) ℓ) := by
    have : Continuous (fun t : ℝ => (p + (t : ℂ) • v) - (m : ℂ)) := by fun_prop
    exact this.continuousOn.norm
  have hcontB : ContinuousOn (fun t : ℝ => ‖(p + (t : ℂ) • v) - ((m + 1 : ℤ) : ℂ)‖)
      (Set.uIcc (0:ℝ) ℓ) := by
    have : Continuous (fun t : ℝ => (p + (t : ℂ) • v) - ((m + 1 : ℤ) : ℂ)) := by fun_prop
    exact this.continuousOn.norm
  have hIntA : IntervalIntegrable (fun t : ℝ => 1 / ‖(p + (t : ℂ) • v) - (m : ℂ)‖)
      volume (0:ℝ) ℓ := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div continuousOn_const hcontA
    intro t ht
    rw [Set.uIcc_of_le hℓ0] at ht
    exact ne_of_gt (lt_of_lt_of_le hδ (hclear t ht m))
  have hIntB : IntervalIntegrable (fun t : ℝ => 1 / ‖(p + (t : ℂ) • v) - ((m + 1 : ℤ) : ℂ)‖)
      volume (0:ℝ) ℓ := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div continuousOn_const hcontB
    intro t ht
    rw [Set.uIcc_of_le hℓ0] at ht
    exact ne_of_gt (lt_of_lt_of_le hδ (hclear t ht (m + 1)))
  have hIntSum : IntervalIntegrable (fun t : ℝ =>
      1 / ‖(p + (t : ℂ) • v) - (m : ℂ)‖
        + 1 / ‖(p + (t : ℂ) • v) - ((m + 1 : ℤ) : ℂ)‖) volume (0:ℝ) ℓ := hIntA.add hIntB
  have hIntMin : IntervalIntegrable (fun t : ℝ =>
      1 / min (‖(p + (t : ℂ) • v) - (m : ℂ)‖)
        (‖(p + (t : ℂ) • v) - ((m + 1 : ℤ) : ℂ)‖)) volume (0:ℝ) ℓ := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div continuousOn_const (hcontA.inf hcontB)
    intro t ht
    rw [Set.uIcc_of_le hℓ0] at ht
    exact ne_of_gt (lt_of_lt_of_le hδ (le_min (hclear t ht m) (hclear t ht (m + 1))))
  -- Step 4: the two single-integer estimates.
  have hA_le : (∫ t in (0:ℝ)..ℓ, 1 / ‖(p + (t : ℂ) • v) - (m : ℂ)‖)
      ≤ 2 * (1 + Real.log (2 + ℓ / δ)) := by
    have hhyp : ∀ t ∈ Set.Icc (0:ℝ) ℓ, δ ≤ ‖(p - (m : ℂ)) + (t : ℂ) • v‖ := by
      intro t ht
      have he : (p - (m : ℂ)) + (t : ℂ) • v = (p + (t : ℂ) • v) - (m : ℂ) := by
        simp only [smul_eq_mul]; ring
      rw [he]
      exact hclear t ht m
    have h := line_integral_inv_norm_le (r := p - (m : ℂ)) (v := v) (ℓ := ℓ) (δ := δ)
      hℓ0 hδ hv hhyp
    have heq : (∫ t in (0:ℝ)..ℓ, 1 / ‖(p - (m : ℂ)) + (t : ℂ) • v‖)
        = ∫ t in (0:ℝ)..ℓ, 1 / ‖(p + (t : ℂ) • v) - (m : ℂ)‖ := by
      apply intervalIntegral.integral_congr
      intro t _
      show 1 / ‖(p - (m : ℂ)) + (t : ℂ) • v‖ = 1 / ‖(p + (t : ℂ) • v) - (m : ℂ)‖
      have he : (p - (m : ℂ)) + (t : ℂ) • v = (p + (t : ℂ) • v) - (m : ℂ) := by
        simp only [smul_eq_mul]; ring
      rw [he]
    rwa [heq] at h
  have hB_le : (∫ t in (0:ℝ)..ℓ, 1 / ‖(p + (t : ℂ) • v) - ((m + 1 : ℤ) : ℂ)‖)
      ≤ 2 * (1 + Real.log (2 + ℓ / δ)) := by
    have hhyp : ∀ t ∈ Set.Icc (0:ℝ) ℓ, δ ≤ ‖(p - ((m + 1 : ℤ) : ℂ)) + (t : ℂ) • v‖ := by
      intro t ht
      have he : (p - ((m + 1 : ℤ) : ℂ)) + (t : ℂ) • v
          = (p + (t : ℂ) • v) - ((m + 1 : ℤ) : ℂ) := by
        simp only [smul_eq_mul]; ring
      rw [he]
      exact hclear t ht (m + 1)
    have h := line_integral_inv_norm_le (r := p - ((m + 1 : ℤ) : ℂ)) (v := v) (ℓ := ℓ)
      (δ := δ) hℓ0 hδ hv hhyp
    have heq : (∫ t in (0:ℝ)..ℓ, 1 / ‖(p - ((m + 1 : ℤ) : ℂ)) + (t : ℂ) • v‖)
        = ∫ t in (0:ℝ)..ℓ, 1 / ‖(p + (t : ℂ) • v) - ((m + 1 : ℤ) : ℂ)‖ := by
      apply intervalIntegral.integral_congr
      intro t _
      show 1 / ‖(p - ((m + 1 : ℤ) : ℂ)) + (t : ℂ) • v‖
        = 1 / ‖(p + (t : ℂ) • v) - ((m + 1 : ℤ) : ℂ)‖
      have he : (p - ((m + 1 : ℤ) : ℂ)) + (t : ℂ) • v
          = (p + (t : ℂ) • v) - ((m + 1 : ℤ) : ℂ) := by
        simp only [smul_eq_mul]; ring
      rw [he]
    rwa [heq] at h
  -- Step 5: assemble.
  calc ∫ t in (0:ℝ)..ℓ, 1 / (⨅ k : ℤ, ‖(p + (t : ℂ) • v) - (k : ℂ)‖)
      = ∫ t in (0:ℝ)..ℓ,
          1 / min (‖(p + (t : ℂ) • v) - (m : ℂ)‖) (‖(p + (t : ℂ) • v) - ((m + 1 : ℤ) : ℂ)‖) :=
        hcongr
    _ ≤ ∫ t in (0:ℝ)..ℓ,
          (1 / ‖(p + (t : ℂ) • v) - (m : ℂ)‖
            + 1 / ‖(p + (t : ℂ) • v) - ((m + 1 : ℤ) : ℂ)‖) :=
        intervalIntegral.integral_mono_on hℓ0 hIntMin hIntSum hpt
    _ = (∫ t in (0:ℝ)..ℓ, 1 / ‖(p + (t : ℂ) • v) - (m : ℂ)‖)
          + ∫ t in (0:ℝ)..ℓ, 1 / ‖(p + (t : ℂ) • v) - ((m + 1 : ℤ) : ℂ)‖ :=
        intervalIntegral.integral_add hIntA hIntB
    _ ≤ 2 * (1 + Real.log (2 + ℓ / δ)) + 2 * (1 + Real.log (2 + ℓ / δ)) := add_le_add hA_le hB_le
    _ = 4 * (1 + Real.log (2 + ℓ / δ)) := by ring

end Work.Pert.V5
