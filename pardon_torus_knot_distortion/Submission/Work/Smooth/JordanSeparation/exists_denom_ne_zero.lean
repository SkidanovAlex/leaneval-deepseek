import Mathlib
import Submission.Work.Smooth.JordanSeparation.Defs
import Submission.Work.Smooth.JordanSeparation.far_chord_bound

/-!
# Nonvanishing of the winding-integral denominator near the parameter `0`

For a `C¹` immersed simple closed plane curve `c` and all sufficiently small `s > 0` one has

`(γ τ - γ 0)^2 + s^2 · u^2 ≠ 0`  for every `τ`,   where `u = unitTangent c 0`.

This is the denominator estimate for the local model of the winding integral: the quantity is
nonzero because

* near the parameters `τ ≡ 0 (mod 2π)` the curve is tangent to `u`, so `((γ τ - γ 0)/u)^2` grows
  like `τ^2‖γ'(0)‖²` and hence has *positive real part* — the derivative computation of
  `exists_local_re_pos`;
* away from those parameters the chord `γ τ - γ 0` is bounded below by the far-chord bound
  `far_chord_bound`, which beats `s^2` as soon as `s` is small.

## Main results

* `exists_shift_mem_Ico` — reduction of a parameter modulo one period;
* `exists_local_re_pos` — positivity of the real part of the squared normalised chord near `0`;
* `exists_denom_ne_zero` — the requested nonvanishing.
-/

open Set Filter
open scoped Topology
open Work.Smooth.Jordan

namespace Work.Smooth.JordanSeparation

noncomputable section

/-- **Reduction of a parameter modulo one period.**  Every `τ : ℝ` differs from a parameter
`τ₀ ∈ [0, 2π)` by an integer multiple of `2π`, and `γ τ₀ = γ τ` by periodicity. -/
theorem exists_shift_mem_Ico (c : PlaneCurve) (τ : ℝ) :
    ∃ k : ℤ, τ - (k : ℝ) * (2 * Real.pi) ∈ Set.Ico (0 : ℝ) (2 * Real.pi) ∧
      c.γ (τ - (k : ℝ) * (2 * Real.pi)) = c.γ τ := by
  refine ⟨⌊τ / (2 * Real.pi)⌋, ?_, ?_⟩
  · have hpos : (0 : ℝ) < 2 * Real.pi := two_pi_pos
    constructor
    · have hh := (le_div_iff₀ hpos).mp (Int.floor_le (τ / (2 * Real.pi)))
      linarith
    · have hh := (div_lt_iff₀ hpos).mp (Int.lt_floor_add_one (τ / (2 * Real.pi)))
      linarith
  · have hh : c.γ (τ - (⌊τ / (2 * Real.pi)⌋ : ℝ) * (2 * Real.pi) +
        (⌊τ / (2 * Real.pi)⌋ : ℝ) * (2 * Real.pi)) =
        c.γ (τ - (⌊τ / (2 * Real.pi)⌋ : ℝ) * (2 * Real.pi)) :=
      c.periodic.int_mul ⌊τ / (2 * Real.pi)⌋ (τ - (⌊τ / (2 * Real.pi)⌋ : ℝ) * (2 * Real.pi))
    rw [show τ - (⌊τ / (2 * Real.pi)⌋ : ℝ) * (2 * Real.pi) +
        (⌊τ / (2 * Real.pi)⌋ : ℝ) * (2 * Real.pi) = τ from by ring] at hh
    exact hh.symm

/-- **Positivity of the real part of the squared normalised chord near the parameter `0`.**
For a `C¹` immersed curve the image of `τ ↦ (γ τ - γ 0)/u` (with `u` the unit tangent at `0`) is
tangent to the real axis at `0` and grows linearly, so the square has positive real part on a
punctured neighbourhood of `0`. -/
theorem exists_local_re_pos (c : SmoothPlaneCurve) (h : c.IsImmersion) :
    ∃ δ₁ : ℝ, 0 < δ₁ ∧ ∀ τ : ℝ, 0 < |τ| → |τ| < δ₁ →
      0 < (((c.γ τ - c.γ 0) / (unitTangent c 0)) ^ 2).re := by
  set v : ℂ := deriv c.γ 0 with hv
  have hv0 : v ≠ 0 := hv ▸ h 0
  have hnormpos : 0 < ‖v‖ := norm_pos_iff.mpr hv0
  have hderiv : HasDerivAt c.γ v 0 := hv ▸ (c.differentiable 0).hasDerivAt
  have hlim : Tendsto (fun t : ℝ => t⁻¹ • (c.γ t - c.γ 0)) (𝓝[≠] (0:ℝ)) (𝓝 v) := by
    have hh := hderiv.tendsto_slope_zero
    simpa only [zero_add] using hh
  have hu_ne : unitTangent c 0 ≠ 0 := by
    intro h0
    have hh := norm_unitTangent c h 0
    rw [h0, norm_zero] at hh
    norm_num at hh
  have hu_eq : unitTangent c 0 = v * (((‖v‖ : ℝ)) : ℂ)⁻¹ := by
    rw [unitTangent_def, ← hv, div_eq_mul_inv]
  have hc_ne : (((‖v‖ : ℝ)) : ℂ) ≠ 0 := by
    simpa using ne_of_gt hnormpos
  have hu_mul : unitTangent c 0 * (((‖v‖ : ℝ)) : ℂ) = v := by
    rw [hu_eq, mul_assoc, inv_mul_cancel₀ hc_ne, mul_one]
  have huval : (unitTangent c 0)⁻¹ * v = (((‖v‖ : ℝ)) : ℂ) := by
    conv_lhs => rw [← hu_mul]
    rw [← mul_assoc, inv_mul_cancel₀ hu_ne, one_mul]
  -- the limit of the squared normalised chord, which is `‖γ'(0)‖²`
  have hF : Tendsto (fun t : ℝ => (unitTangent c 0)⁻¹ * (t⁻¹ • (c.γ t - c.γ 0)))
      (𝓝[≠] (0:ℝ)) (𝓝 ((unitTangent c 0)⁻¹ * v)) := hlim.const_mul _
  have hF2 := hF.pow 2
  have hval : ((unitTangent c 0)⁻¹ * v) ^ 2 = (((‖v‖ ^ 2 : ℝ)) : ℂ) := by
    rw [huval, ← Complex.ofReal_pow]
  have hmain : Tendsto (fun t : ℝ => ((c.γ t - c.γ 0) / ((t : ℂ) * unitTangent c 0)) ^ 2)
      (𝓝[≠] (0:ℝ)) (𝓝 (((‖v‖ ^ 2 : ℝ)) : ℂ)) := by
    rw [hval] at hF2
    refine hF2.congr' (Eventually.of_forall fun t => ?_)
    simp only []
    congr 1
    rw [Complex.real_smul, div_eq_mul_inv, mul_inv, Complex.ofReal_inv]
    ring
  have hsqpos : 0 < ‖v‖ ^ 2 := pow_pos hnormpos 2
  have hev : ∀ᶠ t in 𝓝[≠] (0:ℝ),
      dist (((c.γ t - c.γ 0) / ((t : ℂ) * unitTangent c 0)) ^ 2) (((‖v‖ ^ 2 : ℝ)) : ℂ)
        < ‖v‖ ^ 2 / 2 :=
    (Metric.tendsto_nhds.mp hmain) _ (by linarith)
  obtain ⟨δ₁, hδ₁pos, hδ₁⟩ := Metric.mem_nhdsWithin_iff.mp hev
  refine ⟨δ₁, hδ₁pos, fun τ hτ hτδ => ?_⟩
  have hP : dist (((c.γ τ - c.γ 0) / ((τ : ℂ) * unitTangent c 0)) ^ 2) (((‖v‖ ^ 2 : ℝ)) : ℂ)
      < ‖v‖ ^ 2 / 2 :=
    hδ₁ ⟨Metric.mem_ball.mpr (by rw [dist_zero_right]; exact hτδ),
      by simp only [Set.mem_compl_iff, Set.mem_singleton_iff]; exact abs_pos.mp hτ⟩
  have hre : 0 < (((c.γ τ - c.γ 0) / ((τ : ℂ) * unitTangent c 0)) ^ 2).re := by
    rw [Complex.dist_eq] at hP
    have h1 := Complex.abs_re_le_norm
      (((c.γ τ - c.γ 0) / ((τ : ℂ) * unitTangent c 0)) ^ 2 - (((‖v‖ ^ 2 : ℝ)) : ℂ))
    rw [Complex.sub_re, Complex.ofReal_re] at h1
    have h2 : |(((c.γ τ - c.γ 0) / ((τ : ℂ) * unitTangent c 0)) ^ 2).re - ‖v‖ ^ 2|
        < ‖v‖ ^ 2 / 2 :=
      lt_of_le_of_lt h1 hP
    have h3 := (abs_lt.mp h2).1
    linarith
  have hτC : (τ : ℂ) ≠ 0 := by exact_mod_cast (abs_pos.mp hτ)
  have hident : ((c.γ τ - c.γ 0) / (unitTangent c 0)) ^ 2
      = (((τ ^ 2 : ℝ)) : ℂ) * ((c.γ τ - c.γ 0) / ((τ : ℂ) * unitTangent c 0)) ^ 2 := by
    field_simp
    rw [Complex.ofReal_pow]
  rw [hident, Complex.re_ofReal_mul]
  exact mul_pos (sq_pos_of_ne_zero (abs_pos.mp hτ)) hre

/-- **The denominator is nonzero for small `s`.**  With `u = unitTangent c 0` the quantity
`(γ τ - γ 0)^2 + s^2 u^2` does not vanish for `0 < s < δ` and every `τ`. -/
theorem exists_denom_ne_zero (c : Work.Smooth.Jordan.SmoothPlaneCurve)
    (h : Work.Smooth.Jordan.SmoothPlaneCurve.IsImmersion c) (hsimple : c.toPlaneCurve.IsSimple) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ s : ℝ, 0 < s → s < δ → ∀ τ : ℝ,
      (c.γ τ - c.γ 0) ^ 2 + (s : ℂ) ^ 2 * (Work.Smooth.JordanSeparation.unitTangent c 0) ^ 2 ≠ 0 := by
  obtain ⟨δ₁, hδ₁pos, hδ₁⟩ := exists_local_re_pos c h
  set ε : ℝ := min (Real.pi / 2) δ₁ with hεdef
  have hεpos : 0 < ε := lt_min (by linarith [Real.pi_pos]) hδ₁pos
  have hεδ₁ : ε ≤ δ₁ := min_le_right _ _
  have hεπ : ε ≤ Real.pi := le_trans (min_le_left _ _) (by linarith [Real.pi_pos])
  obtain ⟨η, hηpos, hη⟩ := far_chord_bound c hsimple hεpos hεπ
  refine ⟨min ε η, lt_min hεpos hηpos, ?_⟩
  intro s hs hsδ τ
  have hsε : s < ε := lt_of_lt_of_le hsδ (min_le_left _ _)
  have hsη : s < η := lt_of_lt_of_le hsδ (min_le_right _ _)
  have hsC : (s : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hs)
  have hu_ne : unitTangent c 0 ≠ 0 := by
    intro h0
    have hh := norm_unitTangent c h 0
    rw [h0, norm_zero] at hh
    norm_num at hh
  obtain ⟨k, hk_mem, hk_eq⟩ := exists_shift_mem_Ico c.toPlaneCurve τ
  set τ₀ : ℝ := τ - (k : ℝ) * (2 * Real.pi) with hτ₀def
  have hτ₀_mem : τ₀ ∈ Set.Ico (0 : ℝ) (2 * Real.pi) := hk_mem
  have hτ₀_eq : c.γ τ₀ = c.γ τ := hk_eq
  -- the close-to-`2πℤ` case
  have near_step : ∀ x : ℝ, |x| < δ₁ → c.γ x = c.γ τ →
      (c.γ τ - c.γ 0) ^ 2 + (s : ℂ) ^ 2 * (unitTangent c 0) ^ 2 ≠ 0 := by
    intro x hx hxe
    have hw : c.γ τ - c.γ 0 = c.γ x - c.γ 0 := by rw [hxe]
    rw [hw]
    rcases eq_or_ne x 0 with hx0 | hxne
    · subst hx0
      have hz : c.γ 0 - c.γ 0 = (0 : ℂ) := sub_self _
      rw [hz, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_add]
      exact mul_ne_zero (pow_ne_zero 2 hsC) (pow_ne_zero 2 hu_ne)
    · have hrelt := hδ₁ x (abs_pos.mpr hxne) hx
      have hident2 : (c.γ x - c.γ 0) ^ 2 + (s : ℂ) ^ 2 * (unitTangent c 0) ^ 2
          = (unitTangent c 0) ^ 2 *
            (((c.γ x - c.γ 0) / (unitTangent c 0)) ^ 2 + (s : ℂ) ^ 2) := by
        field_simp
      rw [hident2]
      refine mul_ne_zero (pow_ne_zero 2 hu_ne) fun hsum => ?_
      have hre0 : (((c.γ x - c.γ 0) / (unitTangent c 0)) ^ 2 + (s : ℂ) ^ 2).re = 0 := by
        rw [hsum, Complex.zero_re]
      have hs2 : ((s : ℂ) ^ 2).re = s ^ 2 := by rw [← Complex.ofReal_pow, Complex.ofReal_re]
      rw [Complex.add_re, hs2] at hre0
      have hspos : 0 < s ^ 2 := pow_pos hs 2
      linarith
  -- the far case
  have far_step : ε ≤ τ₀ → τ₀ ≤ 2 * Real.pi - ε →
      (c.γ τ - c.γ 0) ^ 2 + (s : ℂ) ^ 2 * (unitTangent c 0) ^ 2 ≠ 0 := by
    intro h1 h2 hzero
    have hchord : η ≤ ‖c.γ τ₀ - c.γ 0‖ := by
      refine hη τ₀ 0 hτ₀_mem ⟨le_refl 0, two_pi_pos⟩ ?_ ?_
      · rw [zero_sub, abs_neg, abs_of_nonneg hτ₀_mem.1]; exact h1
      · rw [zero_sub, abs_neg, abs_of_nonneg hτ₀_mem.1]; exact h2
    have hchord' : η ≤ ‖c.γ τ - c.γ 0‖ := by rw [← hτ₀_eq]; exact hchord
    have h2eq : (c.γ τ - c.γ 0) ^ 2 = -((s : ℂ) ^ 2 * (unitTangent c 0) ^ 2) :=
      add_eq_zero_iff_eq_neg.mp hzero
    have h3 : ‖c.γ τ - c.γ 0‖ ^ 2 = s ^ 2 := by
      have h4 : ‖(c.γ τ - c.γ 0) ^ 2‖ = ‖(s : ℂ) ^ 2 * (unitTangent c 0) ^ 2‖ := by
        rw [h2eq, norm_neg]
      rw [norm_pow, norm_mul, norm_pow, norm_pow, norm_unitTangent c h 0, one_pow, mul_one,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs] at h4
      exact h4
    have hle : η ^ 2 ≤ ‖c.γ τ - c.γ 0‖ ^ 2 := pow_le_pow_left₀ hηpos.le hchord' 2
    have hlt : s ^ 2 < η ^ 2 := pow_lt_pow_left₀ hsη hs.le (by norm_num)
    linarith
  rcases lt_or_ge ε τ₀ with hgt | hle
  · rcases le_or_gt τ₀ (2 * Real.pi - ε) with hfar2 | hnear2
    · exact far_step hgt.le hfar2
    · refine near_step (τ₀ - 2 * Real.pi) ?_ ?_
      · rw [abs_of_neg (by linarith [hτ₀_mem.2])]
        linarith
      · have hh := c.periodic (τ₀ - 2 * Real.pi)
        rw [show τ₀ - 2 * Real.pi + 2 * Real.pi = τ₀ from by ring] at hh
        exact hh.symm.trans hτ₀_eq
  · rcases lt_or_eq_of_le hle with hlt | heq
    · refine near_step τ₀ ?_ hτ₀_eq
      rw [abs_of_nonneg hτ₀_mem.1]
      exact lt_of_lt_of_le hlt hεδ₁
    · refine far_step heq.ge ?_
      rw [heq]
      linarith

end

end Work.Smooth.JordanSeparation
