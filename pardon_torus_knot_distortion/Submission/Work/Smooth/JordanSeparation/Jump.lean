import Mathlib
import Submission.Work.Smooth.JordanSeparation.Defs
import Submission.Work.Smooth.JordanSeparation.exists_normal_offset_notMem_trace
import Submission.Work.Smooth.JordanSeparation.wind_normal_offset_sub
import Submission.Work.Smooth.JordanSeparation.tendsto_winding_jump_integral

/-!
# The index jumps by one across a simple immersed curve

This file assembles the *at least two components* half of the Jordan curve theorem for a `C¹`
immersed simple closed plane curve `c`:

* `wind_normal_offset_sub` (sibling) rewrites the difference of the two winding integrals at the
  normal offsets `c.γ 0 ± s·normalField c 0` as `(1/π)·ê·∫ s·γ'/((γ-γ0)² + s²ê²)`;
* `tendsto_winding_jump_integral` (sibling) shows that the integral tends to `π·conj ê` as
  `s → 0⁺`, so that difference tends to `(1/π)·ê·(π·conj ê) = ê·conj ê = 1`;
* since the difference of two winding integrals off the trace is an integer (`wind_mem_int`), it is
  *eventually equal* to `1`.

Hence:

* `tendsto_wind_normal_offset_sub` — the difference tends to `1`;
* `wind_normal_offset_sub_eq_one` — it is identically `1` for small `s > 0`;
* `ind_jump` — the index of `c` at `c.γ 0 + s·normalField c 0` is one more than at
  `c.γ 0 - s·normalField c 0`.
-/

open Set
open Work.Smooth.Jordan

namespace Work.Smooth.JordanSeparation

noncomputable section

/-- **The difference of the two winding integrals at the normal offsets tends to `1`.** -/
theorem tendsto_wind_normal_offset_sub (c : SmoothPlaneCurve) (himm : c.IsImmersion)
    (hs : c.toPlaneCurve.IsSimple) :
    Filter.Tendsto (fun s : ℝ =>
        wind c (c.γ 0 + s * normalField c 0) - wind c (c.γ 0 - s * normalField c 0))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 1) := by
  obtain ⟨δ₁, hδ₁, hnt⟩ := exists_normal_offset_notMem_trace c himm hs
  have hJ := tendsto_winding_jump_integral c himm hs
  have h₁ : Filter.Tendsto (fun s : ℝ => (1 / (Real.pi : ℂ)) * unitTangent c 0 *
      (∫ τ in (0 : ℝ)..(2 * Real.pi),
        (s * deriv c.γ τ) /
          ((c.γ τ - c.γ 0) ^ 2 + (s : ℂ) ^ 2 * (unitTangent c 0) ^ 2)))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds ((1 / (Real.pi : ℂ)) * unitTangent c 0 *
        ((Real.pi : ℂ) * (starRingEnd ℂ) (unitTangent c 0)))) :=
    hJ.const_mul _
  have hval : (1 / (Real.pi : ℂ)) * unitTangent c 0 *
      ((Real.pi : ℂ) * (starRingEnd ℂ) (unitTangent c 0)) = 1 := by
    have hunit := norm_unitTangent c himm 0
    have hconj : unitTangent c 0 * (starRingEnd ℂ) (unitTangent c 0) = 1 := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hunit]
      norm_num
    calc (1 / (Real.pi : ℂ)) * unitTangent c 0 *
          ((Real.pi : ℂ) * (starRingEnd ℂ) (unitTangent c 0))
        = ((1 / (Real.pi : ℂ)) * (Real.pi : ℂ)) *
            (unitTangent c 0 * (starRingEnd ℂ) (unitTangent c 0)) := by ring
      _ = 1 := by rw [hconj]; field_simp
  rw [hval] at h₁
  have hmem : ∀ᶠ s : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0), s ∈ Set.Ioo (0 : ℝ) δ₁ := by
    rw [eventually_nhdsWithin_iff]
    filter_upwards [isOpen_Iio.mem_nhds (show (0 : ℝ) < δ₁ by linarith)] with s hlt hpos
    exact ⟨hpos, hlt⟩
  refine h₁.congr' ?_
  filter_upwards [hmem] with s hs1
  have hspos : c.γ 0 + s * normalField c 0 ∉ c.trace := (hnt s hs1.1 hs1.2).1
  have hsneg : c.γ 0 - s * normalField c 0 ∉ c.trace := (hnt s hs1.1 hs1.2).2
  exact (wind_normal_offset_sub c himm hs1.1 hspos hsneg).symm

/-- **The difference of the two winding integrals at the normal offsets is `1` for small `s > 0`.** -/
theorem wind_normal_offset_sub_eq_one (c : SmoothPlaneCurve) (himm : c.IsImmersion)
    (hs : c.toPlaneCurve.IsSimple) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ s : ℝ, 0 < s → s < δ →
      wind c (c.γ 0 + s * normalField c 0) - wind c (c.γ 0 - s * normalField c 0) = 1 := by
  obtain ⟨δ₁, hδ₁, hnt⟩ := exists_normal_offset_notMem_trace c himm hs
  have htend := tendsto_wind_normal_offset_sub c himm hs
  have hev : ∀ᶠ s : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      dist (wind c (c.γ 0 + s * normalField c 0)
        - wind c (c.γ 0 - s * normalField c 0)) (1 : ℂ) < (1 / 2 : ℝ) :=
    (Metric.tendsto_nhds.mp htend) (1 / 2) (by norm_num)
  rw [eventually_nhdsWithin_iff] at hev
  rw [Metric.eventually_nhds_iff] at hev
  obtain ⟨ε, hε, hεspec⟩ := hev
  refine ⟨min ε δ₁, lt_min hε hδ₁, fun s hs0 hslt => ?_⟩
  have hε' : dist s (0 : ℝ) < ε := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hs0]
    exact lt_of_lt_of_le hslt (min_le_left _ _)
  have hP : dist (wind c (c.γ 0 + s * normalField c 0)
      - wind c (c.γ 0 - s * normalField c 0)) (1 : ℂ) < (1 / 2 : ℝ) := hεspec hε' hs0
  have hsδ₁ : s < δ₁ := lt_of_lt_of_le hslt (min_le_right _ _)
  have hnt' := hnt s hs0 hsδ₁
  have hint : ∃ k : ℤ, wind c (c.γ 0 + s * normalField c 0)
      - wind c (c.γ 0 - s * normalField c 0) = (k : ℂ) := by
    obtain ⟨k, hk⟩ := wind_mem_int c hnt'.1
    obtain ⟨l, hl⟩ := wind_mem_int c hnt'.2
    exact ⟨k - l, by rw [hk, hl]; push_cast; ring⟩
  obtain ⟨m, hm⟩ := hint
  have hm1 : ‖(((m - 1 : ℤ)) : ℂ)‖ < (1 / 2 : ℝ) := by
    have hcast : (((m - 1 : ℤ)) : ℂ) = (m : ℂ) - 1 := by
      rw [Int.cast_sub, Int.cast_one]
    rw [hcast, ← hm, dist_eq_norm] at *
    exact hP
  have hm1Z : |(m - 1 : ℤ)| < 1 := by
    have h2 : (((|(m - 1 : ℤ)| : ℤ)) : ℝ) < 1 := by
      rw [Int.cast_abs, ← Complex.norm_intCast]
      linarith [hm1]
    exact_mod_cast h2
  have hm0 : m - 1 = 0 := Int.abs_lt_one_iff.mp hm1Z
  rw [hm]
  have : m = 1 := by omega
  rw [this]; norm_num

/-- **The index jumps by one across a simple immersed closed curve.**  For a `C¹` immersed simple
closed plane curve `c` there is `δ > 0` such that for `0 < s < δ` the points
`c.γ 0 ± s·normalField c 0` lie off the trace and the index at the `+` point is one more than the
index at the `-` point. -/
theorem ind_jump (c : SmoothPlaneCurve) (himm : c.IsImmersion) (hs : c.toPlaneCurve.IsSimple) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ s : ℝ, 0 < s → s < δ →
      c.γ 0 + s * normalField c 0 ∉ c.trace ∧
        c.γ 0 - s * normalField c 0 ∉ c.trace ∧
        ind c (c.γ 0 + s * normalField c 0) = ind c (c.γ 0 - s * normalField c 0) + 1 := by
  obtain ⟨δ₁, hδ₁, hnt⟩ := exists_normal_offset_notMem_trace c himm hs
  obtain ⟨δ₂, hδ₂, hwind⟩ := wind_normal_offset_sub_eq_one c himm hs
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun s hs0 hslt => ?_⟩
  have hs₁ : s < δ₁ := lt_of_lt_of_le hslt (min_le_left _ _)
  have hs₂ : s < δ₂ := lt_of_lt_of_le hslt (min_le_right _ _)
  obtain ⟨hpos, hneg⟩ := hnt s hs0 hs₁
  refine ⟨hpos, hneg, ?_⟩
  have hw := hwind s hs0 hs₂
  obtain ⟨k, hk⟩ := wind_mem_int c hpos
  obtain ⟨l, hl⟩ := wind_mem_int c hneg
  have hcast : ((ind c (c.γ 0 + s * normalField c 0)
      - ind c (c.γ 0 - s * normalField c 0) : ℤ) : ℂ) = 1 := by
    rw [Int.cast_sub, ind_spec c ⟨k, hk⟩, ind_spec c ⟨l, hl⟩]
    exact hw
  have hm : ind c (c.γ 0 + s * normalField c 0) - ind c (c.γ 0 - s * normalField c 0)
      = (1 : ℤ) := Int.cast_injective (by rw [hcast]; norm_num)
  omega

end

end Work.Smooth.JordanSeparation
