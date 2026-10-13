import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_StreamBdry.SB25Aux2.axisTail_bound`

The 1-D tail bound used by leaf B4 (`axis_d2_bound`): for `W := f·cos`,

  `|W θ₀ + v₀(1 - sin θ₀)| ≤ ε (sin δ - δ cos δ)`,  `δ = π/2 - θ₀`,

under `|f| ≤ B` on `(0,π/2)`, `f` differentiable there, and
`|f' - tan·f - v₀| ≤ ε(π/2 - t)` on `[θ₀, π/2)`.

This is the `W`-half of the axis expansion: `J := W + v₀(1 - sin)` satisfies
`J' = cos·(f' - tan·f - v₀)`, so `|J'| ≤ ε cos t (π/2 - t)` on `[θ₀, π/2)`, and `J → 0` at
`π/2` because `f` is bounded there.  The fundamental theorem of calculus on the half-open
interval (`intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto`, with the integrability
of `deriv J` from its a.e. bound `ε(π/2 - θ₀)` and `aestronglyMeasurable_deriv`) gives
`|J θ₀| ≤ ∫_{θ₀}^{π/2}|J'| ≤ ε ∫_{θ₀}^{π/2} cos t (π/2 - t) dt = ε(sin δ - δ cos δ)`,
the last integral being evaluated with the primitive `(π/2 - t) sin t - cos t`.
-/

noncomputable section
open scoped Real Topology NNReal
open Set Filter MeasureTheory

namespace Work.FTS_StreamBdry.SB25Aux2

theorem axisTail_bound (f : ℝ → ℝ) (v0 B ε θ0 : ℝ) (hθ0 : θ0 ∈ Set.Ioo (0 : ℝ) (Real.pi / 2))
    (hB : 0 ≤ B) (hε : 0 ≤ ε)
    (hf : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), DifferentiableAt ℝ f θ)
    (hb : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), |f θ| ≤ B)
    (hV : ∀ t ∈ Set.Ico θ0 (Real.pi / 2),
      |deriv f t - Real.tan t * f t - v0| ≤ ε * (Real.pi / 2 - t)) :
    |f θ0 * Real.cos θ0 + v0 * (1 - Real.sin θ0)| ≤
      ε * (Real.sin (Real.pi / 2 - θ0) - (Real.pi / 2 - θ0) * Real.cos (Real.pi / 2 - θ0)) := by
  set J : ℝ → ℝ := fun t => f t * Real.cos t + v0 * (1 - Real.sin t) with hJdef
  have hlt : θ0 < Real.pi / 2 := hθ0.2
  have hθ0pos : 0 < θ0 := hθ0.1
  -- the derivative of `J` on `(0, π/2)`
  have hJderiv : ∀ x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      HasDerivAt J (Real.cos x * (deriv f x - Real.tan x * f x - v0)) x := by
    intro x hx
    have hcx : Real.cos x ≠ 0 :=
      ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hx.1], hx.2⟩)
    have h1 : HasDerivAt (fun t => f t * Real.cos t)
        (deriv f x * Real.cos x + f x * (-Real.sin x)) x :=
      (hf x hx).hasDerivAt.mul (Real.hasDerivAt_cos x)
    have h2 : HasDerivAt (fun t => v0 * (1 - Real.sin t)) (v0 * (-Real.cos x)) x := by
      have h1' : HasDerivAt (fun t => 1 - Real.sin t) (-Real.cos x) x :=
        (Real.hasDerivAt_sin x).const_sub 1
      exact h1'.const_mul v0
    have h3 : HasDerivAt (fun t => f t * Real.cos t + v0 * (1 - Real.sin t))
        (deriv f x * Real.cos x + f x * (-Real.sin x) + v0 * (-Real.cos x)) x := h1.add h2
    rw [hJdef]
    convert h3 using 1
    rw [Real.tan_eq_sin_div_cos]
    field_simp
    ring
  -- `deriv J` is bounded on `(θ₀, π/2]`
  have hbound : ∀ᵐ x ∂(volume.restrict (Set.Ioc θ0 (Real.pi / 2))),
      ‖deriv J x‖ ≤ ε * (Real.pi / 2 - θ0) := by
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioc, MeasureTheory.ae_iff]
    refine MeasureTheory.measure_mono_null ?_ (Real.volume_singleton (a := Real.pi / 2))
    intro x hx
    simp only [Set.mem_ofPred_eq, not_imp] at hx
    obtain ⟨hxIoc, hxlt⟩ := hx
    simp only [Set.mem_singleton_iff]
    by_contra hne
    have hxoo : x ∈ Set.Ioo θ0 (Real.pi / 2) := ⟨hxIoc.1, lt_of_le_of_ne hxIoc.2 hne⟩
    have hx0 : x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
      ⟨by linarith [hθ0pos, hxoo.1], hxoo.2⟩
    have hd : deriv J x = Real.cos x * (deriv f x - Real.tan x * f x - v0) :=
      (hJderiv x hx0).deriv
    have hVx : |deriv f x - Real.tan x * f x - v0| ≤ ε * (Real.pi / 2 - x) :=
      hV x ⟨hxoo.1.le, hxoo.2⟩
    have hcosnn : 0 ≤ Real.cos x :=
      le_of_lt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hx0.1], hx0.2⟩)
    have hcle : Real.cos x ≤ 1 := Real.cos_le_one x
    have hdle : ε * (Real.pi / 2 - x) ≤ ε * (Real.pi / 2 - θ0) :=
      mul_le_mul_of_nonneg_left (by linarith [hxoo.1]) hε
    have hprod : Real.cos x * |deriv f x - Real.tan x * f x - v0| ≤
        1 * (ε * (Real.pi / 2 - θ0)) :=
      mul_le_mul hcle (le_trans hVx hdle) (abs_nonneg _) (by norm_num)
    rw [hd, Real.norm_eq_abs, abs_mul, abs_of_nonneg hcosnn] at hxlt
    linarith [hprod]
  have hJint : IntervalIntegrable (deriv J) volume θ0 (Real.pi / 2) := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hlt.le]
    exact MeasureTheory.IntegrableOn.of_bound measure_Ioc_lt_top
      (aestronglyMeasurable_deriv J _) _ hbound
  -- one-sided limits of `J`
  have hJleft : Filter.Tendsto J (nhdsWithin θ0 (Set.Ioi θ0)) (nhds (J θ0)) := by
    have hfcont : ContinuousAt f θ0 := (hf θ0 hθ0).continuousAt
    have hcont : ContinuousAt J θ0 := by
      rw [hJdef]
      exact (hfcont.mul Real.continuous_cos.continuousAt).add
        (continuousAt_const.mul (continuousAt_const.sub Real.continuous_sin.continuousAt))
    exact hcont.tendsto.mono_left nhdsWithin_le_nhds
  have hJright : Filter.Tendsto J (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
    have hev : ∀ᶠ t in nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)),
        |J t| ≤ B * Real.cos t + |v0| * (1 - Real.sin t) := by
      filter_upwards [Ioo_mem_nhdsLT hlt] with t ht
      have ht0 : t ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨by linarith [hθ0pos, ht.1], ht.2⟩
      have hft : |f t| ≤ B := hb t ht0
      have hcosnn : 0 ≤ Real.cos t :=
        le_of_lt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, ht0.1], ht0.2⟩)
      have hsinnn : 0 ≤ 1 - Real.sin t := by have := Real.sin_le_one t; linarith
      rw [hJdef]
      calc |f t * Real.cos t + v0 * (1 - Real.sin t)|
          ≤ |f t * Real.cos t| + |v0 * (1 - Real.sin t)| := abs_add_le _ _
        _ = |f t| * Real.cos t + |v0| * (1 - Real.sin t) := by
              rw [abs_mul, abs_mul, abs_of_nonneg hcosnn, abs_of_nonneg hsinnn]
        _ ≤ B * Real.cos t + |v0| * (1 - Real.sin t) := by
              have := mul_le_mul_of_nonneg_right hft hcosnn
              linarith
    have hmaj : Filter.Tendsto (fun t => B * Real.cos t + |v0| * (1 - Real.sin t))
        (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
      have hcos : Filter.Tendsto (fun t => Real.cos t)
          (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
        simpa using (Real.continuous_cos.continuousAt.tendsto.mono_left nhdsWithin_le_nhds :
          Filter.Tendsto (fun t => Real.cos t) (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)))
            (nhds (Real.cos (Real.pi / 2))))
      have hsin : Filter.Tendsto (fun t => Real.sin t)
          (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 1) := by
        simpa using (Real.continuous_sin.continuousAt.tendsto.mono_left nhdsWithin_le_nhds :
          Filter.Tendsto (fun t => Real.sin t) (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)))
            (nhds (Real.sin (Real.pi / 2))))
      have h1 : Filter.Tendsto (fun t => B * Real.cos t)
          (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
        simpa using (tendsto_const_nhds (x := B)).mul hcos
      have h2 : Filter.Tendsto (fun t => |v0| * (1 - Real.sin t))
          (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
        have := (tendsto_const_nhds (x := |v0|)).mul
          ((tendsto_const_nhds (x := (1 : ℝ))).sub hsin)
        simpa using this
      simpa using h1.add h2
    have hsq := squeeze_zero' (Filter.Eventually.of_forall (fun t => abs_nonneg (J t))) hev hmaj
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simpa [Real.norm_eq_abs] using hsq
  -- fundamental theorem of calculus on `[θ₀, π/2]`
  have hFTC : ∫ y in θ0..(Real.pi / 2), deriv J y = 0 - J θ0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto hlt
      (f := J) (f' := deriv J) (fa := J θ0) (fb := 0)
      (fun x hx => ((hJderiv x ⟨by linarith [hθ0pos, hx.1], hx.2⟩).differentiableAt).hasDerivAt)
      hJint hJleft hJright
  have h1 : |J θ0| ≤ ∫ y in θ0..(Real.pi / 2), |deriv J y| := by
    have := intervalIntegral.abs_integral_le_integral_abs (μ := volume)
      (a := θ0) (b := Real.pi / 2) (f := fun y => deriv J y) hlt.le
    rw [hFTC] at this
    simpa using this
  have h2 : ∫ y in θ0..(Real.pi / 2), |deriv J y|
      ≤ ∫ y in θ0..(Real.pi / 2), ε * (Real.cos y * (Real.pi / 2 - y)) := by
    refine intervalIntegral.integral_mono_on_of_le_Ioo hlt.le hJint.abs ?_ (fun x hx => ?_)
    · apply ContinuousOn.intervalIntegrable
      fun_prop
    · have hx0 : x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨by linarith [hθ0pos, hx.1], hx.2⟩
      have hd : deriv J x = Real.cos x * (deriv f x - Real.tan x * f x - v0) :=
        (hJderiv x hx0).deriv
      have hVx : |deriv f x - Real.tan x * f x - v0| ≤ ε * (Real.pi / 2 - x) :=
        hV x ⟨hx.1.le, hx.2⟩
      have hcosnn : 0 ≤ Real.cos x :=
        le_of_lt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hx0.1], hx0.2⟩)
      rw [hd, abs_mul, abs_of_nonneg hcosnn]
      have hh := mul_le_mul_of_nonneg_left hVx hcosnn
      nlinarith [hh, hcosnn, hε]
  have h3 : ∫ y in θ0..(Real.pi / 2), ε * (Real.cos y * (Real.pi / 2 - y))
      = ε * (Real.sin (Real.pi / 2 - θ0)
          - (Real.pi / 2 - θ0) * Real.cos (Real.pi / 2 - θ0)) := by
    rw [intervalIntegral.integral_const_mul]
    congr 1
    have hprim : ∀ y : ℝ, HasDerivAt (fun s : ℝ => (Real.pi / 2 - s) * Real.sin s - Real.cos s)
        (Real.cos y * (Real.pi / 2 - y)) y := by
      intro y
      have h1 : HasDerivAt (fun s : ℝ => Real.pi / 2 - s) (-1) y := by
        have h2 : HasDerivAt (fun s : ℝ => -s) (-1) y := (hasDerivAt_id y).neg
        have h3 : HasDerivAt (fun s : ℝ => (Real.pi / 2) + (-s)) (-1) y :=
          h2.const_add (Real.pi / 2)
        simpa [sub_eq_add_neg] using h3
      have h2 := h1.mul (Real.hasDerivAt_sin y)
      have h3 := h2.sub (Real.hasDerivAt_cos y)
      convert h3 using 1
      ring
    have hint : IntervalIntegrable (fun y : ℝ => Real.cos y * (Real.pi / 2 - y)) volume θ0
        (Real.pi / 2) := by
      apply ContinuousOn.intervalIntegrable
      fun_prop
    have h4 := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun s : ℝ => (Real.pi / 2 - s) * Real.sin s - Real.cos s)
      (f' := fun y : ℝ => Real.cos y * (Real.pi / 2 - y)) (fun x _ => hprim x) hint
    rw [h4]
    have hP : (Real.pi / 2 - Real.pi / 2) * Real.sin (Real.pi / 2) - Real.cos (Real.pi / 2) = 0 := by
      simp
    rw [hP, Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub]
    ring
  rw [hJdef] at h1
  linarith [h1, h2, h3]

end Work.FTS_StreamBdry.SB25Aux2
