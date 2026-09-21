import Mathlib

namespace Work.Analysis.Abel

open MeasureTheory Set Filter
open scoped Topology Interval

/-- A slice `v ↦ B x σ` of a jointly `C¹` function is `C¹` in the second variable, on the
vertical line `x = x₀` (as long as the point `x₀` is strictly inside the `x`-range). -/
lemma contDiffOn_slice_right {B : ℝ → ℝ → ℝ} {x₀ c d x₁ x₂ : ℝ}
    (hx₁ : x₁ < x₀) (hx₂ : x₀ < x₂)
    (hB : ContDiffOn ℝ 1 (fun p : ℝ × ℝ => B p.1 p.2) (Set.Ioo x₁ x₂ ×ˢ Set.Ioo c d)) :
    ContDiffOn ℝ 1 (fun v : ℝ => B x₀ v) (Set.Ioo c d) := by
  have hinner : ContDiffOn ℝ 1 (fun v : ℝ => ((x₀ : ℝ), v)) (Set.Ioo c d) :=
    contDiffOn_const.prodMk contDiffOn_id
  have h := hB.comp hinner (fun v hv => ⟨⟨hx₁, hx₂⟩, hv⟩)
  simpa [Function.comp_def] using h

/-- **Integration by parts with a fractional-power weight.**
For `q > 0`, `L₀ > 0` and `(x,σ) ↦ B x σ` jointly `C¹` on an open box containing
`{x₀} × [x₀, x₀+L₀]`,
`∫_0^{L₀} y^q · ∂₂B(x₀, x₀+y) dy = L₀^q B(x₀, x₀+L₀) - ∫_0^{L₀} q y^{q-1} B(x₀, x₀+y) dy`,
where `∂₂B(x₀, x₀+y) = deriv (fun v => B x₀ v) (x₀+y)`. -/
theorem integral_rpow_mul_deriv_slice_eq
    {q : ℝ} (hq : 0 < q) {B : ℝ → ℝ → ℝ} {x₀ L₀ x₁ x₂ c d : ℝ}
    (hx₁ : x₁ < x₀) (hx₂ : x₀ < x₂) (hc : c < x₀) (hd : x₀ + L₀ < d) (hL : 0 < L₀)
    (hB : ContDiffOn ℝ 1 (fun p : ℝ × ℝ => B p.1 p.2) (Set.Ioo x₁ x₂ ×ˢ Set.Ioo c d)) :
    (∫ y in (0:ℝ)..L₀, y ^ q * deriv (fun v : ℝ => B x₀ v) (x₀ + y))
      = L₀ ^ q * B x₀ (x₀ + L₀) - ∫ y in (0:ℝ)..L₀, q * y ^ (q - 1) * B x₀ (x₀ + y) := by
  -- the open interval of `y ↦ x₀ + y` on which the slice is known to be smooth
  set S : Set ℝ := Set.Ioo (c - x₀) (d - x₀) with hSdef
  have hS_nhds : ∀ y ∈ S, x₀ + y ∈ Set.Ioo c d := by
    intro y hy
    simp only [hSdef, Set.mem_Ioo] at hy
    exact ⟨by linarith [hy.1], by linarith [hy.2]⟩
  -- smoothness of the slice `v ↦ B x₀ v`
  have hslice : ContDiffOn ℝ 1 (fun v : ℝ => B x₀ v) (Set.Ioo c d) :=
    contDiffOn_slice_right hx₁ hx₂ hB
  -- smoothness of the shifted slice `y ↦ B x₀ (x₀ + y)`
  have hF : ContDiffOn ℝ 1 (fun y : ℝ => B x₀ (x₀ + y)) S := by
    have hinner : ContDiffOn ℝ 1 (fun y : ℝ => ((x₀ : ℝ), x₀ + y)) S :=
      contDiffOn_const.prodMk (contDiffOn_const.add contDiffOn_id)
    have h := hB.comp hinner (fun y hy => ⟨⟨hx₁, hx₂⟩, hS_nhds y hy⟩)
    simpa [Function.comp_def] using h
  -- the chain rule identifies the derivative of the shifted slice
  have hderivF : ∀ y ∈ S, HasDerivAt (fun y : ℝ => B x₀ (x₀ + y))
      (deriv (fun v : ℝ => B x₀ v) (x₀ + y)) y := by
    intro y hy
    have hd_slice : DifferentiableAt ℝ (fun v : ℝ => B x₀ v) (x₀ + y) :=
      (hslice.differentiableOn (by norm_num)).differentiableAt
        (isOpen_Ioo.mem_nhds (hS_nhds y hy))
    have h1 : HasDerivAt (fun y : ℝ => x₀ + y) 1 y := hasDerivAt_id y |>.const_add x₀
    have h2 := (hd_slice.hasDerivAt).comp y h1
    simpa [Function.comp_def, mul_one] using h2
  -- the slice derivative, transported to the `y`-line, is continuous
  have hcont_deriv : ContinuousOn (fun y : ℝ => deriv (fun v : ℝ => B x₀ v) (x₀ + y))
      (Set.uIcc (0:ℝ) L₀) := by
    have hd_cont : ContinuousOn (deriv (fun v : ℝ => B x₀ v)) (Set.Ioo c d) :=
      hslice.continuousOn_deriv_of_isOpen isOpen_Ioo le_rfl
    have hshift : ContinuousOn (fun y : ℝ => x₀ + y) (Set.uIcc (0:ℝ) L₀) := by fun_prop
    refine hd_cont.comp hshift ?_
    rw [Set.uIcc_of_le hL.le]
    intro y hy
    exact ⟨by linarith [hy.1], by linarith [hy.2]⟩
  -- the two `'`-functions are interval integrable
  have hu' : IntervalIntegrable (fun y : ℝ => q * y ^ (q - 1)) volume (0:ℝ) L₀ :=
    (intervalIntegral.intervalIntegrable_rpow'
      (a := (0:ℝ)) (b := L₀) (by linarith : (-1:ℝ) < q - 1)).const_mul q
  have hv' : IntervalIntegrable (fun y : ℝ => deriv (fun v : ℝ => B x₀ v) (x₀ + y))
      volume (0:ℝ) L₀ :=
    hcont_deriv.intervalIntegrable
  -- continuity on the closed interval
  have hu : ContinuousOn (fun y : ℝ => y ^ q) (Set.uIcc (0:ℝ) L₀) :=
    (continuous_id.rpow_const (fun _ => Or.inr hq.le)).continuousOn
  have hv : ContinuousOn (fun y : ℝ => B x₀ (x₀ + y)) (Set.uIcc (0:ℝ) L₀) := by
    refine hF.continuousOn.mono ?_
    rw [Set.uIcc_of_le hL.le]
    intro y hy
    exact ⟨by linarith [hy.1], by linarith [hy.2]⟩
  -- one-sided derivatives on the open interval
  have huu' : ∀ y ∈ Set.Ioo (min (0:ℝ) L₀) (max (0:ℝ) L₀),
      HasDerivWithinAt (fun y : ℝ => y ^ q) (q * y ^ (q - 1)) (Set.Ioi y) y := by
    intro y hy
    rw [min_eq_left hL.le, max_eq_right hL.le] at hy
    exact (Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt hy.1))).hasDerivWithinAt
  have hvv' : ∀ y ∈ Set.Ioo (min (0:ℝ) L₀) (max (0:ℝ) L₀),
      HasDerivWithinAt (fun y : ℝ => B x₀ (x₀ + y))
        (deriv (fun v : ℝ => B x₀ v) (x₀ + y)) (Set.Ioi y) y := by
    intro y hy
    rw [min_eq_left hL.le, max_eq_right hL.le] at hy
    have hyS : y ∈ S := by
      simp only [hSdef, Set.mem_Ioo]; exact ⟨by linarith [hy.1], by linarith [hy.2]⟩
    exact (hderivF y hyS).hasDerivWithinAt
  -- integration by parts
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDeriv_right
    (a := (0:ℝ)) (b := L₀) (u := fun y : ℝ => y ^ q) (u' := fun y : ℝ => q * y ^ (q - 1))
    (v := fun y : ℝ => B x₀ (x₀ + y)) (v' := fun y : ℝ => deriv (fun v : ℝ => B x₀ v) (x₀ + y))
    hu hv huu' hvv' hu' hv'
  rw [hibp]
  simp only [Real.zero_rpow hq.ne', zero_mul, sub_zero, add_zero]

end Work.Analysis.Abel
