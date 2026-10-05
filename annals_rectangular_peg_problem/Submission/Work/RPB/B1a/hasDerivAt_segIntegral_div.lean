/-
# Differentiation under the integral sign for the parametrized segment integral (B1a)

`segIntegral (fun ζ => f ζ * (ζ - w)⁻¹) a b` is a Cauchy-type integral of `f` along the segment
`[a,b]`, viewed as a function of the pole `w`.  This file proves that off the segment it is
complex differentiable in `w`, with derivative
`segIntegral (fun ζ => f ζ * (ζ - w)⁻²) a b`; the sign is the expected one because
`d/dw (ζ - w)⁻¹ = (ζ - w)⁻²`.

The proof is an application of differentiation under the integral sign for interval integrals
(`intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le`).  The two inputs are:

* `w ∉ segment ℝ a b` gives a positive distance `d` from `w` to the compact segment, hence a
  positive lower bound for `‖ζ - x‖` for `x` near `w` and `ζ` on the segment
  (`exists_ball_forall_le_norm_segment_sub`);
* `f` is continuous on the compact segment, hence bounded there by some `C`.

The derivative of the integrand in the parameter is bounded by the constant
`C * d⁻² * ‖b - a‖`, which is integrable on `[0,1]`.
-/
import Mathlib
import Submission.Work.RPB.B1a.SegChain
import Submission.Work.RPB.B1a.exists_ball_forall_le_norm_segment_sub

namespace Work.RPB.B1a

open Complex Set MeasureTheory intervalIntegral
open scoped Topology

noncomputable section

/-- The segment `[a,b]` in `ℂ` is compact (it is a continuous image of `Icc 0 1`). -/
private lemma isCompact_segment' (a b : ℂ) : IsCompact (segment ℝ a b) := by
  rw [segment_eq_image]
  exact isCompact_Icc.image (by continuity)

/-- The derivative of `y ↦ (c - y)⁻¹` at `x`.  The chain rule produces
`-(-(c - x)²)⁻¹ = (c - x)^(-2 : ℤ)`, the form in which the derivative appears in
`hasDerivAt_segIntegral_div`. -/
private lemma hasDerivAt_sub_inv {c x : ℂ} (h : c ≠ x) :
    HasDerivAt (fun y : ℂ => (c - y)⁻¹) ((c - x) ^ (-2 : ℤ)) x := by
  have h1 : HasDerivAt (fun y : ℂ => c - y) (-1) x :=
    (hasDerivAt_id (x := x)).const_sub c
  have h2 := (hasDerivAt_inv (x := c - x) (sub_ne_zero.mpr h)).comp x h1
  convert h2 using 1
  · ext y; simp
  · rw [zpow_neg, zpow_ofNat]; ring

theorem hasDerivAt_segIntegral_div {f : ℂ → ℂ} {a b w : ℂ}
    (hw : w ∉ segment ℝ a b) (hf : ContinuousOn f (segment ℝ a b)) :
    HasDerivAt (fun w => segIntegral (fun ζ => f ζ * (ζ - w)⁻¹) a b)
      (segIntegral (fun ζ => f ζ * (ζ - w) ^ (-2 : ℤ)) a b) w := by
  -- Positive distance from `w` to the segment, and a bound for `f` on the segment.
  obtain ⟨d, hdpos, hd⟩ := exists_ball_forall_le_norm_segment_sub hw
  obtain ⟨C, hC⟩ := (isCompact_segment' a b).exists_bound_of_continuousOn hf
  have hCnn : 0 ≤ C := le_trans (norm_nonneg (f a)) (hC a (left_mem_segment ℝ a b))
  -- The parametrization of the segment.
  let γ : ℝ → ℂ := fun t => a + (t : ℂ) * (b - a)
  have hγcont : Continuous γ := by dsimp only [γ]; fun_prop
  have hγmem : MapsTo γ (uIcc (0:ℝ) 1) (segment ℝ a b) := by
    intro t ht
    exact mem_segment_param (by simpa [uIcc_of_le zero_le_one] using ht)
  -- The pole stays off the parametrized segment.
  have hne : ∀ x ∈ Metric.ball w d, ∀ t ∈ uIcc (0:ℝ) 1, γ t - x ≠ 0 := by
    intro x hx t ht h
    have h1 : d ≤ ‖γ t - x‖ := hd x hx (γ t) (hγmem ht)
    rw [h, norm_zero] at h1
    linarith
  have hF_cont : ∀ x ∈ Metric.ball w d, ContinuousOn
      (fun t : ℝ => f (γ t) * (γ t - x)⁻¹ * (b - a)) (uIcc (0:ℝ) 1) := by
    intro x hx
    have h1 : ContinuousOn (fun t : ℝ => f (γ t)) (uIcc (0:ℝ) 1) :=
      hf.comp hγcont.continuousOn hγmem
    have h2 : ContinuousOn (fun t : ℝ => (γ t - x)⁻¹) (uIcc (0:ℝ) 1) :=
      ContinuousOn.inv₀ (hγcont.continuousOn.sub continuousOn_const)
        (fun t ht => hne x hx t ht)
    exact (h1.mul h2).mul (continuousOn_const (c := b - a))
  have hF'_cont : ∀ x ∈ Metric.ball w d, ContinuousOn
      (fun t : ℝ => f (γ t) * (γ t - x) ^ (-2 : ℤ) * (b - a)) (uIcc (0:ℝ) 1) := by
    intro x hx
    have h1 : ContinuousOn (fun t : ℝ => f (γ t)) (uIcc (0:ℝ) 1) :=
      hf.comp hγcont.continuousOn hγmem
    have hsub : ContinuousOn (fun t : ℝ => γ t - x) (uIcc (0:ℝ) 1) :=
      hγcont.continuousOn.sub continuousOn_const
    have h2 : ContinuousOn (fun t : ℝ => ((γ t - x) ^ 2)⁻¹) (uIcc (0:ℝ) 1) :=
      ContinuousOn.inv₀ (hsub.pow 2) (fun t ht => pow_ne_zero 2 (hne x hx t ht))
    have h2' : ContinuousOn (fun t : ℝ => (γ t - x) ^ (-2 : ℤ)) (uIcc (0:ℝ) 1) := by
      convert h2 using 1
      ext t
      rw [zpow_neg, zpow_ofNat]
    exact (h1.mul h2').mul (continuousOn_const (c := b - a))
  have hs_mem : Metric.ball w d ∈ 𝓝 w := Metric.ball_mem_nhds w hdpos
  have hw_ball : w ∈ Metric.ball w d := Metric.mem_ball_self hdpos
  have hF_meas : ∀ᶠ x in 𝓝 w, AEStronglyMeasurable
      (fun t : ℝ => f (γ t) * (γ t - x)⁻¹ * (b - a)) (volume.restrict (uIoc (0:ℝ) 1)) := by
    filter_upwards [hs_mem] with x hx
    exact ((hF_cont x hx).mono uIoc_subset_uIcc).aestronglyMeasurable measurableSet_uIoc
  have hF'_meas : AEStronglyMeasurable
      (fun t : ℝ => f (γ t) * (γ t - w) ^ (-2 : ℤ) * (b - a))
      (volume.restrict (uIoc (0:ℝ) 1)) :=
    ((hF'_cont w hw_ball).mono uIoc_subset_uIcc).aestronglyMeasurable measurableSet_uIoc
  have hF_int : IntervalIntegrable
      (fun t : ℝ => f (γ t) * (γ t - w)⁻¹ * (b - a)) volume 0 1 :=
    ContinuousOn.intervalIntegrable (hF_cont w hw_ball)
  have hbound_int : IntervalIntegrable (fun _ : ℝ => C * (d ^ 2)⁻¹ * ‖b - a‖) volume 0 1 :=
    intervalIntegrable_const
  -- Uniform bound on the parameter derivative of the integrand.
  have h_bound : ∀ᵐ t ∂volume, t ∈ uIoc (0:ℝ) 1 →
      ∀ x ∈ Metric.ball w d,
        ‖f (γ t) * (γ t - x) ^ (-2:ℤ) * (b - a)‖ ≤ C * (d^2)⁻¹ * ‖b - a‖ := by
    refine Filter.Eventually.of_forall (fun t ht x hx => ?_)
    have ht' : t ∈ uIcc (0:ℝ) 1 := uIoc_subset_uIcc ht
    have hmem : γ t ∈ segment ℝ a b := hγmem ht'
    have hfx : ‖f (γ t)‖ ≤ C := hC (γ t) hmem
    have hdist : d ≤ ‖γ t - x‖ := hd x hx (γ t) hmem
    have hne0 : γ t - x ≠ 0 := hne x hx t ht'
    have hnorminv : ‖(γ t - x) ^ (-2:ℤ)‖ = (‖γ t - x‖^2)⁻¹ := by
      rw [norm_zpow, zpow_neg, zpow_ofNat]
    have hle : (‖γ t - x‖^2)⁻¹ ≤ (d^2)⁻¹ := by
      have h1 : d^2 ≤ ‖γ t - x‖^2 := by
        nlinarith [norm_nonneg (γ t - x), le_of_lt hdpos]
      exact (inv_le_inv₀ (pow_pos (norm_pos_iff.mpr hne0) 2) (pow_pos hdpos 2)).mpr h1
    rw [norm_mul, norm_mul, hnorminv]
    exact mul_le_mul (mul_le_mul hfx hle (by positivity) hCnn) le_rfl (norm_nonneg _)
      (mul_nonneg hCnn (by positivity))
  -- Pointwise derivative of `x ↦ f (γ t) * (γ t - x)⁻¹ * (b - a)`.
  have h_diff : ∀ᵐ t ∂volume, t ∈ uIoc (0:ℝ) 1 →
      ∀ x ∈ Metric.ball w d,
        HasDerivAt (fun x : ℂ => f (γ t) * (γ t - x)⁻¹ * (b - a))
          (f (γ t) * (γ t - x) ^ (-2:ℤ) * (b - a)) x := by
    refine Filter.Eventually.of_forall (fun t ht x hx => ?_)
    have ht' : t ∈ uIcc (0:ℝ) 1 := uIoc_subset_uIcc ht
    have hne' : γ t ≠ x := by
      intro h
      have h1 : d ≤ ‖γ t - x‖ := hd x hx (γ t) (hγmem ht')
      rw [h, sub_self, norm_zero] at h1
      linarith
    exact (hasDerivAt_sub_inv hne').const_mul (f (γ t)) |>.mul_const (b - a)
  have main := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (a := (0:ℝ)) (b := 1)
    (F := fun x t => f (γ t) * (γ t - x)⁻¹ * (b - a))
    (F' := fun x t => f (γ t) * (γ t - x) ^ (-2:ℤ) * (b - a))
    (x₀ := w) (s := Metric.ball w d) (bound := fun _ : ℝ => C * (d^2)⁻¹ * ‖b - a‖)
    hs_mem hF_meas hF_int hF'_meas h_bound hbound_int h_diff
  simpa only [segIntegral, γ] using main.2

end

end Work.RPB.B1a
