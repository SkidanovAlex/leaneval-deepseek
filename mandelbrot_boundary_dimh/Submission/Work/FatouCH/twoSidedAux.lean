import Mathlib
import Submission.Unif.Commons.Analysis.Complex.Analytic.deriv_ne_zero_of_injOn

/-!
# Shared auxiliaries for the two-sided Koebe bound (`Work.FatouCH.koebeTwoSided`)

Geometry of the ball, non-vanishing of the derivative of a univalent map, and the
normalised rescaling `u ↦ (Φ (z + s u) - Φ z) / (s Φ' z)` of a univalent `Φ`, which turns
the Abel relation `Φ (z + v z) = Φ z + 1` into a statement about a univalent function on the
unit disc with value `0` and derivative `1` at the origin.
-/

namespace Work.FatouCH

open Metric Set Complex
open scoped Topology

/-- If `‖w - 1‖ < 1/4` then `‖w‖ > 3/4`. -/
lemma norm_gt_three_quarters_of_norm_sub_one_lt {w : ℂ} (h : ‖w - 1‖ < 1 / 4) : 3 / 4 < ‖w‖ := by
  have h2 : ‖(1 : ℂ)‖ ≤ ‖w‖ + ‖(1 : ℂ) - w‖ := by
    calc ‖(1 : ℂ)‖ = ‖w + ((1 : ℂ) - w)‖ := by ring_nf
      _ ≤ ‖w‖ + ‖(1 : ℂ) - w‖ := norm_add_le _ _
  have h3 : ‖(1 : ℂ) - w‖ = ‖w - 1‖ := by rw [← norm_neg (w - 1)]; ring_nf
  rw [norm_one, h3] at h2
  linarith

/-- If `z ∈ ball z₀ (R - c)` and `‖w‖ < c` then `z + w ∈ ball z₀ R`. -/
lemma add_mem_ball_of_norm_lt {z₀ z w : ℂ} {R c : ℝ}
    (hz : z ∈ Metric.ball z₀ (R - c)) (hw : ‖w‖ < c) : z + w ∈ Metric.ball z₀ R := by
  rw [Metric.mem_ball] at hz ⊢
  have h1 : dist (z + w) z₀ ≤ dist (z + w) z + dist z z₀ := dist_triangle _ _ _
  have h2 : dist (z + w) z = ‖w‖ := by rw [dist_eq_norm, add_sub_cancel_left]
  linarith

/-- If `z ∈ ball z₀ (R - 2)`, `‖s‖ ≤ 2` and `‖u‖ < 1`, then `z + s * u ∈ ball z₀ R`. -/
lemma add_mul_mem_ball_of_norm_le {z₀ z s u : ℂ} {R : ℝ}
    (hz : z ∈ Metric.ball z₀ (R - 2)) (hs : ‖s‖ ≤ 2) (hu : ‖u‖ < 1) :
    z + s * u ∈ Metric.ball z₀ R := by
  refine add_mem_ball_of_norm_lt (c := 2) hz ?_
  calc ‖s * u‖ = ‖s‖ * ‖u‖ := norm_mul s u
    _ ≤ 2 * ‖u‖ := mul_le_mul_of_nonneg_right hs (norm_nonneg u)
    _ < 2 := by linarith

/-- The derivative of a holomorphic injective function does not vanish. -/
theorem deriv_ne_zero_of_differentiableOn_injOn_ball {Φ : ℂ → ℂ} {z₀ : ℂ} {R : ℝ}
    (hΦ : DifferentiableOn ℂ Φ (Metric.ball z₀ R)) (hinj : Set.InjOn Φ (Metric.ball z₀ R))
    {z : ℂ} (hz : z ∈ Metric.ball z₀ R) : deriv Φ z ≠ 0 := by
  have hz' : dist z z₀ < R := by simpa [Metric.mem_ball] using hz
  have hr : 0 < R - dist z z₀ := by linarith
  have hsub : Metric.ball z (R - dist z z₀) ⊆ Metric.ball z₀ R := by
    intro w hw
    rw [Metric.mem_ball] at hw ⊢
    calc dist w z₀ ≤ dist w z + dist z z₀ := dist_triangle _ _ _
      _ < R - dist z z₀ + dist z z₀ := by linarith
      _ = R := by ring
  refine Commons.Analysis.Complex.Analytic.deriv_ne_zero_of_injOn (f := Φ) (c := z)
    (r := R - dist z z₀) hr ?_ (hinj.mono hsub)
  exact (hΦ.analyticOn isOpen_ball).analyticAt (isOpen_ball.mem_nhds hz)

/-- The normalised rescaling `u ↦ (Φ (z + s u) - Φ z) / (s Φ' z)` of `Φ`. -/
noncomputable def normedTransform (Φ : ℂ → ℂ) (z s : ℂ) : ℂ → ℂ :=
  fun u => (Φ (z + s * u) - Φ z) / (s * deriv Φ z)

lemma normedTransform_apply (Φ : ℂ → ℂ) (z s u : ℂ) :
    normedTransform Φ z s u = (Φ (z + s * u) - Φ z) / (s * deriv Φ z) := rfl

/-- `normedTransform Φ z s` is holomorphic on the unit disc when `Φ` is holomorphic on the ball,
`‖s‖ ≤ 2` and `z ∈ ball z₀ (R-2)`. -/
theorem normedTransform_analyticAt {Φ : ℂ → ℂ} {z₀ z s : ℂ} {R : ℝ}
    (hΦ : DifferentiableOn ℂ Φ (Metric.ball z₀ R)) (hz : z ∈ Metric.ball z₀ (R - 2))
    (hs : ‖s‖ ≤ 2) :
    ∀ u ∈ Metric.ball (0 : ℂ) 1, AnalyticAt ℂ (normedTransform Φ z s) u := by
  intro u hu
  have hu1 : ‖u‖ < 1 := by simpa [Metric.mem_ball, dist_eq_norm] using hu
  have hmem : z + s * u ∈ Metric.ball z₀ R := add_mul_mem_ball_of_norm_le hz hs hu1
  have hPhi : AnalyticAt ℂ Φ (z + s * u) :=
    (hΦ.analyticOn isOpen_ball).analyticAt (isOpen_ball.mem_nhds hmem)
  have hinner : AnalyticAt ℂ (fun u : ℂ => z + s * u) u := by fun_prop
  have h1 : AnalyticAt ℂ (fun u : ℂ => Φ (z + s * u)) u := by
    have h := hPhi.comp (f := fun u : ℂ => z + s * u) (g := Φ) (x := u) hinner
    simpa [Function.comp_def] using h
  have h2 : AnalyticAt ℂ ((fun u : ℂ => Φ (z + s * u)) - fun _ : ℂ => Φ z) u :=
    h1.sub analyticAt_const
  have h3 : AnalyticAt ℂ (fun u : ℂ => (Φ (z + s * u) - Φ z) / (s * deriv Φ z)) u :=
    h2.div_const (c := s * deriv Φ z)
  rw [show normedTransform Φ z s = fun u : ℂ => (Φ (z + s * u) - Φ z) / (s * deriv Φ z)
    from rfl]
  exact h3

/-- `normedTransform Φ z s` is injective on the unit disc if `Φ` is injective on the ball and
`s ≠ 0`. -/
theorem normedTransform_injOn {Φ : ℂ → ℂ} {z₀ z s : ℂ} {R : ℝ}
    (hinj : Set.InjOn Φ (Metric.ball z₀ R)) (hz : z ∈ Metric.ball z₀ (R - 2))
    (hs : ‖s‖ ≤ 2) (hne : s ≠ 0) (hd : deriv Φ z ≠ 0) :
    Set.InjOn (normedTransform Φ z s) (Metric.ball (0 : ℂ) 1) := by
  intro a ha b hb hab
  have hn : ‖a‖ < 1 := by simpa [Metric.mem_ball, dist_eq_norm] using ha
  have hn' : ‖b‖ < 1 := by simpa [Metric.mem_ball, dist_eq_norm] using hb
  have hmem : z + s * a ∈ Metric.ball z₀ R := add_mul_mem_ball_of_norm_le hz hs hn
  have hmem' : z + s * b ∈ Metric.ball z₀ R := add_mul_mem_ball_of_norm_le hz hs hn'
  have hc : s * deriv Φ z ≠ 0 := mul_ne_zero hne hd
  have h1 : (Φ (z + s * a) - Φ z) / (s * deriv Φ z)
      = (Φ (z + s * b) - Φ z) / (s * deriv Φ z) := by
    simpa [normedTransform] using hab
  have h2 : Φ (z + s * a) - Φ z = Φ (z + s * b) - Φ z := by
    have h := congrArg (fun y : ℂ => y * (s * deriv Φ z)) h1
    rwa [div_mul_cancel₀ _ hc, div_mul_cancel₀ _ hc] at h
  have h3 : Φ (z + s * a) = Φ (z + s * b) := by
    have h := congrArg (fun y : ℂ => y + Φ z) h2
    simpa using h
  have h4 : z + s * a = z + s * b := hinj hmem hmem' h3
  have h5 : s * a = s * b := add_left_cancel h4
  exact mul_left_cancel₀ hne h5

lemma normedTransform_zero (Φ : ℂ → ℂ) (z s : ℂ) : normedTransform Φ z s 0 = 0 := by
  simp [normedTransform]

/-- `normedTransform Φ z s` has derivative `1` at `0`. -/
theorem normedTransform_deriv_zero {Φ : ℂ → ℂ} {z₀ z s : ℂ} {R : ℝ}
    (hΦ : DifferentiableOn ℂ Φ (Metric.ball z₀ R)) (hz : z ∈ Metric.ball z₀ R)
    (hne : s * deriv Φ z ≠ 0) :
    deriv (normedTransform Φ z s) 0 = 1 := by
  have hdiff : DifferentiableAt ℂ Φ z := hΦ.differentiableAt (isOpen_ball.mem_nhds hz)
  have hinner : HasDerivAt (fun u : ℂ => z + s * u) s 0 := by
    simpa using (hasDerivAt_const_mul s (x := (0 : ℂ))).const_add z
  have hd' : HasDerivAt Φ (deriv Φ z) ((fun u : ℂ => z + s * u) 0) := by
    simpa using hdiff.hasDerivAt
  have h1 : HasDerivAt (fun u : ℂ => Φ (z + s * u)) (deriv Φ z * s) 0 := by
    have h := hd'.comp (0 : ℂ) hinner
    simpa [Function.comp_def] using h
  have h2 : HasDerivAt (fun u : ℂ => Φ (z + s * u) - Φ z) (deriv Φ z * s) 0 :=
    h1.sub_const (Φ z)
  have h3 : HasDerivAt (fun u : ℂ => (Φ (z + s * u) - Φ z) / (s * deriv Φ z))
      ((deriv Φ z * s) / (s * deriv Φ z)) 0 := h2.div_const (s * deriv Φ z)
  have h4 : (deriv Φ z * s) / (s * deriv Φ z) = 1 := by
    rw [mul_comm (deriv Φ z) s]; exact div_self hne
  have h5 : deriv (fun u : ℂ => (Φ (z + s * u) - Φ z) / (s * deriv Φ z)) 0 = 1 :=
    h3.deriv.trans h4
  rw [show normedTransform Φ z s = fun u : ℂ => (Φ (z + s * u) - Φ z) / (s * deriv Φ z)
    from rfl]
  exact h5

/-- If `‖w - 1‖ < 1/4` then `‖w / 2‖ < 5/8`. -/
lemma norm_div_two_lt_five_eighths {w : ℂ} (h : ‖w - 1‖ < 1 / 4) : ‖w / 2‖ < 5 / 8 := by
  have h1 : ‖w‖ ≤ ‖w - 1‖ + ‖(1 : ℂ)‖ := by
    calc ‖w‖ = ‖(w - 1) + 1‖ := by ring_nf
      _ ≤ ‖w - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
  rw [norm_one] at h1
  have h2 : ‖w / 2‖ = ‖w‖ / 2 := by rw [norm_div]; norm_num
  rw [h2]
  linarith

/-- Monotonicity of the growth-bound expression when `t ≤ 5/8`. -/
lemma rpow_one_add_div_one_sub_le {t ρ : ℝ} (hρ : 0 < ρ) (ht0 : 0 ≤ t) (ht : t ≤ 5 / 8) :
    ((1 + t) / (1 - t)) ^ (1 / ρ) ≤ (13 / 3) ^ (1 / ρ) := by
  have ht1 : 0 < 1 - t := by linarith
  have h0 : 0 ≤ (1 + t) / (1 - t) := div_nonneg (by linarith) ht1.le
  have h2 : (1 + t) / (1 - t) ≤ 13 / 3 := by
    rw [div_le_iff₀ ht1]
    linarith
  exact Real.rpow_le_rpow h0 h2 (by positivity)

end Work.FatouCH
