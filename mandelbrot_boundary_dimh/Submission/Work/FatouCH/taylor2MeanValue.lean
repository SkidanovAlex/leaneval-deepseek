import Mathlib

namespace Work.FatouCH

open Set Metric

/-- Second-order Taylor bound, in the mean-value form that keeps the linear term evaluated at the *centre* `z₀`. If `f` is holomorphic on `ball z₀ R` (`R ≥ 3`) and `‖iteratedDeriv 3 f‖ ≤ S` on `ball z₀ (5/4)`, then for `‖w‖ < 5/4` we have `‖f (z₀+w) - f z₀ - w * deriv f z₀ - (w^2/2) * iteratedDeriv 2 f z₀‖ ≤ (125/64) * S`. Apply `Convex.norm_image_sub_le_of_norm_deriv_le` on the convex set `ball z₀ (5/4)` (which contains the segment from `z₀` to `z₀ + w`) to `q z = f z - f z₀ - (z-z₀) deriv f z₀ - ((z-z₀)^2/2) iteratedDeriv 2 f z₀`, twice (to `q` and to `deriv q`), using `q z₀ = deriv q z₀ = 0` and `‖iteratedDeriv 2 q‖ = ‖iteratedDeriv 2 f - iteratedDeriv 2 f z₀‖ ≤ (5/4) S` on that ball. -/
theorem taylor2MeanValue {f : ℂ → ℂ} {z₀ : ℂ} {R S : ℝ} (hR : 3 ≤ R)
    (hf : DifferentiableOn ℂ f (Metric.ball z₀ R))
    (hS : ∀ ζ ∈ Metric.ball z₀ (5 / 4), ‖iteratedDeriv 3 f ζ‖ ≤ S)
    {w : ℂ} (hw : ‖w‖ < 5 / 4) :
    ‖f (z₀ + w) - f z₀ - w * deriv f z₀ - (w ^ 2 / 2) * iteratedDeriv 2 f z₀‖
      ≤ (125 / 64) * S := by
  have hz₀ : z₀ ∈ Metric.ball z₀ (5/4:ℝ) := Metric.mem_ball_self (by norm_num)
  have hzw : z₀ + w ∈ Metric.ball z₀ (5/4:ℝ) := by
    rw [Metric.mem_ball, dist_eq_norm]
    simpa using hw
  have hS0 : 0 ≤ S := le_trans (norm_nonneg _) (hS z₀ hz₀)
  have hsub : Metric.ball z₀ (5/4:ℝ) ⊆ Metric.ball z₀ R := Metric.ball_subset_ball (by linarith)
  have hBopen : IsOpen (Metric.ball z₀ (5/4:ℝ)) := Metric.isOpen_ball
  have hBconv : Convex ℝ (Metric.ball z₀ (5/4:ℝ)) := convex_ball _ _
  have hfB : DifferentiableOn ℂ f (Metric.ball z₀ (5/4:ℝ)) := hf.mono hsub
  have hd1 : DifferentiableOn ℂ (deriv f) (Metric.ball z₀ (5/4:ℝ)) := hfB.deriv hBopen
  have hiterfun : iteratedDeriv 2 f = deriv (deriv f) := by
    rw [iteratedDeriv_eq_iterate]; rfl
  have hd2 : DifferentiableOn ℂ (iteratedDeriv 2 f) (Metric.ball z₀ (5/4:ℝ)) := by
    rw [hiterfun]; exact hd1.deriv hBopen
  have hfAt : ∀ x ∈ Metric.ball z₀ (5/4:ℝ), DifferentiableAt ℂ f x :=
    fun x hx => (hfB x hx).differentiableAt (hBopen.mem_nhds hx)
  have hd1At : ∀ x ∈ Metric.ball z₀ (5/4:ℝ), DifferentiableAt ℂ (deriv f) x :=
    fun x hx => (hd1 x hx).differentiableAt (hBopen.mem_nhds hx)
  have hd2At : ∀ x ∈ Metric.ball z₀ (5/4:ℝ), DifferentiableAt ℂ (iteratedDeriv 2 f) x :=
    fun x hx => (hd2 x hx).differentiableAt (hBopen.mem_nhds hx)
  -- First mean value estimate: the second derivative varies by at most `S · ‖y - z₀‖`.
  have hstepA : ∀ y ∈ Metric.ball z₀ (5/4:ℝ),
      ‖iteratedDeriv 2 f y - iteratedDeriv 2 f z₀‖ ≤ S * ‖y - z₀‖ := by
    intro y hy
    have hbd : ∀ x ∈ Metric.ball z₀ (5/4:ℝ), ‖deriv (iteratedDeriv 2 f) x‖ ≤ S := by
      intro x hx
      rw [← iteratedDeriv_succ]
      exact hS x hx
    exact hBconv.norm_image_sub_le_of_norm_deriv_le (f := iteratedDeriv 2 f) (C := S)
      (fun x hx => hd2At x hx) hbd (x := z₀) (y := y) hz₀ hy
  -- The first-order remainder `G z = f'(z) - f'(z₀) - (z - z₀) f''(z₀)`, with `G z₀ = 0`.
  set G : ℂ → ℂ := fun z : ℂ => deriv f z - deriv f z₀ - (z - z₀) * iteratedDeriv 2 f z₀ with hG
  have hGz₀ : G z₀ = 0 := by rw [hG]; simp
  have hGAt : ∀ x ∈ Metric.ball z₀ (5/4:ℝ),
      HasDerivAt G (iteratedDeriv 2 f x - iteratedDeriv 2 f z₀) x := by
    intro x hx
    rw [hG]
    have h1 : HasDerivAt (fun z : ℂ => deriv f z - deriv f z₀) (deriv (deriv f) x) x :=
      (hd1At x hx).hasDerivAt.sub_const (deriv f z₀)
    have h2 : HasDerivAt (fun z : ℂ => (z - z₀) * iteratedDeriv 2 f z₀)
        (iteratedDeriv 2 f z₀) x := by
      simpa using (((hasDerivAt_id' x).sub_const z₀).mul_const (iteratedDeriv 2 f z₀))
    have h := h1.sub h2
    convert h using 1
    rw [hiterfun]
  have hBoundB : ∀ y ∈ Metric.ball z₀ (5/4:ℝ),
      ‖iteratedDeriv 2 f y - iteratedDeriv 2 f z₀‖ ≤ (5/4) * S := by
    intro y hy
    have h1 := hstepA y hy
    have h2 : ‖y - z₀‖ ≤ 5/4 := by
      rw [← dist_eq_norm]; exact (Metric.mem_ball.mp hy).le
    calc ‖iteratedDeriv 2 f y - iteratedDeriv 2 f z₀‖ ≤ S * ‖y - z₀‖ := h1
      _ ≤ S * (5/4) := mul_le_mul_of_nonneg_left h2 hS0
      _ = (5/4) * S := by ring
  have hMB : ‖G (z₀ + w) - G z₀‖ ≤ ((5/4) * S) * ‖w‖ := by
    have h := hBconv.norm_image_sub_le_of_norm_hasDerivWithin_le (f := G)
      (f' := fun x => iteratedDeriv 2 f x - iteratedDeriv 2 f z₀) (C := (5/4) * S)
      (fun x hx => (hGAt x hx).hasDerivWithinAt) (fun x hx => hBoundB x hx)
      (x := z₀) (y := z₀ + w) hz₀ hzw
    simpa using h
  have hBoundC : ∀ y ∈ Metric.ball z₀ (5/4:ℝ), ‖G y‖ ≤ (25/16) * S := by
    intro y hy
    have h1 : ‖G y - G z₀‖ ≤ ((5/4) * S) * ‖y - z₀‖ := by
      have h := hBconv.norm_image_sub_le_of_norm_hasDerivWithin_le (f := G)
        (f' := fun x => iteratedDeriv 2 f x - iteratedDeriv 2 f z₀) (C := (5/4) * S)
        (fun x hx => (hGAt x hx).hasDerivWithinAt) (fun x hx => hBoundB x hx)
        (x := z₀) (y := y) hz₀ hy
      simpa using h
    rw [hGz₀, sub_zero] at h1
    have h2 : ‖y - z₀‖ ≤ 5/4 := by
      rw [← dist_eq_norm]; exact (Metric.mem_ball.mp hy).le
    calc ‖G y‖ ≤ ((5/4) * S) * ‖y - z₀‖ := h1
      _ ≤ ((5/4) * S) * (5/4) := mul_le_mul_of_nonneg_left h2 (mul_nonneg (by norm_num) hS0)
      _ = (25/16) * S := by ring
  -- The second-order remainder `Q z = f z - f z₀ - (z - z₀) f'(z₀) - ((z - z₀)^2/2) f''(z₀)`.
  set Q : ℂ → ℂ := fun z : ℂ =>
      f z - f z₀ - (z - z₀) * deriv f z₀ - ((z - z₀) ^ 2 / 2) * iteratedDeriv 2 f z₀ with hQ
  have hQz₀ : Q z₀ = 0 := by rw [hQ]; simp
  have hQAt : ∀ x ∈ Metric.ball z₀ (5/4:ℝ), HasDerivAt Q (G x) x := by
    intro x hx
    rw [hQ, hG]
    have h1 : HasDerivAt (fun z : ℂ => f z - f z₀) (deriv f x) x :=
      (hfAt x hx).hasDerivAt.sub_const (f z₀)
    have h2 : HasDerivAt (fun z : ℂ => (z - z₀) * deriv f z₀) (deriv f z₀) x := by
      simpa using (((hasDerivAt_id' x).sub_const z₀).mul_const (deriv f z₀))
    have h3 : HasDerivAt (fun z : ℂ => ((z - z₀) ^ 2 / 2) * iteratedDeriv 2 f z₀)
        ((x - z₀) * iteratedDeriv 2 f z₀) x := by
      have h0 : HasDerivAt (fun z : ℂ => ((z - z₀) ^ 2 / 2) * iteratedDeriv 2 f z₀)
          (((2 : ℂ) * (x - z₀) ^ (2 - 1) * 1) / 2 * iteratedDeriv 2 f z₀) x :=
        ((((hasDerivAt_id' x).sub_const z₀).pow 2).div_const 2).mul_const (iteratedDeriv 2 f z₀)
      convert h0 using 1
      ring
    exact (h1.sub h2).sub h3
  have hMQ : ‖Q (z₀ + w) - Q z₀‖ ≤ ((25/16) * S) * ‖w‖ := by
    have h := hBconv.norm_image_sub_le_of_norm_hasDerivWithin_le (f := Q) (f' := G)
      (C := (25/16) * S)
      (fun x hx => (hQAt x hx).hasDerivWithinAt) (fun x hx => hBoundC x hx)
      (x := z₀) (y := z₀ + w) hz₀ hzw
    simpa using h
  have hQval : Q (z₀ + w) =
      f (z₀ + w) - f z₀ - w * deriv f z₀ - (w ^ 2 / 2) * iteratedDeriv 2 f z₀ := by
    rw [hQ]
    simp
  calc ‖f (z₀ + w) - f z₀ - w * deriv f z₀ - (w ^ 2 / 2) * iteratedDeriv 2 f z₀‖
      = ‖Q (z₀ + w)‖ := by rw [hQval]
    _ = ‖Q (z₀ + w) - Q z₀‖ := by rw [hQz₀, sub_zero]
    _ ≤ ((25/16) * S) * ‖w‖ := hMQ
    _ ≤ ((25/16) * S) * (5/4) := mul_le_mul_of_nonneg_left hw.le (mul_nonneg (by norm_num) hS0)
    _ = (125/64) * S := by ring

end Work.FatouCH
