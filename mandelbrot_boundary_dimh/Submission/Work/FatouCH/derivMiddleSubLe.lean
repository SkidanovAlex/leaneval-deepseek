import Mathlib

namespace Work.FatouCH

/-- If `f` is holomorphic on the ball `ball z₀ R`, then for any `r < R` each iterated derivative
`iteratedDeriv n f` is holomorphic (in particular differentiable) on the smaller ball
`ball z₀ r`.  Proof: `f` is analytic on the (open) ball `ball z₀ R`, hence `C^∞` there, hence all
its iterated derivatives are differentiable there; restrict to the smaller ball and identify the
derivative within the open set with the global one.

Note that this says more than the fact that `f` itself has derivatives: it says that the functions
`deriv f`, `iteratedDeriv 2 f`, ... are again holomorphic, which is what mean value estimates
applied to those functions need. -/
theorem differentiableOn_iteratedDeriv_of_lt_radius {f : ℂ → ℂ} {z₀ : ℂ} {R r : ℝ} {n : ℕ}
    (hf : DifferentiableOn ℂ f (Metric.ball z₀ R)) (hr : r < R) :
    DifferentiableOn ℂ (iteratedDeriv n f) (Metric.ball z₀ r) := by
  have hmem : ∀ z, z ∈ Metric.ball z₀ r → z ∈ Metric.ball z₀ R := by
    intro z hz
    rw [Metric.mem_ball, dist_eq_norm] at hz ⊢
    exact lt_trans hz hr
  have hAnal : AnalyticOn ℂ f (Metric.ball z₀ R) := hf.analyticOn Metric.isOpen_ball
  have hCd : ContDiffOn ℂ (⊤ : WithTop ℕ∞) f (Metric.ball z₀ R) :=
    hAnal.contDiffOn Metric.isOpen_ball.uniqueDiffOn
  have hw :=
    hCd.differentiableOn_iteratedDerivWithin (m := n) (by simp) Metric.isOpen_ball.uniqueDiffOn
  refine (hw.mono (fun z hz => hmem z hz)).congr (fun z hz => ?_)
  exact (iteratedDerivWithin_of_isOpen Metric.isOpen_ball (hmem z hz)).symm

/-- The second derivative at the centre is the mean slope of the first derivative over the segment, up to `(25/12) S`. If `f` is holomorphic on `ball z₀ R` (`R ≥ 3`) and `‖iteratedDeriv 3 f‖ ≤ S` on `ball z₀ (5/4)`, then for `3/4 ≤ ‖w‖` and `‖w‖ < 5/4` we have `‖iteratedDeriv 2 f z₀ - (deriv f (z₀+w) - deriv f z₀)/w‖ ≤ (25/12) * S`. Apply `Convex.norm_image_sub_le_of_norm_deriv_le` on `ball z₀ (5/4)` to `G z = deriv f z - deriv f z₀ - (z - z₀) iteratedDeriv 2 f z₀` and to `deriv G`: `G z₀ = 0`, `deriv G z₀ = 0`, `‖iteratedDeriv 2 G‖ = ‖iteratedDeriv 2 f - iteratedDeriv 2 f z₀‖ ≤ (5/4) S`, so `‖G (z₀+w)‖ ≤ (25/16) S`, and `G (z₀+w) = w * ((deriv f (z₀+w) - deriv f z₀)/w - iteratedDeriv 2 f z₀)`. -/
theorem derivMiddleSubLe {f : ℂ → ℂ} {z₀ w : ℂ} {R S : ℝ} (hR : 3 ≤ R)
    (hf : DifferentiableOn ℂ f (Metric.ball z₀ R))
    (hS : ∀ ζ ∈ Metric.ball z₀ (5 / 4), ‖iteratedDeriv 3 f ζ‖ ≤ S)
    (hw : ‖w‖ < 5 / 4) (hw' : 3 / 4 ≤ ‖w‖) :
    ‖iteratedDeriv 2 f z₀ - (deriv f (z₀ + w) - deriv f z₀) / w‖ ≤ (25 / 12) * S := by
  -- `S` is nonnegative, as the third derivative of `f` is bounded by it at the centre
  have hSnonneg : 0 ≤ S :=
    le_trans (norm_nonneg _) (hS z₀ (by rw [Metric.mem_ball, dist_self]; norm_num))
  have h54 : (5 : ℝ) / 4 < R := by linarith
  -- holomorphy of the first two derivatives on the ball of radius `5/4`
  have hdiff2 : DifferentiableOn ℂ (iteratedDeriv 2 f) (Metric.ball z₀ (5 / 4)) :=
    differentiableOn_iteratedDeriv_of_lt_radius hf h54
  have hdiff1 : DifferentiableOn ℂ (deriv f) (Metric.ball z₀ (5 / 4)) := by
    have := differentiableOn_iteratedDeriv_of_lt_radius (f := f) (z₀ := z₀) (R := R) (r := 5 / 4) (n := 1) hf h54
    rwa [iteratedDeriv_one] at this
  have hd2deriv : ∀ z ∈ Metric.ball z₀ (5 / 4), deriv (iteratedDeriv 2 f) z = iteratedDeriv 3 f z := by
    intro z _
    rw [← iteratedDeriv_succ (f := f) (n := 2)]
  -- the second derivative is `S`-Lipschitz on `ball z₀ (5/4)`, with Lipschitz constant `S`
  have hlip : ∀ z ∈ Metric.ball z₀ (5 / 4),
      ‖iteratedDeriv 2 f z - iteratedDeriv 2 f z₀‖ ≤ S * (5 / 4) := by
    intro z hz
    have h := Convex.norm_image_sub_le_of_norm_deriv_le (f := iteratedDeriv 2 f)
      (s := Metric.ball z₀ (5 / 4)) (x := z₀) (y := z) (C := S)
      (fun x hx => hdiff2.differentiableAt (Metric.isOpen_ball.mem_nhds hx))
      (fun x hx => by rw [hd2deriv x hx]; exact hS x hx)
      (convex_ball z₀ (5 / 4 : ℝ)) (by rw [Metric.mem_ball, dist_self]; norm_num) hz
    have hzlt : ‖z - z₀‖ ≤ 5 / 4 := by
      rw [Metric.mem_ball, dist_eq_norm] at hz
      exact le_of_lt hz
    calc ‖iteratedDeriv 2 f z - iteratedDeriv 2 f z₀‖ ≤ S * ‖z - z₀‖ := h
      _ ≤ S * (5 / 4) := mul_le_mul_of_nonneg_left hzlt hSnonneg
  -- the auxiliary function `G`
  let G : ℂ → ℂ := fun z => deriv f z - deriv f z₀ - (z - z₀) * iteratedDeriv 2 f z₀
  have hGderiv : ∀ z ∈ Metric.ball z₀ (5 / 4),
      deriv G z = iteratedDeriv 2 f z - iteratedDeriv 2 f z₀ := by
    intro z hz
    have h2eq : iteratedDeriv 2 f = deriv (deriv f) := by
      have h := iteratedDeriv_succ (f := f) (n := 1)
      rw [iteratedDeriv_one] at h
      exact h
    have h1 : HasDerivAt (deriv f) (iteratedDeriv 2 f z) z := by
      have h := (hdiff1.differentiableAt (Metric.isOpen_ball.mem_nhds hz)).hasDerivAt
      rw [← h2eq] at h
      exact h
    have h2 : HasDerivAt (fun y : ℂ => (y - z₀) * iteratedDeriv 2 f z₀)
        (iteratedDeriv 2 f z₀) z := by
      have hb : HasDerivAt (fun y : ℂ => y - z₀) 1 z := by
        simpa using (hasDerivAt_id z).sub_const z₀
      simpa using hb.mul_const (iteratedDeriv 2 f z₀)
    have hc : HasDerivAt (fun _ : ℂ => deriv f z₀) 0 z := hasDerivAt_const z (deriv f z₀)
    have hG' : HasDerivAt G (iteratedDeriv 2 f z - iteratedDeriv 2 f z₀) z := by
      have h12 := (h1.sub hc).sub h2
      convert h12 using 2
      ring
    exact hG'.deriv
  have hGdiff : ∀ z ∈ Metric.ball z₀ (5 / 4), DifferentiableAt ℂ G z := by
    intro z hz
    have h1 : DifferentiableAt ℂ (deriv f) z :=
      hdiff1.differentiableAt (Metric.isOpen_ball.mem_nhds hz)
    have h3 : DifferentiableAt ℂ (fun y : ℂ => (y - z₀) * iteratedDeriv 2 f z₀) z := by fun_prop
    have h12 := (h1.sub (differentiableAt_const (deriv f z₀))).sub h3
    convert h12 using 1
  -- mean value theorem for `G` on `ball z₀ (5/4)`
  have hGbound : ‖G (z₀ + w)‖ ≤ (25 / 16) * S := by
    have h := Convex.norm_image_sub_le_of_norm_deriv_le (f := G)
      (s := Metric.ball z₀ (5 / 4)) (x := z₀) (y := z₀ + w) (C := S * (5 / 4))
      (fun x hx => hGdiff x hx)
      (fun x hx => by rw [hGderiv x hx]; exact hlip x hx)
      (convex_ball z₀ (5 / 4 : ℝ)) (by rw [Metric.mem_ball, dist_self]; norm_num)
      (by rw [Metric.mem_ball, dist_eq_norm]; simpa using hw)
    rw [show G z₀ = 0 from by simp [G], sub_zero] at h
    rw [show z₀ + w - z₀ = w from by ring] at h
    have hwle : ‖w‖ ≤ 5 / 4 := le_of_lt hw
    calc ‖G (z₀ + w)‖ ≤ (S * (5 / 4)) * ‖w‖ := h
      _ ≤ (S * (5 / 4)) * (5 / 4) :=
          mul_le_mul_of_nonneg_left hwle (mul_nonneg hSnonneg (by norm_num))
      _ = (25 / 16) * S := by ring
  have hwne : w ≠ 0 := by
    intro h
    rw [h, norm_zero] at hw'
    norm_num at hw'
  have hGval : G (z₀ + w) = w * ((deriv f (z₀ + w) - deriv f z₀) / w - iteratedDeriv 2 f z₀) := by
    simp only [G]
    field_simp
    ring
  have hkey : ‖(deriv f (z₀ + w) - deriv f z₀) / w - iteratedDeriv 2 f z₀‖
      ≤ (25 / 16) * S / ‖w‖ := by
    rw [le_div_iff₀ (norm_pos_iff.mpr hwne)]
    rw [← norm_mul]
    rw [mul_comm ((deriv f (z₀ + w) - deriv f z₀) / w - iteratedDeriv 2 f z₀) w, ← hGval]
    exact hGbound
  calc ‖iteratedDeriv 2 f z₀ - (deriv f (z₀ + w) - deriv f z₀) / w‖
      = ‖(deriv f (z₀ + w) - deriv f z₀) / w - iteratedDeriv 2 f z₀‖ := norm_sub_rev _ _
    _ ≤ (25 / 16) * S / ‖w‖ := hkey
    _ ≤ (25 / 12) * S := by
        rw [div_le_iff₀ (norm_pos_iff.mpr hwne)]
        have h1 : 0 ≤ (25 / 12 : ℝ) * S := mul_nonneg (by norm_num) hSnonneg
        have h2 : (25 / 12 : ℝ) * S * (3 / 4) ≤ (25 / 12) * S * ‖w‖ :=
          mul_le_mul_of_nonneg_left hw' h1
        nlinarith [h2]

end Work.FatouCH
