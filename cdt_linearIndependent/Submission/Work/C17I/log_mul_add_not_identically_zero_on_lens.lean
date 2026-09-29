import Mathlib

namespace Work.C17I

private lemma cnorm_ofReal (t : ℝ) : ‖(t : ℂ)‖ = |t| := by simp

/-- **Divergence of the principal logarithm against a bounded factor.**  Let `x > 0`, `r > 0` and let
`y1`, `hh` be complex differentiable on the disc `ball(x, r)`, with `y1 x ≠ 0`.  Then for `κ ≠ 0`
the function `z ↦ κ·y1 z·Complex.log(x − z) + hh z` is not identically zero on the "lens"
`ball(x, r) ∩ ball(0, x)`.  Indeed the lens contains the points `x − ε` (`0 < ε < min r x`), where
`log(x − (x − ε)) = log ε → −∞` while `y1` stays at positive distance from `0` and `hh` stays
bounded near `x`. -/
theorem log_mul_add_not_identically_zero_on_lens {x r : ℝ} (hx : 0 < x) (hr : 0 < r)
    (y1 hh : ℂ → ℂ)
    (hy1d : DifferentiableOn ℂ y1 (Metric.ball (x : ℂ) r))
    (hhhd : DifferentiableOn ℂ hh (Metric.ball (x : ℂ) r))
    (hy1x : y1 (x : ℂ) ≠ 0) (κ : ℂ) (hκ : κ ≠ 0) :
    ¬ (∀ z ∈ Metric.ball (x : ℂ) r ∩ Metric.ball (0 : ℂ) x,
        κ * y1 z * Complex.log ((x : ℂ) - z) + hh z = 0) := by
  intro h
  -- `x` is an interior point of the disc, so both functions are continuous there.
  have hmem : Metric.ball (x:ℂ) r ∈ nhds (x:ℂ) := Metric.ball_mem_nhds _ hr
  have hy1cont : ContinuousAt y1 (x:ℂ) := (hy1d.differentiableAt hmem).continuousAt
  have hhhcont : ContinuousAt hh (x:ℂ) := (hhhd.differentiableAt hmem).continuousAt
  have h2pos : 0 < ‖y1 (x:ℂ)‖ := norm_pos_iff.mpr hy1x
  have hκpos : 0 < ‖κ‖ := norm_pos_iff.mpr hκ
  -- Positive lower bound for `‖y1‖` near `x`.
  obtain ⟨δ1, hδ1pos, hδ1⟩ : ∃ δ > 0, ∀ w, dist w (x:ℂ) < δ → ‖y1 (x:ℂ)‖ / 2 < ‖y1 w‖ := by
    have hset : {w : ℂ | ‖y1 (x:ℂ)‖ / 2 < ‖w‖} ∈ nhds (y1 (x:ℂ)) :=
      (isOpen_lt continuous_const continuous_norm).mem_nhds (by simp only [Set.mem_ofPred_eq]; linarith)
    have hev : ∀ᶠ w in nhds (x:ℂ), ‖y1 (x:ℂ)‖ / 2 < ‖y1 w‖ := hy1cont.eventually_mem hset
    rw [Metric.eventually_nhds_iff] at hev
    exact hev
  -- Upper bound for `‖hh‖` near `x`.
  obtain ⟨δ2, hδ2pos, hδ2⟩ : ∃ δ > 0, ∀ w, dist w (x:ℂ) < δ → ‖hh w - hh (x:ℂ)‖ < 1 := by
    have hev : ∀ᶠ w in nhds (x:ℂ), hh w ∈ Metric.ball (hh (x:ℂ)) 1 :=
      hhhcont.eventually_mem (Metric.ball_mem_nhds _ zero_lt_one)
    rw [Metric.eventually_nhds_iff] at hev
    obtain ⟨δ, hδpos, hδ⟩ := hev
    exact ⟨δ, hδpos, fun w hw => by
      have hw' := hδ hw
      rwa [Metric.mem_ball, dist_eq_norm] at hw'⟩
  -- Constants of the growth argument.
  set c : ℝ := ‖κ‖ * (‖y1 (x:ℂ)‖ / 2) with hcdef
  have hcpos : 0 < c := by rw [hcdef]; exact mul_pos hκpos (by linarith)
  set M : ℝ := ‖hh (x:ℂ)‖ + 1 with hMdef
  have hMpos : 0 < M := by rw [hMdef]; positivity
  -- A radius `m0` small enough for every requirement.
  set m0 : ℝ := min (r/2) (min (x/2) (min (δ1/2) (δ2/2))) with hm0def
  have hm0pos : 0 < m0 := by
    rw [hm0def]
    exact lt_min (by linarith) (lt_min (by linarith) (lt_min (by linarith) (by linarith)))
  set B : ℝ := max (((M+1)/c) + 1) (-Real.log m0 + 1) with hBdef
  have hBgt : (M+1)/c < B := by
    rw [hBdef]
    exact lt_of_lt_of_le (by linarith) (le_max_left _ _)
  have hBpos : 0 < B := lt_trans (div_pos (by linarith) hcpos) hBgt
  -- `ε = exp(-B)` lies below `m0` (hence below `r`, `x`, `δ1`, `δ2`) and `|log ε| = B`.
  set ε : ℝ := Real.exp (-B) with hεdef
  have hεpos : 0 < ε := by rw [hεdef]; exact Real.exp_pos _
  have hm0_le_r : m0 ≤ r/2 := by rw [hm0def]; exact min_le_left _ _
  have hm0_le_x : m0 ≤ x/2 := by rw [hm0def]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hm0_le_δ1 : m0 ≤ δ1/2 := by
    rw [hm0def]; exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hm0_le_δ2 : m0 ≤ δ2/2 := by
    rw [hm0def]; exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
  have hε_lt_m0 : ε < m0 := by
    rw [hεdef, ← Real.exp_log hm0pos]
    apply Real.exp_lt_exp.mpr
    have h1 : -Real.log m0 + 1 ≤ B := by rw [hBdef]; exact le_max_right _ _
    linarith
  have hεr : ε < r := by linarith [hε_lt_m0, hm0_le_r]
  have hεx : ε < x := by linarith [hε_lt_m0, hm0_le_x]
  have hεδ1 : ε < δ1 := by linarith [hε_lt_m0, hm0_le_δ1, hδ1pos]
  have hεδ2 : ε < δ2 := by linarith [hε_lt_m0, hm0_le_δ2, hδ2pos]
  have hlogε : Real.log ε = -B := by rw [hεdef, Real.log_exp]
  have habslog : |Real.log ε| = B := by rw [hlogε, abs_neg, abs_of_pos hBpos]
  have hAlog : (M+1)/c < |Real.log ε| := by rw [habslog]; exact hBgt
  have hlogpos : 0 < |Real.log ε| := lt_trans (div_pos (by linarith) hcpos) hAlog
  -- The test point `z = x - ε` of the lens.
  set z : ℂ := ((x - ε : ℝ) : ℂ) with hzdef
  have hdist : dist z (x:ℂ) = ε := by
    rw [hzdef, dist_eq_norm]
    have h1 : ((x - ε : ℝ) : ℂ) - (x:ℂ) = ((-ε : ℝ) : ℂ) := by push_cast; ring
    rw [h1, cnorm_ofReal, abs_neg, abs_of_pos hεpos]
  have hzball1 : z ∈ Metric.ball (x:ℂ) r := by rw [Metric.mem_ball, hdist]; exact hεr
  have hzball2 : z ∈ Metric.ball (0:ℂ) x := by
    rw [Metric.mem_ball, dist_eq_norm, hzdef, sub_zero, cnorm_ofReal,
      abs_of_pos (by linarith : 0 < x - ε)]
    linarith
  have hzh := h z ⟨hzball1, hzball2⟩
  have hsub : (x:ℂ) - z = (ε:ℂ) := by
    rw [hzdef]; push_cast; ring
  have hhlog : Complex.log ((x:ℂ) - z) = (Real.log ε : ℂ) := by
    rw [hsub, ← Complex.ofReal_log (le_of_lt hεpos)]
  rw [hhlog] at hzh
  have heq : κ * y1 z * (Real.log ε : ℂ) = - hh z := by
    rw [add_eq_zero_iff_eq_neg] at hzh; exact hzh
  have hnormeq : ‖κ * y1 z * (Real.log ε : ℂ)‖ = ‖hh z‖ := by rw [heq, norm_neg]
  have hnorm1 : ‖κ * y1 z * (Real.log ε : ℂ)‖ = ‖κ‖ * ‖y1 z‖ * |Real.log ε| := by
    rw [norm_mul, norm_mul, cnorm_ofReal]
  -- Lower bound for the left-hand side.
  have hstep1 : c < ‖κ‖ * ‖y1 z‖ := by
    have hdz : dist z (x:ℂ) < δ1 := by rw [hdist]; exact hεδ1
    have hδ1z := hδ1 z hdz
    rw [hcdef]
    exact mul_lt_mul_of_pos_left hδ1z hκpos
  have hstep2 : c * |Real.log ε| < ‖κ‖ * ‖y1 z‖ * |Real.log ε| :=
    mul_lt_mul_of_pos_right hstep1 hlogpos
  have hstep3 : M + 1 < c * |Real.log ε| := by
    have h' := mul_lt_mul_of_pos_left hAlog hcpos
    rwa [mul_div_cancel₀ _ (ne_of_gt hcpos)] at h'
  -- Upper bound for the right-hand side.
  have hMbound : ‖hh z‖ < M := by
    have hdz : dist z (x:ℂ) < δ2 := by rw [hdist]; exact hεδ2
    have hb := hδ2 z hdz
    calc ‖hh z‖ = ‖(hh z - hh (x:ℂ)) + hh (x:ℂ)‖ := by rw [sub_add_cancel]
      _ ≤ ‖hh z - hh (x:ℂ)‖ + ‖hh (x:ℂ)‖ := norm_add_le _ _
      _ < 1 + ‖hh (x:ℂ)‖ := by linarith
      _ = M := by rw [hMdef]; ring
  have hcontr : M + 1 < ‖hh z‖ := by
    rw [← hnormeq, hnorm1]
    exact lt_trans hstep3 hstep2
  linarith [hcontr, hMbound]

end Work.C17I
