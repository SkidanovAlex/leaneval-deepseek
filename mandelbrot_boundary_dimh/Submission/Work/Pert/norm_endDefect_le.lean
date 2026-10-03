import Mathlib
import Submission.Work.Pert.EndDefect
import Submission.Work.Escape.exists_differentiableOn_ball_clog
import Submission.Work.FatouL1.discSharpPick
import Submission.Work.Pert.StripChart
import Submission.Work.Pert.Strip.chart_facts

/-!
# `Work.Pert.norm_endDefect_le`: the size of the end defect

For perturbation data `(σ, α, u)` of `f z = z + z(z-σ)u z` with `‖α‖ ≤ 1/64`, `α ≠ 0`,
`u` holomorphic and nowhere vanishing on `ball 0 rr` with `1/2 ≤ ‖u w‖ ≤ 2` there,
`‖σ‖ ≤ rr/2` and the normalisation `1 - σ u 0 = exp (2πiα)`, the end defect

    endDefect u σ α = (1/(2πiα)) * log (1/(1 + σ u σ)) - 1

satisfies `‖endDefect u σ α‖ ≤ 100 ‖α‖ (1 + 1/rr)`.

The proof is an estimate for the principal logarithm.  Writing `A = 2πiα`, `E = exp A`,
`s = σ u 0 = 1 - E` and `δ = σ (u σ - u 0) = s (exp w - 1)` with `w = log u σ - log u 0`, one has

    log (1/(1 + σ u σ)) - A = -log (1 - s²) - log (1 + δ/(1 + s)),

and the two terms are bounded by `O(‖α‖²)` and `O(‖α‖²/rr)` respectively.  The key input is the
Schwarz–Pick estimate for the strip `|Re| ≤ log 2`, which controls `w = log u σ - log u 0`.
-/

set_option maxHeartbeats 4000000

namespace Work.Pert

open Metric Complex

noncomputable section

/-- **Schwarz–Pick for maps into a vertical strip.**  If `g` is holomorphic on `ball 0 R` and
`|(g z).re| ≤ h` there, then `‖deriv g z‖ ≤ 4 h R / (π (R ^ 2 - ‖z‖ ^ 2))` for `z` in the ball.

This follows from the Schwarz–Pick estimate on the unit disc applied to the composite
`w ↦ stripChart h (g (R w))`, using the identity
`1 - ‖stripChart h ζ‖ ^ 2 ≤ (4h/π) ‖deriv (stripChart h) ζ‖` on the strip (see
`Work.Pert.Strip.chart_facts`). -/
theorem strip_deriv_le {h R : ℝ} (hh : 0 < h) (hR : 0 < R) {g : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g (Metric.ball 0 R))
    (hre : ∀ z ∈ Metric.ball 0 R, |(g z).re| ≤ h) :
    ∀ z ∈ Metric.ball 0 R, ‖deriv g z‖ ≤ 4 * h * R / (Real.pi * (R ^ 2 - ‖z‖ ^ 2)) := by
  obtain ⟨hchartdiff, hchartnorm, hchartarith, hchartderivne⟩ := Work.Pert.Strip.chart_facts hh
  intro z hz
  have hz_lt : ‖z‖ < R := by
    rw [Metric.mem_ball, dist_zero_right] at hz; exact hz
  have hRne : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
  have hRnorm : ‖(R : ℂ)‖ = R := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR]
  set t : ℂ := z / (R : ℂ) with ht
  have htz : (R : ℂ) * t = z := by rw [ht]; field_simp
  have ht_mem : t ∈ Metric.ball (0 : ℂ) 1 := by
    rw [Metric.mem_ball, dist_zero_right, ht, norm_div, hRnorm, div_lt_one hR]
    exact hz_lt
  have hmaps : Set.MapsTo (fun s : ℂ => (R : ℂ) * s) (Metric.ball (0 : ℂ) 1)
      (Metric.ball (0 : ℂ) R) := by
    intro s hs
    rw [Metric.mem_ball, dist_zero_right] at hs ⊢
    rw [norm_mul, hRnorm]
    nlinarith [hs]
  have hψd : DifferentiableOn ℂ (fun s : ℂ => g ((R : ℂ) * s)) (Metric.ball 0 1) :=
    hg.comp (by fun_prop) hmaps
  have hψm : Set.MapsTo (fun s : ℂ => g ((R : ℂ) * s)) (Metric.ball (0 : ℂ) 1)
      {ζ : ℂ | |ζ.re| ≤ h} := fun s hs => hre _ (hmaps hs)
  have hFd : DifferentiableOn ℂ (fun s : ℂ => Work.Pert.stripChart h (g ((R : ℂ) * s)))
      (Metric.ball 0 1) := hchartdiff.comp hψd hψm
  have hFm : Set.MapsTo (fun s : ℂ => Work.Pert.stripChart h (g ((R : ℂ) * s)))
      (Metric.ball (0 : ℂ) 1) (Metric.closedBall 0 1) := by
    intro s hs
    rw [Metric.mem_closedBall, dist_zero_right]
    exact hchartnorm _ (hψm hs)
  have hpick := Work.FatouL1.discSharpPick hFd hFm ht_mem
  -- the value of the composite at `t`
  have hFt : (fun s : ℂ => Work.Pert.stripChart h (g ((R : ℂ) * s))) t
      = Work.Pert.stripChart h (g z) := by
    simp only [htz]
  -- the chain rule
  have hψ_at : DifferentiableAt ℂ (fun s : ℂ => g ((R : ℂ) * s)) t := by
    have h1 : DifferentiableAt ℂ (fun s : ℂ => (R : ℂ) * s) t := by fun_prop
    exact (hg.differentiableAt (Metric.isOpen_ball.mem_nhds (by rw [htz]; exact hz))).comp t h1
  have hchart_at : DifferentiableAt ℂ (Work.Pert.stripChart h) (g ((R : ℂ) * t)) :=
    (Work.Pert.Strip.chart_hasDerivAt hh (hre _ (hmaps ht_mem))).differentiableAt
  have hchain : deriv (fun s : ℂ => Work.Pert.stripChart h (g ((R : ℂ) * s))) t
      = deriv (Work.Pert.stripChart h) (g z) * (deriv g z * R) := by
    have hc := deriv_comp (x := t) (h := fun s : ℂ => g ((R : ℂ) * s))
      (h₂ := Work.Pert.stripChart h) hchart_at hψ_at
    simp only [Function.comp_def] at hc
    rw [hc, htz]
    -- the derivative of the inner map
    have hc2 : deriv (fun s : ℂ => g ((R : ℂ) * s)) t = deriv g ((R : ℂ) * t) * R := by
      have h1 : DifferentiableAt ℂ (fun s : ℂ => (R : ℂ) * s) t := by fun_prop
      have hc3 := deriv_comp (x := t) (h := fun s : ℂ => (R : ℂ) * s) (h₂ := g)
        (hg.differentiableAt (Metric.isOpen_ball.mem_nhds (by rw [htz]; exact hz))) h1
      simp only [Function.comp_def] at hc3
      rw [hc3]
      have h2 : deriv (fun s : ℂ => (R : ℂ) * s) t = R := by
        have h3 := deriv_const_mul (𝕜 := ℂ) (c := (R : ℂ)) (x := t) (d := fun s : ℂ => s)
          differentiableAt_id
        simpa using h3
      rw [h2]
    rw [hc2, htz]
  -- the norm identity
  have hderiv_norm : ‖deriv (fun s : ℂ => Work.Pert.stripChart h (g ((R : ℂ) * s))) t‖
      = ‖deriv (Work.Pert.stripChart h) (g z)‖ * (R * ‖deriv g z‖) := by
    rw [hchain, norm_mul, norm_mul, hRnorm]
    ring
  -- the two key inequalities
  have hDpos : 0 < ‖deriv (Work.Pert.stripChart h) (g z)‖ := by
    refine lt_of_le_of_ne (norm_nonneg _) (Ne.symm ?_)
    simpa using hchartderivne (g z) (hre z hz)
  have hden_t : 1 - ‖t‖ ^ 2 = (R ^ 2 - ‖z‖ ^ 2) / R ^ 2 := by
    rw [ht, norm_div, hRnorm]
    field_simp
  have hden_pos : 0 < 1 - ‖t‖ ^ 2 := by
    have h1 : ‖t‖ < 1 := by simpa [Metric.mem_ball, dist_zero_right] using ht_mem
    nlinarith [norm_nonneg t]
  have hdenz : 0 < R ^ 2 - ‖z‖ ^ 2 := by nlinarith [hz_lt, norm_nonneg z]
  have hq : 0 ≤ R ^ 2 / (R ^ 2 - ‖z‖ ^ 2) := div_nonneg (sq_nonneg R) hdenz.le
  have hstep1 : R * ‖deriv g z‖
      ≤ (4 * h / Real.pi) * (R ^ 2 / (R ^ 2 - ‖z‖ ^ 2)) := by
    have hineq : ‖deriv (Work.Pert.stripChart h) (g z)‖ * (R * ‖deriv g z‖)
        ≤ ‖deriv (Work.Pert.stripChart h) (g z)‖
          * ((4 * h / Real.pi) * (R ^ 2 / (R ^ 2 - ‖z‖ ^ 2))) := by
      calc ‖deriv (Work.Pert.stripChart h) (g z)‖ * (R * ‖deriv g z‖)
          = ‖deriv (fun s : ℂ => Work.Pert.stripChart h (g ((R : ℂ) * s))) t‖ :=
            hderiv_norm.symm
        _ ≤ (1 - ‖(fun s : ℂ => Work.Pert.stripChart h (g ((R : ℂ) * s))) t‖ ^ 2)
              / (1 - ‖t‖ ^ 2) := hpick
        _ = (1 - ‖Work.Pert.stripChart h (g z)‖ ^ 2) * (1 - ‖t‖ ^ 2)⁻¹ := by
            rw [hFt, div_eq_mul_inv]
        _ = (1 - ‖Work.Pert.stripChart h (g z)‖ ^ 2)
              * (R ^ 2 / (R ^ 2 - ‖z‖ ^ 2)) := by
            rw [hden_t, inv_div]
        _ ≤ ((4 * h / Real.pi) * ‖deriv (Work.Pert.stripChart h) (g z)‖)
              * (R ^ 2 / (R ^ 2 - ‖z‖ ^ 2)) :=
            mul_le_mul_of_nonneg_right (hchartarith (g z) (hre z hz)) hq
        _ = ‖deriv (Work.Pert.stripChart h) (g z)‖
              * ((4 * h / Real.pi) * (R ^ 2 / (R ^ 2 - ‖z‖ ^ 2))) := by ring
    exact le_of_mul_le_mul_left hineq hDpos
  -- divide by `R`
  have hstep2 : ‖deriv g z‖ ≤ ((4 * h / Real.pi) * (R ^ 2 / (R ^ 2 - ‖z‖ ^ 2))) / R := by
    rw [le_div_iff₀ hR]
    linarith [hstep1]
  have hstep3 : ((4 * h / Real.pi) * (R ^ 2 / (R ^ 2 - ‖z‖ ^ 2))) / R
      = 4 * h * R / (Real.pi * (R ^ 2 - ‖z‖ ^ 2)) := by
    field_simp
  rw [hstep3] at hstep2
  exact hstep2

/-! ## Elementary bounds -/

/-- `‖exp z - 1‖ ≤ exp ‖z‖ - 1`. -/
private lemma norm_exp_sub_one_le_exp_norm_sub_one (z : ℂ) :
    ‖Complex.exp z - 1‖ ≤ Real.exp ‖z‖ - 1 := by
  simpa using Complex.norm_exp_sub_sum_le_exp_norm_sub_sum z 1

/-- `exp x ≤ 1 + x + (3/4) x ^ 2` for `0 ≤ x ≤ 1` (Taylor bound, `Real.exp_bound'`). -/
private lemma exp_le_one_add_add (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    Real.exp x ≤ 1 + x + (3 / 4) * x ^ 2 := by
  have h := Real.exp_bound' (x := x) h0 h1 (n := 2) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

/-- `‖log (1 + z)‖ ≤ (3/2) ‖z‖` for `‖z‖ ≤ 1/2`. -/
private lemma norm_log_one_add_le_three_halves {z : ℂ} (hz : ‖z‖ ≤ 1 / 2) :
    ‖Complex.log (1 + z)‖ ≤ (3 / 2) * ‖z‖ := by
  have h1 : ‖z‖ < 1 := by linarith
  have h2 := Complex.norm_log_one_add_le h1
  have h4 : (1 - ‖z‖)⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ (by linarith : (0 : ℝ) < 1 - ‖z‖) (by norm_num : (0 : ℝ) < 2)]
    linarith
  have h5 : ‖z‖ ^ 2 * (1 - ‖z‖)⁻¹ ≤ ‖z‖ ^ 2 * 2 :=
    mul_le_mul_of_nonneg_left h4 (sq_nonneg ‖z‖)
  have h6 : ‖z‖ ^ 2 ≤ ‖z‖ / 2 := by nlinarith [norm_nonneg z, hz]
  have h7 : ‖z‖ ^ 2 * (1 - ‖z‖)⁻¹ / 2 ≤ ‖z‖ / 2 := by linarith
  linarith

/-- The argument of a complex number with positive real part lies in `(-π/2, π/2)`, so the sum of
two such arguments lies in `Ioc (-π) π`; this is the branch condition for `Complex.log_mul`. -/
private lemma arg_add_mem_Ioc {x y : ℂ} (hx : 0 < x.re) (hy : 0 < y.re) :
    x.arg + y.arg ∈ Set.Ioc (-Real.pi) Real.pi := by
  have hp := Real.pi_pos
  have hx1 : -(Real.pi / 2) < x.arg := Complex.neg_pi_div_two_lt_arg_iff.mpr (Or.inl hx)
  have hx2 : x.arg < Real.pi / 2 := Complex.arg_lt_pi_div_two_iff.mpr (Or.inl hx)
  have hy1 : -(Real.pi / 2) < y.arg := Complex.neg_pi_div_two_lt_arg_iff.mpr (Or.inl hy)
  have hy2 : y.arg < Real.pi / 2 := Complex.arg_lt_pi_div_two_iff.mpr (Or.inl hy)
  exact ⟨by linarith, by linarith⟩

/-- A complex number with positive real part has argument `≠ π`. -/
private lemma arg_ne_pi_of_re_pos {z : ℂ} (hz : 0 < z.re) : z.arg ≠ Real.pi := by
  have h : z.arg < Real.pi := Complex.arg_lt_pi_iff.mpr (Or.inl hz.le)
  intro hc
  rw [hc] at h
  exact lt_irrefl _ h

/-- The real part of a complex number is at least minus its norm. -/
private lemma neg_norm_le_re (z : ℂ) : -(‖z‖) ≤ z.re := by
  have := Complex.abs_re_le_norm z
  rw [abs_le] at this
  linarith [this.1]

/-- `64 log 2 / (3π) ≤ 4.71`. -/
private lemma sixtyfour_log2_le : 64 * Real.log 2 / (3 * Real.pi) ≤ 4.71 := by
  rw [div_le_iff₀ (by positivity)]
  nlinarith [Real.log_two_lt_d9, Real.pi_gt_d4]

/-- `8 log 2 / (3π) ≤ 1`. -/
private lemma eight_log2_le : 8 * Real.log 2 / (3 * Real.pi) ≤ 1 := by
  rw [div_le_one (by positivity)]
  nlinarith [Real.log_two_lt_d9, Real.pi_gt_three]

/-- The pointwise strip bound is at most its value at the boundary `‖x‖ = rr/2`. -/
private lemma deriv_coeff_le {rr : ℝ} (hrr : 0 < rr) {x : ℂ} (hx : ‖x‖ ≤ rr / 2) :
    4 * Real.log 2 * rr / (Real.pi * (rr ^ 2 - ‖x‖ ^ 2))
      ≤ 16 * Real.log 2 / (3 * Real.pi * rr) := by
  have h2 : 0 < rr ^ 2 - ‖x‖ ^ 2 := by nlinarith [norm_nonneg x, hrr, hx]
  rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < Real.pi * (rr ^ 2 - ‖x‖ ^ 2))
    (by positivity : (0 : ℝ) < 3 * Real.pi * rr)]
  have hkey : 3 * rr ^ 2 ≤ 4 * (rr ^ 2 - ‖x‖ ^ 2) := by nlinarith [hx, norm_nonneg x]
  have h4 : (4 * Real.log 2 * Real.pi) * (3 * rr ^ 2)
      ≤ (4 * Real.log 2 * Real.pi) * (4 * (rr ^ 2 - ‖x‖ ^ 2)) :=
    mul_le_mul_of_nonneg_left hkey (by positivity)
  have e1 : 4 * Real.log 2 * rr * (3 * Real.pi * rr)
      = (4 * Real.log 2 * Real.pi) * (3 * rr ^ 2) := by ring
  have e2 : 16 * Real.log 2 * (Real.pi * (rr ^ 2 - ‖x‖ ^ 2))
      = (4 * Real.log 2 * Real.pi) * (4 * (rr ^ 2 - ‖x‖ ^ 2)) := by ring
  rw [e1, e2]
  exact h4

/-- The logarithmic-term bound for `1 - s ^ 2`. -/
private lemma log_one_sub_sq_le {a : ℝ} {s : ℂ} (ha64 : a ≤ 1 / 64) (hs : ‖s‖ ≤ 6.75 * a) :
    ‖Complex.log (1 - s ^ 2)‖ ≤ 70 * a ^ 2 := by
  have hs2 : ‖s ^ 2‖ ≤ 1 / 2 := by rw [norm_pow]; nlinarith [hs, ha64, norm_nonneg s]
  have h1 : ‖Complex.log (1 - s ^ 2)‖ ≤ (3 / 2) * ‖s ^ 2‖ := by
    have h := norm_log_one_add_le_three_halves (z := -(s ^ 2)) (by rw [norm_neg]; exact hs2)
    rw [norm_neg] at h
    simpa only [sub_eq_add_neg] using h
  rw [norm_pow] at h1
  have h2 : ‖s‖ ^ 2 ≤ 45.5625 * a ^ 2 := by nlinarith [hs, norm_nonneg s]
  nlinarith [h1, h2]

/-- The logarithmic-term bound for `1 + δ / (1 + s)`. -/
private lemma log_one_add_div_le {a rr : ℝ} {x : ℂ} (hrr : 0 < rr)
    (hx : ‖x‖ ≤ 240 * a ^ 2 / rr) (hxu : ‖x‖ ≤ 0.56) :
    ‖Complex.log (1 + x)‖ ≤ 400 * a ^ 2 / rr := by
  have hlt : ‖x‖ < 1 := by linarith
  have h1 := Complex.norm_log_one_add_le hlt
  have h2 : (1 - ‖x‖)⁻¹ ≤ 2.28 := by
    rw [inv_le_comm₀ (by linarith : (0 : ℝ) < 1 - ‖x‖) (by norm_num)]
    linarith
  have h4 : ‖x‖ ^ 2 ≤ 0.56 * ‖x‖ := by nlinarith [hxu, norm_nonneg x]
  have h5 : ‖x‖ ^ 2 * (1 - ‖x‖)⁻¹ ≤ (0.56 * ‖x‖) * 2.28 := by
    calc ‖x‖ ^ 2 * (1 - ‖x‖)⁻¹ ≤ ‖x‖ ^ 2 * 2.28 :=
          mul_le_mul_of_nonneg_left h2 (sq_nonneg ‖x‖)
      _ ≤ (0.56 * ‖x‖) * 2.28 := by nlinarith [h4, norm_nonneg x]
  have hfac : ‖x‖ ^ 2 * (1 - ‖x‖)⁻¹ / 2 ≤ 0.64 * ‖x‖ := by
    have h5' : ‖x‖ ^ 2 * (1 - ‖x‖)⁻¹ / 2 ≤ (0.56 * ‖x‖) * 2.28 / 2 := by linarith [h5]
    have h6 : (0.56 * ‖x‖) * 2.28 / 2 ≤ 0.64 * ‖x‖ := by nlinarith [norm_nonneg x]
    linarith
  have h7 : ‖Complex.log (1 + x)‖ ≤ (1 + 0.64) * ‖x‖ := by linarith
  have h8 : (1 + 0.64) * (240 * a ^ 2 / rr) ≤ 400 * a ^ 2 / rr := by
    rw [← mul_div_assoc, div_le_div_iff₀ hrr hrr]
    nlinarith [sq_nonneg a, hrr]
  calc ‖Complex.log (1 + x)‖ ≤ (1 + 0.64) * ‖x‖ := h7
    _ ≤ (1 + 0.64) * (240 * a ^ 2 / rr) := mul_le_mul_of_nonneg_left hx (by norm_num)
    _ ≤ 400 * a ^ 2 / rr := h8

/-! ## The main estimate -/

theorem norm_endDefect_le {rr : ℝ} {α σ : ℂ} {u : ℂ → ℂ}
    (hrr : 0 < rr) (hα : ‖α‖ ≤ 1 / 64) (hα0 : α ≠ 0)
    (hu : DifferentiableOn ℂ u (Metric.ball (0 : ℂ) rr))
    (hu2 : ∀ w ∈ Metric.ball (0 : ℂ) rr, 1 / 2 ≤ ‖u w‖ ∧ ‖u w‖ ≤ 2)
    (hσ : ‖σ‖ ≤ rr / 2)
    (hnorm : 1 - σ * u 0 = Complex.exp (2 * Real.pi * Complex.I * α)) :
    ‖Work.Pert.endDefect u σ α‖ ≤ 100 * ‖α‖ * (1 + 1 / rr) := by
  set a : ℝ := ‖α‖ with ha
  have ha_pos : 0 < a := by rw [ha]; exact norm_pos_iff.mpr hα0
  have ha64 : a ≤ 1 / 64 := by rw [ha]; exact hα
  have hpi := Real.pi_pos
  have hpi3 : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hpi4 : Real.pi < 3.1416 := Real.pi_lt_d4
  set A : ℂ := 2 * Real.pi * Complex.I * α with hA
  -- norm of `A`
  have hA_norm : ‖A‖ = 2 * Real.pi * a := by
    rw [hA]
    simp only [ha, norm_mul, Complex.norm_I, mul_one, Complex.norm_ofNat, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hpi]
  have hA_le1 : ‖A‖ ≤ 1 := by
    rw [hA_norm]; nlinarith [ha64, hpi, hpi4]
  have hA_im : -Real.pi < A.im ∧ A.im ≤ Real.pi := by
    have h1 : |A.im| ≤ ‖A‖ := Complex.abs_im_le_norm A
    have h2 : ‖A‖ ≤ Real.pi / 32 := by rw [hA_norm]; nlinarith [ha64, hpi]
    rw [abs_le] at h1
    exact ⟨by linarith [h1.1, h2], by linarith [h1.2, h2, hpi]⟩
  -- the normalisation `s = σ u 0 = 1 - exp A`
  set s : ℂ := σ * u 0 with hs
  have hs_eq : s = 1 - Complex.exp A := by
    rw [hs, hA, ← hnorm]; ring
  have hs_bound : ‖s‖ ≤ 6.75 * a := by
    rw [hs_eq, norm_sub_rev]
    have h1 : ‖Complex.exp A - 1‖ ≤ Real.exp ‖A‖ - 1 := norm_exp_sub_one_le_exp_norm_sub_one A
    have h2 : Real.exp ‖A‖ ≤ 1 + ‖A‖ + (3 / 4) * ‖A‖ ^ 2 :=
      exp_le_one_add_add ‖A‖ (norm_nonneg A) hA_le1
    have h3 : ‖A‖ + (3 / 4) * ‖A‖ ^ 2 ≤ 6.75 * a := by
      rw [hA_norm]
      have hx : 2 * Real.pi * a ≤ Real.pi / 32 := by nlinarith [ha64, hpi]
      have h4 : 0 ≤ 2 * Real.pi * a := by positivity
      have h5 : (3 / 4) * (2 * Real.pi * a) ^ 2 ≤ (3 / 4) * (2 * Real.pi * a) * (Real.pi / 32) := by
        have h6 : (2 * Real.pi * a) ^ 2 ≤ (2 * Real.pi * a) * (Real.pi / 32) := by
          nlinarith [h4, hx]
        linarith
      have h7 : 2 * Real.pi * a + (3 / 4) * (2 * Real.pi * a) * (Real.pi / 32) ≤ 6.75 * a := by
        have h8 : 2 * Real.pi + (3 / 4) * 2 * Real.pi * (Real.pi / 32) ≤ 6.75 := by
          nlinarith [hpi4, hpi]
        nlinarith [h8, ha_pos]
      linarith
    linarith
  -- `u` does not vanish on the ball
  have hu_ne : ∀ w ∈ Metric.ball (0 : ℂ) rr, u w ≠ 0 := by
    intro w hw hzero
    have h := (hu2 w hw).1
    rw [hzero, norm_zero] at h
    norm_num at h
  have h0mem : (0 : ℂ) ∈ Metric.ball (0 : ℂ) rr := by
    rw [Metric.mem_ball, dist_zero_right]; simpa using hrr
  have hσmem : σ ∈ Metric.ball (0 : ℂ) rr := by
    rw [Metric.mem_ball, dist_zero_right]; linarith [hσ, hrr]
  -- bounds on `σ`
  have hσ_bound : ‖σ‖ ≤ 2 * ‖s‖ := by
    have hu0 : 1 / 2 ≤ ‖u 0‖ := (hu2 0 h0mem).1
    rw [hs, norm_mul]
    nlinarith [norm_nonneg σ]
  have hσ_bound' : ‖σ‖ ≤ 13.5 * a := by linarith [hσ_bound, hs_bound]
  have hσ_small : 2 * ‖σ‖ ≤ 1 := by linarith [hσ_bound', ha64]
  have hs_le_rr : ‖s‖ ≤ rr := by
    have h : ‖σ * u 0‖ ≤ 2 * ‖σ‖ := by
      rw [norm_mul]
      have h8 : ‖u 0‖ ≤ 2 := (hu2 0 h0mem).2
      nlinarith [norm_nonneg σ]
    linarith [h, hσ, hs]
  -- the holomorphic logarithm of `u`
  obtain ⟨G, hGdiff, hGexp, hGre⟩ := Work.Escape.exists_differentiableOn_ball_clog hu hu_ne
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hGre_le : ∀ w ∈ Metric.ball (0 : ℂ) rr, |(G w).re| ≤ Real.log 2 := by
    intro w hw
    rw [hGre w hw]
    obtain ⟨h1, h2⟩ := hu2 w hw
    have h1' : Real.log (1 / 2) ≤ Real.log ‖u w‖ := Real.log_le_log (by norm_num) h1
    have h2' : Real.log ‖u w‖ ≤ Real.log 2 := Real.log_le_log (by linarith [norm_nonneg (u w)]) h2
    have h12 : Real.log (1 / 2) = -Real.log 2 := by rw [one_div, Real.log_inv]
    rw [h12] at h1'
    exact abs_le.mpr ⟨by linarith, h2'⟩
  -- Schwarz–Pick for the strip: the increment of `G`
  have hstrip := strip_deriv_le hlog2pos hrr hGdiff hGre_le
  have hG_incr : ‖G σ - G 0‖ ≤ 16 * Real.log 2 / (3 * Real.pi * rr) * ‖σ‖ := by
    have hconv : Convex ℝ (Metric.closedBall (0 : ℂ) (rr / 2)) := convex_closedBall 0 (rr / 2)
    have hdiff : ∀ x ∈ Metric.closedBall (0 : ℂ) (rr / 2), DifferentiableAt ℂ G x := by
      intro x hx
      rw [Metric.mem_closedBall, dist_zero_right] at hx
      refine hGdiff.differentiableAt (Metric.isOpen_ball.mem_nhds ?_)
      rw [Metric.mem_ball, dist_zero_right]; linarith
    have hbd : ∀ x ∈ Metric.closedBall (0 : ℂ) (rr / 2),
        ‖deriv G x‖ ≤ 16 * Real.log 2 / (3 * Real.pi * rr) := by
      intro x hx
      rw [Metric.mem_closedBall, dist_zero_right] at hx
      have hxmem : x ∈ Metric.ball (0 : ℂ) rr := by
        rw [Metric.mem_ball, dist_zero_right]; linarith
      exact le_trans (hstrip x hxmem) (deriv_coeff_le hrr hx)
    have h0 : (0 : ℂ) ∈ Metric.closedBall (0 : ℂ) (rr / 2) := by
      rw [Metric.mem_closedBall, dist_zero_right]; simp; linarith
    have hσmem2 : σ ∈ Metric.closedBall (0 : ℂ) (rr / 2) := by
      rw [Metric.mem_closedBall, dist_zero_right]; linarith [hσ]
    have := hconv.norm_image_sub_le_of_norm_deriv_le hdiff hbd h0 hσmem2
    simpa using this
  -- `w = log u σ - log u 0` is small
  have hw_le1 : ‖G σ - G 0‖ ≤ 1 := by
    have h1 : 16 * Real.log 2 / (3 * Real.pi * rr) * ‖σ‖
        ≤ 16 * Real.log 2 / (3 * Real.pi * rr) * (rr / 2) :=
      mul_le_mul_of_nonneg_left hσ (by positivity)
    have h2 : 16 * Real.log 2 / (3 * Real.pi * rr) * (rr / 2) = 8 * Real.log 2 / (3 * Real.pi) := by
      field_simp
      ring
    have h3 : 8 * Real.log 2 / (3 * Real.pi) ≤ 1 := eight_log2_le
    linarith [hG_incr, h1, h2, h3]
  -- the defect `δ = σ (u σ - u 0)`
  have hδ_eq : σ * (u σ - u 0) = s * (Complex.exp (G σ - G 0) - 1) := by
    rw [hs, Complex.exp_sub, hGexp σ hσmem, hGexp 0 h0mem]
    have hu0 : u 0 ≠ 0 := hu_ne 0 h0mem
    field_simp
  have hδ_bound : ‖σ * (u σ - u 0)‖ ≤ 4.71 * ‖s‖ ^ 2 / rr := by
    rw [hδ_eq, norm_mul]
    have hexp_bound : ‖Complex.exp (G σ - G 0) - 1‖ ≤ 2 * ‖G σ - G 0‖ :=
      Complex.norm_exp_sub_one_le hw_le1
    have h2 : ‖Complex.exp (G σ - G 0) - 1‖
        ≤ 2 * (16 * Real.log 2 / (3 * Real.pi * rr) * (2 * ‖s‖)) := by
      have h3 : 16 * Real.log 2 / (3 * Real.pi * rr) * ‖σ‖
          ≤ 16 * Real.log 2 / (3 * Real.pi * rr) * (2 * ‖s‖) :=
        mul_le_mul_of_nonneg_left hσ_bound (by positivity)
      linarith [hexp_bound, hG_incr, h3]
    have h4 : ‖s‖ * ‖Complex.exp (G σ - G 0) - 1‖
        ≤ ‖s‖ * (2 * (16 * Real.log 2 / (3 * Real.pi * rr) * (2 * ‖s‖))) :=
      mul_le_mul_of_nonneg_left h2 (norm_nonneg s)
    have h5 : ‖s‖ * (2 * (16 * Real.log 2 / (3 * Real.pi * rr) * (2 * ‖s‖)))
        = 64 * Real.log 2 / (3 * Real.pi) * ‖s‖ ^ 2 / rr := by
      field_simp
      ring
    have h6 : 64 * Real.log 2 / (3 * Real.pi) * ‖s‖ ^ 2 / rr ≤ 4.71 * ‖s‖ ^ 2 / rr := by
      rw [div_le_div_iff₀ hrr hrr]
      nlinarith [sixtyfour_log2_le, mul_nonneg (sq_nonneg ‖s‖) hrr.le]
    linarith [h4, h5, h6]
  set δ : ℂ := σ * (u σ - u 0) with hδdef
  -- the two logarithmic terms
  have hs_sq_le : ‖s‖ ^ 2 ≤ 45.5625 * a ^ 2 := by nlinarith [hs_bound, norm_nonneg s]
  have hT1 : ‖Complex.log (1 - s ^ 2)‖ ≤ 70 * a ^ 2 := log_one_sub_sq_le ha64 hs_bound
  have hden : (0.894531 : ℝ) ≤ ‖1 + s‖ := by
    have h1 : (1 : ℝ) - ‖s‖ ≤ ‖1 + s‖ := by
      have h2 := norm_sub_norm_le (1 : ℂ) (-s)
      rw [norm_neg] at h2
      simpa using h2
    have h3 : ‖s‖ ≤ 6.75 / 64 := by linarith [hs_bound, ha64]
    linarith
  have hx_bound : ‖δ / (1 + s)‖ ≤ 240 * a ^ 2 / rr := by
    have h1 : ‖δ / (1 + s)‖ = ‖δ‖ / ‖1 + s‖ := by rw [norm_div]
    rw [h1]
    have h2 : ‖δ‖ / ‖1 + s‖ ≤ (4.71 * ‖s‖ ^ 2 / rr) / 0.894531 :=
      div_le_div₀ (by positivity) hδ_bound (by norm_num) hden
    have h3 : (4.71 * ‖s‖ ^ 2 / rr) / 0.894531 ≤ 240 * a ^ 2 / rr := by
      rw [div_div, div_le_div_iff₀ (by positivity) hrr]
      nlinarith [hs_sq_le, hrr, sq_nonneg a]
    linarith
  have hx_unif : ‖δ / (1 + s)‖ ≤ 0.56 := by
    have h1 : ‖δ / (1 + s)‖ = ‖δ‖ / ‖1 + s‖ := by rw [norm_div]
    rw [h1]
    have h2 : ‖δ‖ / ‖1 + s‖ ≤ (4.71 * ‖s‖ ^ 2 / rr) / 0.894531 :=
      div_le_div₀ (by positivity) hδ_bound (by norm_num) hden
    have h3 : 4.71 * ‖s‖ ^ 2 / rr ≤ 4.71 * (6.75 * a) := by
      rw [div_le_iff₀ hrr]
      have h7 : ‖s‖ ^ 2 ≤ ‖s‖ * (6.75 * a) := by nlinarith [hs_bound, norm_nonneg s]
      have h8 : ‖s‖ * (6.75 * a) ≤ 6.75 * a * rr := by
        have h9 := mul_le_mul_of_nonneg_right hs_le_rr (by positivity : (0 : ℝ) ≤ 6.75 * a)
        linarith [h9]
      linarith [h7, h8]
    have h4 : (4.71 * (6.75 * a)) / 0.894531 ≤ 0.56 := by
      rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 0.894531)]
      nlinarith [ha64]
    have h5 : (4.71 * ‖s‖ ^ 2 / rr) / 0.894531 ≤ (4.71 * (6.75 * a)) / 0.894531 := by
      rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 0.894531) (by norm_num : (0 : ℝ) < 0.894531)]
      nlinarith [h3]
    linarith [h2, h4, h5]
  have hT2 : ‖Complex.log (1 + δ / (1 + s))‖ ≤ 400 * a ^ 2 / rr :=
    log_one_add_div_le hrr hx_bound hx_unif
  -- the principal logarithm of `1 + σ u σ`
  have hPre : 0 < (1 + σ * u σ).re := by
    have h1 : -(‖σ * u σ‖) ≤ (σ * u σ).re := neg_norm_le_re _
    have h2 : ‖σ * u σ‖ ≤ 2 * ‖σ‖ := by
      rw [norm_mul]
      have h3 : ‖u σ‖ ≤ 2 := (hu2 σ hσmem).2
      nlinarith [norm_nonneg σ]
    simp only [Complex.add_re, Complex.one_re]
    linarith [h1, h2, hσ_small]
  have hs_pre : 0 < (1 + s).re := by
    have h2 : -(‖s‖) ≤ s.re := neg_norm_le_re s
    have h3 : ‖s‖ ≤ 1 / 2 := by linarith [hs_bound, ha64]
    simp only [Complex.add_re, Complex.one_re]
    linarith [h2, h3]
  have hPre2 : 0 < (1 + δ / (1 + s)).re := by
    have h2 : -(‖δ / (1 + s)‖) ≤ (δ / (1 + s)).re := neg_norm_le_re _
    simp only [Complex.add_re, Complex.one_re]
    linarith [h2, hx_unif]
  have hs_pre_sub : 0 < (1 - s).re := by
    have h2 : -(‖s‖) ≤ s.re := neg_norm_le_re s
    have h4 : s.re ≤ ‖s‖ := by
      have h5 := Complex.abs_re_le_norm s
      rw [abs_le] at h5
      linarith [h5.2]
    have h3 : ‖s‖ ≤ 1 / 2 := by linarith [hs_bound, ha64]
    simp only [Complex.sub_re, Complex.one_re]
    linarith [h2, h3, h4]
  have hs1_ne : (1 : ℂ) + s ≠ 0 := by
    intro h
    have hcon := hs_pre
    rw [h] at hcon
    simp at hcon
  have hP2_ne : (1 : ℂ) + δ / (1 + s) ≠ 0 := by
    intro h
    have hcon := hPre2
    rw [h] at hcon
    simp at hcon
  have hs_ne : (1 : ℂ) - s ≠ 0 := by
    intro h
    have hcon := hs_pre_sub
    rw [h] at hcon
    simp at hcon
  have hs1_ne' : (1 : ℂ) + σ * u 0 ≠ 0 := by rw [← hs]; exact hs1_ne
  -- the decomposition of the logarithm
  have hP_eq : 1 + σ * u σ = (1 + s) * (1 + δ / (1 + s)) := by
    rw [hδdef, hs]
    rw [mul_add, mul_one, mul_div_cancel₀ _ hs1_ne']
    ring
  have hlog_decomp : Complex.log (1 / (1 + σ * u σ)) - A
      = -Complex.log (1 - s ^ 2) - Complex.log (1 + δ / (1 + s)) := by
    have hA_log : Complex.log (1 - s) = A := by
      have h1 : (1 : ℂ) - s = Complex.exp A := by rw [hs_eq]; ring
      rw [h1]
      exact Complex.log_exp hA_im.1 hA_im.2
    have hs2 : 1 - s ^ 2 = (1 - s) * (1 + s) := by ring
    have hlog_mul1 : Complex.log (1 - s ^ 2)
        = Complex.log (1 - s) + Complex.log (1 + s) := by
      rw [hs2]
      exact Complex.log_mul hs_ne hs1_ne (arg_add_mem_Ioc hs_pre_sub hs_pre)
    have hlog_mul2 : Complex.log ((1 + s) * (1 + δ / (1 + s)))
        = Complex.log (1 + s) + Complex.log (1 + δ / (1 + s)) :=
      Complex.log_mul hs1_ne hP2_ne (arg_add_mem_Ioc hs_pre hPre2)
    have hlogP : Complex.log (1 + σ * u σ)
        = Complex.log (1 + s) + Complex.log (1 + δ / (1 + s)) := by
      rw [hP_eq, hlog_mul2]
    have hlogInv : Complex.log (1 / (1 + σ * u σ)) = -Complex.log (1 + σ * u σ) := by
      simpa using Complex.log_inv _ (arg_ne_pi_of_re_pos hPre)
    rw [hlogInv, hlogP]
    have hsub : Complex.log (1 + s) = Complex.log (1 - s ^ 2) - A := by
      rw [hlog_mul1, hA_log]; ring
    rw [hsub]
    ring
  -- conclusion
  have hmain : ‖Complex.log (1 / (1 + σ * u σ)) - A‖ ≤ 600 * a ^ 2 * (1 + 1 / rr) := by
    rw [hlog_decomp]
    have h1 : ‖-Complex.log (1 - s ^ 2) - Complex.log (1 + δ / (1 + s))‖
        ≤ ‖Complex.log (1 - s ^ 2)‖ + ‖Complex.log (1 + δ / (1 + s))‖ := by
      have h := norm_sub_le (-Complex.log (1 - s ^ 2)) (Complex.log (1 + δ / (1 + s)))
      simpa using h
    have h4 : 70 * a ^ 2 + 400 * a ^ 2 / rr ≤ 600 * a ^ 2 * (1 + 1 / rr) := by
      have h5 : 70 * a ^ 2 ≤ 600 * a ^ 2 := by nlinarith [sq_nonneg a]
      have hX : 0 ≤ a ^ 2 / rr := by positivity
      have h6 : 400 * a ^ 2 / rr ≤ 600 * a ^ 2 / rr := by
        have hh := mul_le_mul_of_nonneg_right (by norm_num : (400 : ℝ) ≤ 600) hX
        calc 400 * a ^ 2 / rr = 400 * (a ^ 2 / rr) := by ring
          _ ≤ 600 * (a ^ 2 / rr) := hh
          _ = 600 * a ^ 2 / rr := by ring
      have h7 : 600 * a ^ 2 * (1 + 1 / rr) = 600 * a ^ 2 + 600 * a ^ 2 / rr := by ring
      linarith
    linarith [h1, hT1, hT2, h4]
  -- pass to the defect
  have hAc : (2 * Real.pi * Complex.I * α) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero))
      Complex.I_ne_zero) hα0
  have hnorm_inv : ‖(1 / (2 * Real.pi * Complex.I * α) : ℂ)‖ = 1 / (2 * Real.pi * a) := by
    rw [norm_div, norm_one, ← hA, hA_norm, ha]
  have hend : Work.Pert.endDefect u σ α
      = (1 / (2 * Real.pi * Complex.I * α))
        * (Complex.log (1 / (1 + σ * u σ)) - A) := by
    rw [Work.Pert.endDefect, hA, mul_sub, one_div_mul_cancel hAc]
  rw [hend, norm_mul, hnorm_inv]
  have h2pi : (0 : ℝ) < 2 * Real.pi * a := by positivity
  have hstep : (1 / (2 * Real.pi * a)) * (600 * a ^ 2 * (1 + 1 / rr)) ≤ 100 * a * (1 + 1 / rr) := by
    have h1 : 0 ≤ 1 + 1 / rr := by positivity
    have h3 : 300 / Real.pi ≤ 100 := by
      rw [div_le_iff₀ hpi]; linarith [hpi3]
    have h4 : 600 * a ^ 2 * (1 + 1 / rr)
        = (2 * Real.pi * a) * (300 * a / Real.pi * (1 + 1 / rr)) := by
      field_simp
      ring
    rw [h4, one_div, inv_mul_cancel_left₀ (ne_of_gt h2pi)]
    have h5 : 300 * a / Real.pi ≤ 100 * a := by
      rw [div_le_iff₀ hpi]; nlinarith [hpi3, ha_pos]
    exact mul_le_mul_of_nonneg_right h5 h1
  calc (1 / (2 * Real.pi * a)) * ‖Complex.log (1 / (1 + σ * u σ)) - A‖
      ≤ (1 / (2 * Real.pi * a)) * (600 * a ^ 2 * (1 + 1 / rr)) :=
        mul_le_mul_of_nonneg_left hmain (by positivity)
    _ ≤ 100 * a * (1 + 1 / rr) := hstep
    _ = 100 * ‖α‖ * (1 + 1 / rr) := by rw [ha]

end

end Work.Pert
