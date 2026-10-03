import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.L62.end_fourier
import Submission.Work.Horn.basic
import Submission.Work.Horn.pushdown_differentiableOn_punctured
import Submission.Work.Escape.exists_differentiableOn_ball_clog

namespace Work.L62

open Complex Set Filter Topology Metric
open scoped Topology

noncomputable section

/-- `qexp x = exp (-(2πi) x)`: the coordinate in which the lower end `im x → -∞` becomes `0`. -/
private def qexp (x : ℂ) : ℂ := Complex.exp (-(2 * Real.pi * Complex.I) * x)

private lemma qexp_ne_zero (x : ℂ) : qexp x ≠ 0 := Complex.exp_ne_zero _

private lemma qexp_eq_piExp_neg (a : ℂ) : qexp a = MandelDim.piExp (-a) := by
  unfold qexp MandelDim.piExp
  congr 1
  ring

private lemma qexp_eq_iff {a b : ℂ} : qexp a = qexp b ↔ ∃ k : ℤ, a = b + k := by
  rw [qexp_eq_piExp_neg a, qexp_eq_piExp_neg b, Work.Horn.MandelDim.piExp_eq_iff]
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨-k, ?_⟩
    have h2 : a = -(-b + (k : ℂ)) := by rw [← hk]; ring
    rw [h2]; push_cast; ring
  · rintro ⟨k, hk⟩
    exact ⟨-k, by rw [hk]; push_cast; ring⟩

private lemma qexp_add_int (x : ℂ) (k : ℤ) : qexp (x + k) = qexp x :=
  qexp_eq_iff.mpr ⟨k, rfl⟩

private lemma qexp_log (ζ : ℂ) (hζ : ζ ≠ 0) :
    qexp (-(Complex.log ζ / (2 * Real.pi * Complex.I))) = ζ := by
  unfold qexp
  rw [show -(2 * Real.pi * Complex.I) * (-(Complex.log ζ / (2 * Real.pi * Complex.I))) = Complex.log ζ by
    field_simp]
  exact Complex.exp_log hζ

/-- The principal lift of `qexp x` differs from `x` by an integer. -/
private lemma exists_int_log_qexp (x : ℂ) :
    ∃ k : ℤ, -(Complex.log (qexp x) / (2 * Real.pi * Complex.I)) = x + k := by
  have h : qexp (-(Complex.log (qexp x) / (2 * Real.pi * Complex.I))) = qexp x :=
    qexp_log _ (qexp_ne_zero x)
  obtain ⟨k, hk⟩ := qexp_eq_iff.mp h
  exact ⟨k, hk⟩

private lemma periodic_add_nat {G : ℂ → ℂ} {Y : ℝ}
    (hper : ∀ x : ℂ, x.im < -Y → G (x + 1) = G x) {x : ℂ} (hx : x.im < -Y) (n : ℕ) :
    G (x + n) = G x := by
  induction n with
  | zero => simp
  | succ m ih =>
      have hmem : (x + (m : ℂ)).im < -Y := by simpa using hx
      have h1 : G (x + ((m + 1 : ℕ) : ℂ)) = G (x + (m : ℂ)) := by
        rw [show x + ((m + 1 : ℕ) : ℂ) = (x + (m : ℂ)) + 1 by push_cast; ring]
        exact hper _ hmem
      rw [h1, ih]

private lemma periodic_sub_nat {G : ℂ → ℂ} {Y : ℝ}
    (hper : ∀ x : ℂ, x.im < -Y → G (x + 1) = G x) {x : ℂ} (hx : x.im < -Y) (n : ℕ) :
    G (x - n) = G x := by
  induction n with
  | zero => simp
  | succ m ih =>
      have hmem : ((x - (m : ℂ)) - 1).im < -Y := by simpa using hx
      have h1 : G ((x - (m : ℂ)) - 1) = G (x - (m : ℂ)) := by
        have hh := hper ((x - (m : ℂ)) - 1) hmem
        rw [show (x - (m : ℂ)) - 1 + 1 = x - (m : ℂ) by ring] at hh
        exact hh.symm
      rw [show x - ((m + 1 : ℕ) : ℂ) = (x - (m : ℂ)) - 1 by push_cast; ring, h1, ih]

private lemma periodic_add_int {G : ℂ → ℂ} {Y : ℝ}
    (hper : ∀ x : ℂ, x.im < -Y → G (x + 1) = G x) {x : ℂ} (hx : x.im < -Y) (k : ℤ) :
    G (x + k) = G x := by
  rcases k with n | n
  · simpa using periodic_add_nat hper hx n
  · rw [show x + (Int.negSucc n : ℤ) = x - ((n + 1 : ℕ) : ℂ) by push_cast [Int.negSucc]; ring]
    exact periodic_sub_nat hper hx (n + 1)

/-- The exponential push-down `ζ ↦ exp (-2πi G x)`, where `ζ = exp (-2πi x)`. -/
private def Phi (G : ℂ → ℂ) (ζ : ℂ) : ℂ :=
  Complex.exp (-(2 * Real.pi * Complex.I) * G (-(Complex.log ζ / (2 * Real.pi * Complex.I))))

/-- The push-down agrees with the lift. -/
private lemma Phi_val {G : ℂ → ℂ} {Y : ℝ}
    (hper : ∀ x : ℂ, x.im < -Y → G (x + 1) = G x) {x : ℂ} (hx : x.im < -Y) :
    Phi G (qexp x) = Complex.exp (-(2 * Real.pi * Complex.I) * G x) := by
  obtain ⟨k, hk⟩ := exists_int_log_qexp x
  unfold Phi
  rw [hk]
  have hshift : x + (k : ℂ) = x + k := rfl
  rw [periodic_add_int hper hx k]

lemma im_log_div_two_pi_I (ζ : ℂ) :
    (Complex.log ζ / (2 * ↑Real.pi * Complex.I)).im = -(Real.log ‖ζ‖) / (2 * Real.pi) := by
  have hre : (2 * ↑Real.pi * Complex.I : ℂ).re = 0 := by simp
  have him : (2 * ↑Real.pi * Complex.I : ℂ).im = 2 * Real.pi := by simp
  have hns : Complex.normSq (2 * ↑Real.pi * Complex.I : ℂ) = (2 * Real.pi) ^ 2 := by
    simp [Complex.normSq]; ring
  rw [Complex.div_im, hre, him, hns, Complex.log_re, Complex.log_im]
  field_simp
  ring

/-- Imaginary part of the principal lift. -/
private lemma im_log_neg (ζ : ℂ) :
    (-(Complex.log ζ / (2 * Real.pi * Complex.I))).im = Real.log ‖ζ‖ / (2 * Real.pi) := by
  have h := im_log_div_two_pi_I ζ
  simp only [Complex.neg_im, h]
  ring

private lemma re_mul_neg_two_pi_I (z : ℂ) :
    (-(2 * Real.pi * Complex.I) * z).re = 2 * Real.pi * z.im := by
  rw [Complex.mul_re]
  have h1 : (-(2 * Real.pi * Complex.I)).re = 0 := by simp
  have h2 : (-(2 * Real.pi * Complex.I)).im = -(2 * Real.pi) := by simp
  rw [h1, h2]
  ring

private lemma Phi_deep {ζ : ℂ} {Y : ℝ} (h1 : 0 < ‖ζ‖)
    (h2 : ‖ζ‖ < Real.exp (-(2 * Real.pi * Y))) :
    (-(Complex.log ζ / (2 * Real.pi * Complex.I))).im < -Y := by
  have hYζ : Real.log ‖ζ‖ < -(2 * Real.pi * Y) :=
    (Real.log_lt_iff_lt_exp h1).mpr h2
  rw [im_log_neg]
  rw [div_lt_iff₀ (by positivity : (0:ℝ) < 2 * Real.pi)]
  linarith

/-- The push-down is holomorphic on the punctured disc (across the branch cut, by periodicity). -/
private lemma Phi_holo {G : ℂ → ℂ} {Y : ℝ}
    (hd : ∀ x : ℂ, x.im < -Y → DifferentiableAt ℂ G x)
    (hper : ∀ x : ℂ, x.im < -Y → G (x + 1) = G x) :
    DifferentiableOn ℂ (Phi G) {ζ : ℂ | 0 < ‖ζ‖ ∧ ‖ζ‖ < Real.exp (-(2 * Real.pi * Y))} := by
  intro ζ₀ hζ₀
  obtain ⟨hζ₀pos, hζ₀lt⟩ := hζ₀
  have hζ₀ne : ζ₀ ≠ 0 := norm_pos_iff.mp hζ₀pos
  set x₀ : ℂ := -(Complex.log ζ₀ / (2 * Real.pi * Complex.I)) with hx₀def
  have hx₀ : x₀.im < -Y := by
    rw [hx₀def]
    exact Phi_deep hζ₀pos hζ₀lt
  set γ : ℂ → ℂ := fun ζ => x₀ - Complex.log (ζ / ζ₀) / (2 * Real.pi * Complex.I) with hγdef
  have hγdiff : DifferentiableAt ℂ γ ζ₀ := by
    have hslit : ζ₀ / ζ₀ ∈ Complex.slitPlane := by
      rw [div_self hζ₀ne]; exact Complex.one_mem_slitPlane
    have h1 : DifferentiableAt ℂ (fun ζ : ℂ => Complex.log (ζ / ζ₀)) ζ₀ :=
      (differentiableAt_id.div_const ζ₀).clog hslit
    have h2 : DifferentiableAt ℂ (fun ζ : ℂ => Complex.log (ζ / ζ₀) / (2 * Real.pi * Complex.I)) ζ₀ :=
      h1.div_const _
    rw [hγdef]
    exact h2.const_sub x₀
  have hγζ₀ : γ ζ₀ = x₀ := by
    rw [hγdef]
    simp [div_self hζ₀ne]
  have hγlift : ∀ ζ : ℂ, ζ ≠ 0 → qexp (γ ζ) = ζ := by
    intro ζ hζ
    rw [hγdef]
    unfold qexp
    rw [show -(2 * Real.pi * Complex.I) * (x₀ - Complex.log (ζ / ζ₀) / (2 * Real.pi * Complex.I)) =
        -(2 * Real.pi * Complex.I) * x₀ + Complex.log (ζ / ζ₀) by field_simp; ring,
      Complex.exp_add]
    have hx : Complex.exp (-(2 * Real.pi * Complex.I) * x₀) = ζ₀ := by
      rw [hx₀def]
      rw [show -(2 * Real.pi * Complex.I) * (-(Complex.log ζ₀ / (2 * Real.pi * Complex.I))) =
          Complex.log ζ₀ by field_simp]
      exact Complex.exp_log hζ₀ne
    rw [hx, Complex.exp_log (div_ne_zero hζ hζ₀ne)]
    field_simp
  have hint : ∀ ζ : ℂ, ζ ≠ 0 → ∃ k : ℤ, γ ζ = -(Complex.log ζ / (2 * Real.pi * Complex.I)) + k := by
    intro ζ hζ
    have h1 : qexp (γ ζ) = qexp (-(Complex.log ζ / (2 * Real.pi * Complex.I))) := by
      rw [hγlift ζ hζ, qexp_log ζ hζ]
    exact qexp_eq_iff.mp h1
  have hb2 : ∀ᶠ ζ in 𝓝 ζ₀, ζ ∈ Metric.ball (0 : ℂ) (Real.exp (-(2 * Real.pi * Y))) :=
    Metric.isOpen_ball.mem_nhds (by simpa [Metric.mem_ball, dist_eq_norm] using hζ₀lt)
  have hn2 : ∀ᶠ ζ in 𝓝 ζ₀, ζ ≠ 0 := isOpen_ne.mem_nhds hζ₀ne
  have heq : Phi G =ᶠ[𝓝 ζ₀] fun ζ => Complex.exp (-(2 * Real.pi * Complex.I) * G (γ ζ)) := by
    filter_upwards [hb2, hn2] with ζ hb hn
    have hsmall : ‖ζ‖ < Real.exp (-(2 * Real.pi * Y)) := by
      simpa [Metric.mem_ball, dist_eq_norm] using hb
    obtain ⟨k, hk⟩ := hint ζ hn
    unfold Phi
    rw [hk, periodic_add_int hper (Phi_deep (norm_pos_iff.mpr hn) hsmall) k]
  have hmem : γ ζ₀ ∈ {x : ℂ | x.im < -Y} := by rw [hγζ₀]; exact hx₀
  have hG1 : DifferentiableAt ℂ (fun ζ => G (γ ζ)) ζ₀ := (hd (γ ζ₀) hmem).comp ζ₀ hγdiff
  have hprod : DifferentiableAt ℂ (fun ζ => -(2 * Real.pi * Complex.I) * G (γ ζ)) ζ₀ :=
    (differentiableAt_const _).mul hG1
  have h1 : DifferentiableAt ℂ (fun ζ => Complex.exp (-(2 * Real.pi * Complex.I) * G (γ ζ))) ζ₀ :=
    Complex.differentiableAt_exp.comp ζ₀ hprod
  exact (h1.congr_of_eventuallyEq heq).differentiableWithinAt

private lemma Phi_bdd {G : ℂ → ℂ} {Y δ : ℝ}
    (hbd : ∀ x : ℂ, x.im < -Y → ‖G x‖ ≤ δ) :
    ∀ ζ : ℂ, 0 < ‖ζ‖ → ‖ζ‖ < Real.exp (-(2 * Real.pi * Y)) → ‖Phi G ζ‖ ≤ Real.exp (2 * Real.pi * δ) := by
  intro ζ h1 h2
  have hx := Phi_deep h1 h2
  have hb := hbd _ hx
  have hIm : (G (-(Complex.log ζ / (2 * Real.pi * Complex.I)))).im ≤ δ :=
    le_trans (le_abs_self _) (le_trans (Complex.abs_im_le_norm _) hb)
  unfold Phi
  rw [Complex.norm_exp, re_mul_neg_two_pi_I]
  exact Real.exp_le_exp.mpr
    (mul_le_mul_of_nonneg_left hIm (by positivity : (0:ℝ) ≤ 2 * Real.pi))

private lemma Phi_bdd_lower {G : ℂ → ℂ} {Y δ : ℝ}
    (hbd : ∀ x : ℂ, x.im < -Y → ‖G x‖ ≤ δ) :
    ∀ ζ : ℂ, 0 < ‖ζ‖ → ‖ζ‖ < Real.exp (-(2 * Real.pi * Y)) →
      Real.exp (-(2 * Real.pi * δ)) ≤ ‖Phi G ζ‖ := by
  intro ζ h1 h2
  have hx := Phi_deep h1 h2
  have hb := hbd _ hx
  have hIm : -δ ≤ (G (-(Complex.log ζ / (2 * Real.pi * Complex.I)))).im := by
    have h2' : |(G (-(Complex.log ζ / (2 * Real.pi * Complex.I)))).im| ≤ δ :=
      le_trans (Complex.abs_im_le_norm _) hb
    have h3 := neg_abs_le (G (-(Complex.log ζ / (2 * Real.pi * Complex.I)))).im
    linarith
  unfold Phi
  rw [Complex.norm_exp, re_mul_neg_two_pi_I]
  refine Real.exp_le_exp.mpr ?_
  rw [show -(2 * Real.pi * δ) = 2 * Real.pi * (-δ) by ring]
  exact mul_le_mul_of_nonneg_left hIm (by positivity : (0:ℝ) ≤ 2 * Real.pi)

/-- `‖qexp w‖ = exp (2π im w)`. -/
private lemma norm_qexp (w : ℂ) : ‖qexp w‖ = Real.exp (2 * Real.pi * w.im) := by
  unfold qexp
  rw [Complex.norm_exp, re_mul_neg_two_pi_I]

/-- `qexp` is holomorphic. -/
private lemma differentiableAt_qexp (w : ℂ) : DifferentiableAt ℂ qexp w := by
  unfold qexp
  fun_prop

/-- `qexp` tends to `0` at the lower end. -/
private lemma tendsto_qexp :
    Tendsto qexp (comap Complex.im atBot) (𝓝 0) := by
  have h1 : Tendsto (fun y : ℝ => 2 * Real.pi * y) atBot atBot := by
    rw [Filter.tendsto_atBot]
    intro b
    filter_upwards [eventually_le_atBot (b / (2 * Real.pi))] with y hy
    have h2pi : (0:ℝ) < 2 * Real.pi := by positivity
    have h := mul_le_mul_of_nonneg_right hy h2pi.le
    rw [div_mul_cancel₀ b (ne_of_gt h2pi)] at h
    linarith
  have h2 : Tendsto (fun y : ℝ => Real.exp (2 * Real.pi * y)) atBot (𝓝 0) :=
    Real.tendsto_exp_atBot.comp h1
  have h3 : (fun w : ℂ => ‖qexp w‖) = (fun y : ℝ => Real.exp (2 * Real.pi * y)) ∘ Complex.im := by
    funext w
    rw [Function.comp_apply, norm_qexp]
  have h4 : Tendsto (fun w : ℂ => ‖qexp w‖) (comap Complex.im atBot) (𝓝 0) := by
    rw [h3]
    exact h2.comp Filter.tendsto_comap
  rwa [tendsto_zero_iff_norm_tendsto_zero]

/-- **Inverting a periodic perturbation of the identity near an end.** -/
theorem near_translation_inverse {G : ℂ → ℂ} {Y δ : ℝ}
    (hd : ∀ x : ℂ, x.im < -Y → DifferentiableAt ℂ G x)
    (hper : ∀ x : ℂ, x.im < -Y → G (x + 1) = G x)
    (hbd : ∀ x : ℂ, x.im < -Y → ‖G x‖ ≤ δ) :
    ∃ (x : ℂ → ℂ) (Y' : ℝ), Y ≤ Y' ∧
      DifferentiableOn ℂ x {w : ℂ | w.im < -Y'} ∧
      ∀ w : ℂ, w.im < -Y' →
        x w + G (x w) = w ∧ x (w + 1) = x w + 1 ∧ (x w).im < -Y ∧ ‖x w - w‖ ≤ δ := by
  have hr : 0 < Real.exp (-(2 * Real.pi * Y)) := Real.exp_pos _
  -- ## 1. the push-down, its bounds and its extension to `0`
  have hdiffΦ : DifferentiableOn ℂ (Phi G)
      (Metric.ball (0 : ℂ) (Real.exp (-(2 * Real.pi * Y))) \ {0}) := by
    intro ζ hζ
    obtain ⟨hb, hne⟩ := hζ
    have h1 : 0 < ‖ζ‖ := norm_pos_iff.mpr hne
    have h2 : ‖ζ‖ < Real.exp (-(2 * Real.pi * Y)) := by
      simpa [Metric.mem_ball, dist_eq_norm] using hb
    refine (Phi_holo hd hper ζ ⟨h1, h2⟩).mono ?_
    intro z hz
    obtain ⟨hz1, hz2⟩ := hz
    exact ⟨norm_pos_iff.mpr hz2, by simpa [Metric.mem_ball, dist_eq_norm] using hz1⟩
  have hbddΦ : BddAbove (norm ∘ Phi G ''
      (Metric.ball (0 : ℂ) (Real.exp (-(2 * Real.pi * Y))) \ {0})) := by
    refine ⟨Real.exp (2 * Real.pi * δ), ?_⟩
    rintro y ⟨ζ, hζ, rfl⟩
    obtain ⟨hb, hne⟩ := hζ
    have h1 : 0 < ‖ζ‖ := norm_pos_iff.mpr hne
    have h2 : ‖ζ‖ < Real.exp (-(2 * Real.pi * Y)) := by
      simpa [Metric.mem_ball, dist_eq_norm] using hb
    exact Phi_bdd hbd ζ h1 h2
  have hriem := Complex.differentiableOn_update_limUnder_of_bddAbove (f := Phi G)
    (s := Metric.ball (0 : ℂ) (Real.exp (-(2 * Real.pi * Y)))) (c := 0)
    (Metric.ball_mem_nhds 0 hr) hdiffΦ hbddΦ
  set Φt : ℂ → ℂ := Function.update (Phi G) 0 ((𝓝[≠] (0:ℂ)).limUnder (Phi G)) with hΦtdef
  have hΦt_diff : DifferentiableOn ℂ Φt (Metric.ball (0 : ℂ) (Real.exp (-(2 * Real.pi * Y)))) := by
    rw [hΦtdef]; exact hriem
  have hΦt0 : Φt 0 = (𝓝[≠] (0:ℂ)).limUnder (Phi G) := by
    rw [hΦtdef]; exact Function.update_self 0 _ _
  have hΦt_agree : ∀ ζ : ℂ, ζ ≠ 0 → Φt ζ = Phi G ζ := by
    intro ζ hζ
    rw [hΦtdef]; exact Function.update_of_ne hζ _ _
  have hΦt_ana : AnalyticAt ℂ Φt 0 := hΦt_diff.analyticAt (Metric.ball_mem_nhds 0 hr)
  have hlim : Tendsto (Phi G) (𝓝[≠] (0:ℂ)) (𝓝 ((𝓝[≠] (0:ℂ)).limUnder (Phi G))) := by
    have hc : ContinuousAt Φt 0 := hΦt_diff.continuousOn.continuousAt (Metric.ball_mem_nhds 0 hr)
    have h1 : Tendsto Φt (𝓝[≠] (0:ℂ)) (𝓝 (Φt 0)) := hc.tendsto.mono_left nhdsWithin_le_nhds
    rw [hΦt0] at h1
    refine h1.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ζ hζ
    exact hΦt_agree ζ hζ
  have hc_ne : (𝓝[≠] (0:ℂ)).limUnder (Phi G) ≠ 0 := by
    have hlow : ∀ᶠ ζ : ℂ in 𝓝[≠] (0:ℂ),
        Real.exp (-(2 * Real.pi * δ)) ≤ ‖Phi G ζ‖ := by
      have hb : ∀ᶠ ζ : ℂ in 𝓝 (0:ℂ), ζ ∈ Metric.ball 0 (Real.exp (-(2 * Real.pi * Y))) :=
        Metric.ball_mem_nhds 0 hr
      filter_upwards [hb.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with ζ hbζ hζne
      have h1 : 0 < ‖ζ‖ := norm_pos_iff.mpr hζne
      have h2 : ‖ζ‖ < Real.exp (-(2 * Real.pi * Y)) := by
        simpa [Metric.mem_ball, dist_eq_norm] using hbζ
      exact Phi_bdd_lower hbd ζ h1 h2
    intro h0
    have h1 := ge_of_tendsto hlim.norm hlow
    rw [h0, norm_zero] at h1
    have h2 := Real.exp_pos (-(2 * Real.pi * δ))
    linarith
  -- ## 2. the local inverse of `ζ ↦ ζ · Φt ζ`
  set F : ℂ → ℂ := fun ζ => ζ * Φt ζ with hFdef
  have hF_ana : AnalyticAt ℂ F 0 := by
    rw [hFdef]
    exact analyticAt_id.mul hΦt_ana
  have hF0 : F 0 = 0 := by
    rw [hFdef]; simp
  have hFd : deriv F 0 = (𝓝[≠] (0:ℂ)).limUnder (Phi G) := by
    have h1 : HasDerivAt (fun ζ : ℂ => ζ * Φt ζ) (1 * Φt 0 + 0 * deriv Φt 0) 0 :=
      (hasDerivAt_id 0).mul (hΦt_ana.differentiableAt.hasDerivAt)
    rw [hFdef, h1.deriv, hΦt0]
    ring
  have hFd_ne : deriv F 0 ≠ 0 := by rw [hFd]; exact hc_ne
  set η : ℂ → ℂ := (hF_ana.hasStrictDerivAt).localInverse F (deriv F 0) 0 hFd_ne with hηdef
  have hη_ana : AnalyticAt ℂ η 0 := by
    rw [hηdef]
    have h := hF_ana.analyticAt_localInverse hFd_ne
    rwa [hF0] at h
  have hη_right : ∀ᶠ ζ in 𝓝 (0:ℂ), F (η ζ) = ζ := by
    have h := (hF_ana.hasStrictDerivAt).eventually_right_inverse (f := F) (f' := deriv F 0) (a := 0) hFd_ne
    rw [hF0] at h
    exact h
  obtain ⟨r₃, hr₃, hball₃⟩ := Metric.mem_nhds_iff.mp hη_right
  have hη_left : ∀ᶠ x in 𝓝 (0:ℂ), η (F x) = x := by
    have h := (hF_ana.hasStrictDerivAt).eventually_left_inverse (f := F) (f' := deriv F 0) (a := 0) hFd_ne
    exact h
  have hηd : HasStrictDerivAt η ((deriv F 0)⁻¹) (F 0) := by
    rw [hηdef]
    exact (hF_ana.hasStrictDerivAt).to_localInverse hFd_ne
  have hηd_ne : deriv η 0 ≠ 0 := by
    have h1 : deriv η 0 = (deriv F 0)⁻¹ := by
      have h := hηd.hasDerivAt.deriv
      rwa [hF0] at h
    rw [h1]
    exact inv_ne_zero hFd_ne
  have hη0 : η 0 = 0 := by
    obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hη_left
    have hcontη : Tendsto η (𝓝 (0:ℂ)) (𝓝 (η 0)) := hη_ana.continuousAt
    have hcontF : Tendsto F (𝓝 (0:ℂ)) (𝓝 (0:ℂ)) := by
      have h := hF_ana.continuousAt
      simp only [ContinuousAt] at h
      rwa [hF0] at h
    have h1 : Tendsto (fun x : ℂ => η (F x)) (𝓝 (0:ℂ)) (𝓝 (η 0)) := hcontη.comp hcontF
    have heq : (fun x : ℂ => η (F x)) =ᶠ[𝓝 (0:ℂ)] (fun x : ℂ => x) := by
      filter_upwards [Metric.ball_mem_nhds 0 hr] with x hx
      exact hball (Metric.mem_ball.mp hx)
    have h2 : Tendsto (fun x : ℂ => η (F x)) (𝓝 (0:ℂ)) (𝓝 (0:ℂ)) :=
      Filter.Tendsto.congr' heq.symm tendsto_id
    exact tendsto_nhds_unique h1 h2
  -- ## 3. the holomorphic logarithm of `ζ ↦ η ζ / ζ`
  have hη_ev : ∀ᶠ y in 𝓝 (0:ℂ), AnalyticAt ℂ η y := hη_ana.eventually_analyticAt
  obtain ⟨r₁, hr₁, hball₁⟩ := Metric.mem_nhds_iff.mp hη_ev
  have hη_diff_on : DifferentiableOn ℂ η (Metric.ball 0 r₁) := fun y hy =>
    (hball₁ (Metric.mem_ball.mp hy)).differentiableAt.differentiableWithinAt
  set μ : ℂ → ℂ := dslope η 0 with hμdef
  have hμ_diff : DifferentiableOn ℂ μ (Metric.ball 0 r₁) := by
    rw [hμdef]
    exact (Complex.differentiableOn_dslope (f := η) (c := 0)
      (Metric.ball_mem_nhds 0 hr₁)).mpr hη_diff_on
  have hμ0 : μ 0 = deriv η 0 := by rw [hμdef]; exact dslope_same η 0
  have hμ0_ne : μ 0 ≠ 0 := by rw [hμ0]; exact hηd_ne
  have hμ_cont : ContinuousAt μ 0 :=
    hμ_diff.continuousOn.continuousAt (Metric.ball_mem_nhds 0 hr₁)
  have hμ_evne : ∀ᶠ ζ in 𝓝 (0:ℂ), μ ζ ≠ 0 :=
    hμ_cont.preimage_mem_nhds (isOpen_ne.mem_nhds hμ0_ne)
  obtain ⟨r₂, hr₂, hball₂⟩ := Metric.mem_nhds_iff.mp hμ_evne
  set R : ℝ := min r₁ r₂ with hRdef
  have hRpos : 0 < R := lt_min hr₁ hr₂
  have hμ_diffR : DifferentiableOn ℂ μ (Metric.ball 0 R) :=
    hμ_diff.mono (Metric.ball_subset_ball (min_le_left _ _))
  have hμ_neR : ∀ ζ ∈ Metric.ball (0:ℂ) R, μ ζ ≠ 0 := fun ζ hζ =>
    hball₂ (Metric.mem_ball.mp (Metric.ball_subset_ball (min_le_right _ _) hζ))
  obtain ⟨L, hLdiff, hLexp, -⟩ := Work.Escape.exists_differentiableOn_ball_clog
    (g := μ) (c := 0) (r := R) hμ_diffR hμ_neR
  have hLcont : ContinuousAt L 0 := hLdiff.continuousOn.continuousAt (Metric.ball_mem_nhds 0 hRpos)
  -- ## 4. the lift `X` and the eventual smallness of the relevant quantities
  set X : ℂ → ℂ := fun w => w - L (qexp w) / (2 * Real.pi * Complex.I) with hXdef
  have hXexp : ∀ w : ℂ, ‖qexp w‖ < R →
      Complex.exp (-(2 * Real.pi * Complex.I) * X w) = η (qexp w) := by
    intro w hw
    have hq : qexp w ≠ 0 := qexp_ne_zero w
    have hmem : qexp w ∈ Metric.ball (0:ℂ) R := by
      rw [Metric.mem_ball, dist_eq_norm]; simpa using hw
    rw [hXdef]
    rw [show -(2 * Real.pi * Complex.I) * (w - L (qexp w) / (2 * Real.pi * Complex.I)) =
        -(2 * Real.pi * Complex.I) * w + L (qexp w) by field_simp; ring,
      Complex.exp_add, hLexp (qexp w) hmem]
    have hμv : μ (qexp w) = (η (qexp w) - η 0) / (qexp w - 0) := by
      rw [hμdef, dslope_of_ne η hq, slope_def_field]
    rw [hμv, hη0]
    rw [show Complex.exp (-(2 * Real.pi * Complex.I) * w) = qexp w from rfl]
    field_simp
    ring
  have hq0 : Tendsto qexp (comap Complex.im atBot) (𝓝 0) := tendsto_qexp
  have hL0t : Tendsto (fun w => L (qexp w)) (comap Complex.im atBot) (𝓝 (L 0)) :=
    hLcont.tendsto.comp hq0
  have hXsub : Tendsto (fun w => X w - w) (comap Complex.im atBot)
      (𝓝 (-(L 0) / (2 * Real.pi * Complex.I))) := by
    have h1 : Tendsto (fun w => -(L (qexp w)) / (2 * Real.pi * Complex.I))
        (comap Complex.im atBot) (𝓝 (-(L 0) / (2 * Real.pi * Complex.I))) := by
      have hc : Continuous (fun z : ℂ => -z / (2 * Real.pi * Complex.I)) := by fun_prop
      exact (hc.tendsto (L 0)).comp hL0t
    refine h1.congr' ?_
    filter_upwards with w
    rw [hXdef]
    ring
  have hb1 : Tendsto (fun w : ℂ => w.im) (comap Complex.im atBot) atBot := Filter.tendsto_comap
  have himX : Tendsto (fun w : ℂ => (X w).im) (comap Complex.im atBot) atBot := by
    have hsum : Tendsto (fun w : ℂ => w.im + (X w - w).im) (comap Complex.im atBot) atBot := by
      rw [Filter.tendsto_atBot]
      intro b
      set c : ℂ := -(L 0) / (2 * Real.pi * Complex.I) with hcdef
      have hc : Tendsto (fun w : ℂ => (X w - w).im) (comap Complex.im atBot) (𝓝 c.im) :=
        (Complex.continuous_im.tendsto _).comp hXsub
      have hset : {y : ℝ | y ≤ c.im + 1} ∈ 𝓝 c.im := by
        refine Filter.mem_of_superset (Metric.ball_mem_nhds c.im (by norm_num : (0:ℝ) < 1)) ?_
        intro y hy
        rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hy
        have : y < c.im + 1 := by linarith [hy.2]
        exact le_of_lt this
      have h2 : ∀ᶠ w in comap Complex.im atBot, (X w - w).im ≤ c.im + 1 := hc.eventually hset
      have h3 : ∀ᶠ w in comap Complex.im atBot, w.im ≤ b - c.im - 1 :=
        (Filter.tendsto_atBot.mp hb1) _
      filter_upwards [h2, h3] with w h2w h3w
      have hthis : (X w).im = w.im + (X w - w).im := by
        rw [show X w = w + (X w - w) by ring]
        simp
      rw [← hthis]
      linarith
    refine Filter.Tendsto.congr' ?_ hsum
    filter_upwards with w
    have hthis : (X w).im = w.im + (X w - w).im := by
      rw [show X w = w + (X w - w) by ring]
      simp
    exact hthis.symm
  have hXim : Tendsto X (comap Complex.im atBot) (comap Complex.im atBot) :=
    Filter.tendsto_comap_iff.mpr himX
  have hqX : Tendsto (fun w => qexp (X w)) (comap Complex.im atBot) (𝓝 0) := hq0.comp hXim
  set ρ : ℝ := min R r₃ with hρdef
  have hA : ∀ᶠ w : ℂ in comap Complex.im atBot,
      ‖qexp w‖ < ρ ∧ ‖qexp (X w)‖ < ρ ∧ (X w).im < -Y := by
    have h1 : ∀ᶠ w : ℂ in comap Complex.im atBot, ‖qexp w‖ < ρ := by
      have h := (Metric.tendsto_nhds.mp hq0) ρ (lt_min hRpos hr₃)
      filter_upwards [h] with w hw
      simpa [dist_eq_norm] using hw
    have h2 : ∀ᶠ w : ℂ in comap Complex.im atBot, ‖qexp (X w)‖ < ρ := by
      have h := (Metric.tendsto_nhds.mp hqX) ρ (lt_min hRpos hr₃)
      filter_upwards [h] with w hw
      simpa [dist_eq_norm] using hw
    have h3 : ∀ᶠ w : ℂ in comap Complex.im atBot, (X w).im < -Y := by
      have := (Filter.tendsto_atBot.mp himX) (-Y - 1)
      filter_upwards [this] with w hw
      linarith
    filter_upwards [h1, h2, h3] with w h1w h2w h3w
    exact ⟨h1w, h2w, h3w⟩
  -- ## 5. `X w + G (X w) - w` is a globally constant integer
  obtain ⟨b, hb⟩ := Filter.eventually_atBot.mp (Filter.eventually_comap.mp hA)
  have hP : ∀ w : ℂ, w.im ≤ b → ‖qexp w‖ < ρ ∧ ‖qexp (X w)‖ < ρ ∧ (X w).im < -Y :=
    fun w hw => hb w.im hw w rfl
  have hZj : ∀ w : ℂ, w.im ≤ b → ∃ k : ℤ, X w + G (X w) = w + k := by
    intro w hw
    obtain ⟨h1, h2, h3⟩ := hP w hw
    have h1R : ‖qexp w‖ < R := lt_of_lt_of_le h1 (min_le_left R r₃)
    have h1r₃ : ‖qexp w‖ < r₃ := lt_of_lt_of_le h1 (min_le_right R r₃)
    have hsec : F (η (qexp w)) = qexp w :=
      hball₃ (Metric.mem_ball.mpr (by simpa [dist_eq_norm] using h1r₃))
    rw [← hXexp w h1R] at hsec
    rw [hFdef] at hsec
    change qexp (X w) * Φt (qexp (X w)) = qexp w at hsec
    have hΦ : Φt (qexp (X w)) = Complex.exp (-(2 * Real.pi * Complex.I) * G (X w)) := by
      rw [hΦt_agree _ (qexp_ne_zero _), Phi_val hper h3]
    rw [hΦ] at hsec
    have hq : qexp (X w + G (X w)) = qexp (X w) * qexp (G (X w)) := by
      unfold qexp
      rw [show -(2 * Real.pi * Complex.I) * (X w + G (X w))
          = -(2 * Real.pi * Complex.I) * X w + -(2 * Real.pi * Complex.I) * G (X w) by ring,
        Complex.exp_add]
    have hqG : qexp (G (X w)) = Complex.exp (-(2 * Real.pi * Complex.I) * G (X w)) := rfl
    have hgoal : qexp (X w + G (X w)) = qexp w := by
      rw [hq, hqG]
      exact hsec
    exact qexp_eq_iff.mp hgoal
  -- the constant on the half-plane `{im < b}`
  set S : Set ℂ := {w : ℂ | w.im < b} with hSdef
  have hS_pre : IsPreconnected S :=
    (convex_halfSpace_im_lt b).isPreconnected
  have hXhol : ∀ w ∈ S, DifferentiableAt ℂ X w := by
    intro w hw
    have h1 : ‖qexp w‖ < ρ := (hP w (le_of_lt hw)).1
    have h2 : qexp w ∈ Metric.ball (0:ℂ) R := by
      rw [Metric.mem_ball, dist_eq_norm]
      simpa using lt_of_lt_of_le h1 (min_le_left R r₃)
    have h3 : DifferentiableAt ℂ (fun w : ℂ => L (qexp w)) w :=
      (hLdiff.differentiableAt (Metric.isOpen_ball.mem_nhds h2)).comp w
        (differentiableAt_qexp w)
    have h4 : DifferentiableAt ℂ (fun w : ℂ => L (qexp w) / (2 * Real.pi * Complex.I)) w :=
      h3.div_const _
    rw [hXdef]
    exact differentiableAt_id.sub h4
  have hZrange : ∀ w : ℂ, w.im < b → ∃ k : ℤ, X w + G (X w) - w = (k : ℂ) := by
    intro w hw
    obtain ⟨k, hk⟩ := hZj w (le_of_lt hw)
    exact ⟨k, by rw [hk]; ring⟩
  have hlocc : IsLocallyConstant (fun s : S => X s.1 + G (X s.1) - s.1) := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro s
    have hcontj : ContinuousAt (fun y : S => X y.1 + G (X y.1) - y.1) s := by
      have h1 : ContinuousAt (fun w : ℂ => X w + G (X w) - w) s.1 := by
        have h2 : DifferentiableAt ℂ (fun w : ℂ => G (X w)) s.1 :=
          (hd (X s.1) (hP s.1 (le_of_lt s.2)).2.2).comp s.1 (hXhol s.1 s.2)
        have h3 : DifferentiableAt ℂ (fun w : ℂ => X w + G (X w) - w) s.1 :=
          ((hXhol s.1 s.2).add h2).sub differentiableAt_id
        exact h3.continuousAt
      exact h1.comp continuous_subtype_val.continuousAt
    have hev : ∀ᶠ y : S in 𝓝 s,
        ‖(X y.1 + G (X y.1) - y.1) - (X s.1 + G (X s.1) - s.1)‖ < 1/2 := by
      have h := (Metric.tendsto_nhds.mp hcontj.tendsto) (1/2) (by norm_num)
      filter_upwards [h] with y hy
      simpa [dist_eq_norm] using hy
    filter_upwards [hev] with y hy
    obtain ⟨k', hk'⟩ := hZrange y.1 y.2
    obtain ⟨k, hk⟩ := hZrange s.1 s.2
    have hdist : ‖((k' : ℂ) - (k : ℂ))‖ < 1/2 := by
      rw [hk', hk] at hy
      exact hy
    have hkk : k' = k := by
      by_contra hne
      have h3 : (1:ℝ) ≤ ‖((k' - k : ℤ) : ℂ)‖ := by
        rw [Complex.norm_intCast]
        exact_mod_cast Int.one_le_abs (sub_ne_zero.mpr hne)
      have h4 : ‖((k' : ℂ) - (k : ℂ))‖ = ‖((k' - k : ℤ) : ℂ)‖ := by push_cast; ring_nf
      rw [h4] at hdist
      linarith
    rw [hk', hk, hkk]
  -- turn the local constancy into a constant
  have hSpre : PreconnectedSpace S := (isPreconnected_iff_preconnectedSpace.mp hS_pre)
  have hmem₀ : ((b - 1) * Complex.I).im < b := by
    rw [Complex.mul_I_im]
    simp
  set w₀ : S := ⟨(b - 1) * Complex.I, hmem₀⟩ with hw₀def
  have hconst : ∀ s : S, X s.1 + G (X s.1) - s.1 = X w₀.1 + G (X w₀.1) - w₀.1 :=
    fun s => hlocc.apply_eq_of_isPreconnected isPreconnected_univ (Set.mem_univ _) (Set.mem_univ _)
  set k₀ : ℤ := Classical.choose (hZrange w₀.1 w₀.2) with hk₀def
  have hk₀ : X w₀.1 + G (X w₀.1) - w₀.1 = (k₀ : ℂ) := Classical.choose_spec (hZrange w₀.1 w₀.2)
  -- ## 6. the solution
  have hbdom : -(max Y (-b)) ≤ b := by
    have : -b ≤ max Y (-b) := le_max_right _ _
    linarith
  refine ⟨fun w => X w - k₀, max Y (-b), le_max_left _ _, ?_, ?_⟩
  · intro w hw
    have hwb : w.im < b := lt_of_lt_of_le hw hbdom
    exact ((hXhol w hwb).sub_const k₀).differentiableWithinAt
  · intro w hw
    have hwb : w.im < b := lt_of_lt_of_le hw hbdom
    obtain ⟨h1, h2, h3⟩ := hP w (le_of_lt hwb)
    have hdeep : (X w).im < -Y := h3
    have hj : X w + G (X w) - w = (k₀ : ℂ) := by
      have h := hconst ⟨w, hwb⟩
      rw [h]; exact hk₀
    have hperk : G (X w - (k₀ : ℂ)) = G (X w) := by
      have h := periodic_add_int hper hdeep (-k₀)
      have he : X w + ((-k₀ : ℤ) : ℂ) = X w - (k₀ : ℂ) := by push_cast; ring
      rw [he] at h
      exact h
    have hG : X w - (k₀ : ℂ) + G (X w - (k₀ : ℂ)) = w := by
      have h2 : X w + G (X w) = w + (k₀ : ℂ) := by
        have h5 : X w + G (X w) = (k₀ : ℂ) + w := by
          have h6 := hj
          rw [sub_eq_iff_eq_add] at h6
          exact h6
        rw [h5]; ring
      rw [hperk, show X w - (k₀ : ℂ) + G (X w) = X w + G (X w) - (k₀ : ℂ) by ring, h2]
      ring
    have hstep : X (w + 1) = X w + 1 := by
      have hq1 : qexp (w + 1) = qexp w := qexp_eq_iff.mpr ⟨1, by ring⟩
      rw [hXdef]
      show (w + 1) - L (qexp (w + 1)) / (2 * Real.pi * Complex.I)
          = w - L (qexp w) / (2 * Real.pi * Complex.I) + 1
      rw [hq1]
      ring
    have hnorm : X w - (k₀ : ℂ) - w = -G (X w - (k₀ : ℂ)) := by linear_combination hG
    refine ⟨hG, ?_, ?_, ?_⟩
    · show X (w + 1) - (k₀ : ℂ) = X w - (k₀ : ℂ) + 1
      rw [hstep]
      ring
    · show (X w - (k₀ : ℂ)).im < -Y
      simpa using hdeep
    · show ‖X w - (k₀ : ℂ) - w‖ ≤ δ
      rw [hnorm, norm_neg]
      exact hbd _ (by simpa using hdeep)

/-- A holomorphic function on a lower half-plane that is `1`-periodic and bounded there has a
limit at the lower end `comap im atBot`. -/
theorem tendsto_atBot_of_periodic_bounded {φ : ℂ → ℂ} {Y B : ℝ}
    (hd : ∀ w : ℂ, w.im < -Y → DifferentiableAt ℂ φ w)
    (hper : ∀ w : ℂ, w.im < -Y → φ (w + 1) = φ w)
    (hbd : ∀ w : ℂ, w.im < -Y → ‖φ w‖ ≤ B) :
    ∃ c : ℂ, Filter.Tendsto φ (Filter.comap Complex.im Filter.atBot) (nhds c) := by
  set φ' : ℂ → ℂ := fun w => φ (-w) with hφ'def
  have hper' : ∀ w : ℂ, (Y + 1) ≤ w.im → φ' (w + 1) = φ' w := by
    intro w hw
    show φ (-(w + 1)) = φ (-w)
    have him : (-(w + 1)).im = -w.im := by simp
    have hmem : (-(w + 1)).im < -Y := by rw [him]; linarith
    have h := hper (-(w + 1)) hmem
    rw [show (-(w + 1)) + 1 = -w by ring] at h
    exact h.symm
  have hhol' : DifferentiableOn ℂ φ' {w : ℂ | (Y + 1) ≤ w.im} := by
    intro w hw
    have hw' : Y + 1 ≤ w.im := hw
    have him : (-w).im = -w.im := by simp
    have hmem : (-w).im < -Y := by rw [him]; linarith
    exact ((hd (-w) hmem).comp w (by fun_prop)).differentiableWithinAt
  have hbd' : ∀ w : ℂ, (Y + 1) ≤ w.im → ‖φ' w‖ ≤ B := by
    intro w hw
    have hw' : Y + 1 ≤ w.im := hw
    have him : (-w).im = -w.im := by simp
    exact hbd (-w) (by rw [him]; linarith)
  obtain ⟨c, M, hM⟩ := end_fourier (Y := Y + 1) (B := B) hper' hhol' hbd'
  refine ⟨c, ?_⟩
  rw [Filter.tendsto_def]
  intro s hs
  obtain ⟨ε, hε, hεs⟩ := Metric.mem_nhds_iff.mp hs
  have haff : Tendsto (fun b : ℝ => -2 * Real.pi * (-b - (Y + 2))) atBot atBot := by
    rw [Filter.tendsto_atBot]
    intro a
    filter_upwards [eventually_le_atBot (a / (2 * Real.pi) - Y - 2)] with b hb
    have h2pi : (0:ℝ) < 2 * Real.pi := by positivity
    have h := mul_le_mul_of_nonneg_right hb h2pi.le
    have h4 : (a / (2 * Real.pi) - Y - 2) * (2 * Real.pi) = a - (Y + 2) * (2 * Real.pi) := by
      field_simp
      ring
    have heq : -2 * Real.pi * (-b - (Y + 2)) = 2 * Real.pi * (b + Y + 2) := by ring
    rw [heq]
    nlinarith [h, h4, h2pi]
  have hexp : Tendsto (fun b : ℝ => M * Real.exp (-2 * Real.pi * (-b - (Y + 2))))
      atBot (nhds 0) := by
    have h1 : Tendsto (fun b : ℝ => Real.exp (-2 * Real.pi * (-b - (Y + 2)))) atBot (nhds 0) :=
      Real.tendsto_exp_atBot.comp haff
    have h2 := h1.const_mul M
    simpa using h2
  have hev : ∀ᶠ b : ℝ in atBot, ‖M * Real.exp (-2 * Real.pi * (-b - (Y + 2)))‖ < ε := by
    have h3 := hexp.eventually (Metric.ball_mem_nhds (0:ℝ) hε)
    filter_upwards [h3] with b hb
    simpa [Metric.mem_ball, dist_eq_norm] using hb
  obtain ⟨b₀, hb₀⟩ := eventually_atBot.mp hev
  refine Filter.mem_comap.mpr ⟨Set.Iic (min b₀ (-Y - 2)),
    Filter.mem_atBot_sets.mpr ⟨_, fun b' hb' => hb'⟩, ?_⟩
  intro w hw
  simp only [Set.mem_preimage, Set.mem_Iic] at hw ⊢
  have hw1 : w.im ≤ b₀ := le_trans hw (min_le_left _ _)
  have hw2 : w.im ≤ -Y - 2 := le_trans hw (min_le_right _ _)
  have hYw : Y + 1 + 1 ≤ (-w).im := by
    have his : (-w).im = -w.im := by simp
    rw [his]; linarith
  have hb := hM (-w) hYw
  have harg : (-w).im - (Y + 1) - 1 = -w.im - (Y + 2) := by simp; ring
  rw [harg] at hb
  have h1 : ‖φ w - c‖ ≤ M * Real.exp (-2 * Real.pi * (-w.im - (Y + 2))) := by
    simpa [hφ'def] using hb
  have h2 : M * Real.exp (-2 * Real.pi * (-w.im - (Y + 2)))
      ≤ ‖M * Real.exp (-2 * Real.pi * (-w.im - (Y + 2)))‖ := by
    rw [Real.norm_eq_abs]; exact le_abs_self _
  exact hεs (Metric.mem_ball.mpr (by
    simpa [dist_eq_norm] using lt_of_le_of_lt (le_trans h1 h2) (hb₀ w.im hw1)))

theorem deriv_E_sub_id_lower {g₀ : ℂ → ℂ} {D : Set ℂ} (d : MandelDim.ParabData g₀ D) :
    ∀ ε > 0, ∃ Y : ℝ, ∀ w : ℂ, w.im < -Y → ‖deriv (fun u : ℂ => d.E u - u) w‖ ≤ ε := by
  intro ε hε
  obtain ⟨cl, hcl⟩ := Work.Horn.MandelDim.ParabData.E_lower_iff d
  obtain ⟨R₁, hR₁⟩ := hcl 1 zero_lt_one
  set Y₀ : ℝ := max (max (d.η₀ + 1) R₁) 0 + 1 with hY₀def
  have hY₀pos : 0 < Y₀ := by
    rw [hY₀def]
    have h := le_max_right (max (d.η₀ + 1) R₁) (0:ℝ)
    linarith
  have hY₀η : d.η₀ < Y₀ := by
    rw [hY₀def]
    have h1 : d.η₀ + 1 ≤ max (d.η₀ + 1) R₁ := le_max_left _ _
    have h2 : max (d.η₀ + 1) R₁ ≤ max (max (d.η₀ + 1) R₁) 0 := le_max_left _ _
    linarith
  have hY₀R : R₁ < Y₀ := by
    rw [hY₀def]
    have h1 : R₁ ≤ max (d.η₀ + 1) R₁ := le_max_right _ _
    have h2 : max (d.η₀ + 1) R₁ ≤ max (max (d.η₀ + 1) R₁) 0 := le_max_left _ _
    linarith
  set ψ : ℂ → ℂ := fun u => (d.E (-u) - (-u)) - cl with hψdef
  have him_neg : ∀ z : ℂ, (-z).im = -z.im := fun z => by simp
  have hψper : ∀ w : ℂ, Y₀ ≤ w.im → ψ (w + 1) = ψ w := by
    intro w hw
    have hmem : d.η₀ < |(-w - 1).im| := by
      have h1 : (-w - 1).im = -w.im := by simp
      rw [h1, abs_of_neg (by linarith)]
      linarith
    have heq := (Work.Horn.isTEquivariantOn_E_abs_im_gt d).2 (-w - 1) hmem
    have h2 : -w - 1 + 1 = -w := by ring
    rw [h2] at heq
    simp only [hψdef]
    rw [heq]
    ring
  have hψhol : DifferentiableOn ℂ ψ {w : ℂ | Y₀ ≤ w.im} := by
    intro u hu
    have hu' : Y₀ ≤ u.im := hu
    have hmem : d.η₀ < |(-u).im| := by
      have h1 : (-u).im = -u.im := him_neg u
      have h2 : -u.im < 0 := by linarith
      rw [h1, abs_of_neg h2]
      linarith
    have hset : {w : ℂ | d.η₀ < |w.im|} ∈ 𝓝 (-u) :=
      (isOpen_lt continuous_const (continuous_abs.comp Complex.continuous_im)).mem_nhds hmem
    have h1 : DifferentiableAt ℂ (fun u : ℂ => d.E (-u)) u :=
      (((Work.Horn.differentiableOn_E_abs_im_gt d) (-u) hmem).differentiableAt hset).comp u
        (by fun_prop)
    have h2 : DifferentiableAt ℂ (fun u : ℂ => (d.E (-u) - (-u)) - cl) u :=
      (h1.sub (by fun_prop)).sub_const cl
    exact h2.differentiableWithinAt
  have hψbd : ∀ w : ℂ, Y₀ ≤ w.im → ‖ψ w‖ ≤ 1 := by
    intro w hw
    have h1 : (-w).im < -R₁ := by
      rw [him_neg]; linarith
    have h3 := hR₁ (-w) h1
    simp only [hψdef]
    rw [show (d.E (-w) - -w) - cl = (d.E (-w) - -w - cl) by ring]
    exact le_of_lt (by simpa [dist_eq_norm] using h3)
  obtain ⟨c, M, hM⟩ := end_fourier hψper hψhol hψbd
  have hderiv_eq : deriv (fun u : ℂ => (d.E u - u) - (cl + c)) = deriv (fun u : ℂ => d.E u - u) := by
    funext z
    rw [show (fun u : ℂ => (d.E u - u) - (cl + c))
        = (fun u : ℂ => (d.E u - u) + (-(cl + c))) by funext u; ring]
    exact deriv_add_const _
  have hball_sub : ∀ w : ℂ, w.im < -(Y₀ + 2) → Metric.ball w 1 ⊆ {v : ℂ | d.η₀ < |v.im|} := by
    intro w hw v hv
    rw [Metric.mem_ball, dist_eq_norm] at hv
    have h4 : |v.im - w.im| ≤ ‖v - w‖ := by
      have h := Complex.abs_im_le_norm (v - w)
      simpa [Complex.sub_im] using h
    have h5 : v.im < w.im + 1 := by
      have h6 : v.im - w.im < 1 := lt_of_le_of_lt (le_abs_self _) (lt_of_le_of_lt h4 hv)
      linarith
    have h6 : v.im < 0 := by linarith
    show d.η₀ < |v.im|
    have h7 : |v.im| = -v.im := abs_of_neg h6
    rw [h7]
    linarith
  have hpoint : ∀ w : ℂ, w.im < -(Y₀ + 2) →
      ‖deriv (fun u : ℂ => (d.E u - u) - (cl + c)) w‖
        ≤ 2 * (|M| * Real.exp (-2 * Real.pi * (-w.im - 3/2 - Y₀))) := by
    intro w hw
    have hball1 := hball_sub w hw
    have hd1 : DifferentiableOn ℂ (fun u : ℂ => (d.E u - u) - (cl + c)) (Metric.ball w 1) := by
      intro v hv
      have hmem := hball1 hv
      have hset : {z : ℂ | d.η₀ < |z.im|} ∈ 𝓝 v :=
        (isOpen_lt continuous_const (continuous_abs.comp Complex.continuous_im)).mem_nhds hmem
      have h1 : DifferentiableAt ℂ (fun u : ℂ => d.E u) v :=
        ((Work.Horn.differentiableOn_E_abs_im_gt d) v hmem).differentiableAt hset
      exact ((h1.sub differentiableAt_id).sub_const _).differentiableWithinAt
    have hdd : DiffContOnCl ℂ (fun u : ℂ => (d.E u - u) - (cl + c)) (Metric.ball w (1/2)) :=
      hd1.diffContOnCl_ball (Metric.closedBall_subset_ball (by norm_num))
    have hsph : ∀ v ∈ Metric.sphere w (1/2),
        ‖(fun u : ℂ => (d.E u - u) - (cl + c)) v‖
          ≤ |M| * Real.exp (-2 * Real.pi * (-w.im - 3/2 - Y₀)) := by
      intro v hv
      have hv' : ‖v - w‖ = 1/2 := by
        rw [← dist_eq_norm]; exact Metric.mem_sphere.mp hv
      have h4 : |v.im - w.im| ≤ ‖v - w‖ := by
        have h := Complex.abs_im_le_norm (v - w)
        simpa [Complex.sub_im] using h
      have h5 : v.im ≤ w.im + 1/2 := by
        have h6 : |v.im - w.im| ≤ 1/2 := by rw [← hv']; exact h4
        have h7 : v.im - w.im ≤ 1/2 := le_trans (le_abs_self _) h6
        linarith
      have h6 : Y₀ + 1 ≤ (-v).im := by
        rw [him_neg]; linarith
      have h8 := hM (-v) h6
      have hid : (fun u : ℂ => (d.E u - u) - (cl + c)) v = ψ (-v) - c := by
        simp only [hψdef]
        ring
      rw [hid]
      refine le_trans h8 ?_
      have h9 : Real.exp (-2 * Real.pi * ((-v).im - Y₀ - 1))
          ≤ Real.exp (-2 * Real.pi * (-w.im - 3/2 - Y₀)) := by
        refine Real.exp_le_exp.mpr ?_
        have h10 : v.im ≤ w.im + 1/2 := h5
        rw [him_neg]
        nlinarith [Real.pi_pos]
      calc M * Real.exp (-2 * Real.pi * ((-v).im - Y₀ - 1))
          ≤ |M| * Real.exp (-2 * Real.pi * ((-v).im - Y₀ - 1)) :=
            mul_le_mul_of_nonneg_right (le_abs_self M) (Real.exp_pos _).le
        _ ≤ |M| * Real.exp (-2 * Real.pi * (-w.im - 3/2 - Y₀)) :=
            mul_le_mul_of_nonneg_left h9 (abs_nonneg M)
    have hc := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (c := w) (R := 1/2)
      (C := |M| * Real.exp (-2 * Real.pi * (-w.im - 3/2 - Y₀)))
      (f := fun u : ℂ => (d.E u - u) - (cl + c)) (by norm_num) hdd hsph
    calc ‖deriv (fun u : ℂ => (d.E u - u) - (cl + c)) w‖
        ≤ |M| * Real.exp (-2 * Real.pi * (-w.im - 3/2 - Y₀)) / (1/2) := hc
      _ = 2 * (|M| * Real.exp (-2 * Real.pi * (-w.im - 3/2 - Y₀))) := by ring
  have hexp0 : Tendsto (fun b : ℝ => 2 * (|M| * Real.exp (-2 * Real.pi * (-b - 3/2 - Y₀))))
      atBot (𝓝 0) := by
    have h1 : Tendsto (fun b : ℝ => -2 * Real.pi * (-b - 3/2 - Y₀)) atBot atBot := by
      rw [Filter.tendsto_atBot]
      intro a
      filter_upwards [eventually_le_atBot (a / (2 * Real.pi) - 3/2 - Y₀)] with b hb
      have h2pi : (0:ℝ) < 2 * Real.pi := by positivity
      have h : -2 * Real.pi * (-b - 3/2 - Y₀) = 2 * Real.pi * (b + 3/2 + Y₀) := by ring
      rw [h]
      have h3 : b * (2 * Real.pi) ≤ (a / (2 * Real.pi) - 3/2 - Y₀) * (2 * Real.pi) :=
        mul_le_mul_of_nonneg_right hb h2pi.le
      have h4 : (a / (2 * Real.pi) - 3/2 - Y₀) * (2 * Real.pi)
          = a - (3/2 + Y₀) * (2 * Real.pi) := by
        field_simp
        ring
      nlinarith [h3, h4, h2pi]
    have h2 : Tendsto (fun b : ℝ => Real.exp (-2 * Real.pi * (-b - 3/2 - Y₀))) atBot (𝓝 0) :=
      Real.tendsto_exp_atBot.comp h1
    have h3 := h2.const_mul (2 * |M|)
    simpa [mul_assoc] using h3
  have hev : ∀ᶠ w : ℂ in comap Complex.im atBot,
      w.im < -(Y₀ + 2) ∧ 2 * (|M| * Real.exp (-2 * Real.pi * (-w.im - 3/2 - Y₀))) ≤ ε := by
    have h1 : ∀ᶠ w : ℂ in comap Complex.im atBot, w.im < -(Y₀ + 2) := by
      rw [Filter.eventually_comap, Filter.eventually_atBot]
      exact ⟨-(Y₀ + 3), fun y hy w hw => by rw [hw]; linarith⟩
    have h2 : ∀ᶠ w : ℂ in comap Complex.im atBot,
        2 * (|M| * Real.exp (-2 * Real.pi * (-w.im - 3/2 - Y₀))) < ε := by
      have hcomp : Tendsto
          (fun w : ℂ => 2 * (|M| * Real.exp (-2 * Real.pi * (-w.im - 3/2 - Y₀))))
          (comap Complex.im atBot) (𝓝 0) := by
        have h3 := hexp0.comp (Filter.tendsto_comap (f := Complex.im) (x := Filter.atBot))
        exact h3
      have h4 := Metric.tendsto_nhds.mp hcomp ε hε
      filter_upwards [h4] with w hw
      have h5 : |2 * (|M| * Real.exp (-2 * Real.pi * (-w.im - 3/2 - Y₀)))| < ε := by
        simpa [Real.dist_eq] using hw
      exact lt_of_le_of_lt (le_abs_self _) h5
    filter_upwards [h1, h2] with w h1w h2w
    exact ⟨h1w, le_of_lt h2w⟩
  obtain ⟨Yb, hYb⟩ := Filter.eventually_atBot.mp (Filter.eventually_comap.mp hev)
  refine ⟨max (-Yb) 0, fun w hw => ?_⟩
  have hle : w.im ≤ Yb := by
    have h1 : -(max (-Yb) 0) ≤ Yb := by
      have h2 : -Yb ≤ max (-Yb) 0 := le_max_left _ _
      linarith
    linarith
  obtain ⟨h1, h2⟩ := hYb w.im hle w rfl
  rw [← hderiv_eq]
  exact le_trans (hpoint w h1) h2

/-- **The perturbed downward inverse branch on a deep half-plane.** -/
theorem perturbed_branch_lower {g₀ : ℂ → ℂ} {D : Set ℂ} (d : MandelDim.ParabData g₀ D)
    (hd : MandelDim.HornData d) {β : ℂ} {cl₀ : ℂ} {κ : ℝ} (hκ : 0 < κ)
    (hβ : κ ≤ Complex.im cl₀ - Complex.im β) {y₁ : ℝ} {H₀ ρ₀ : ℂ → ℂ} {y₀' : ℝ} (hy : y₁ ≤ y₀')
    (hH₀d : DifferentiableOn ℂ H₀ {w : ℂ | Complex.im w < -(y₀' : ℝ)})
    (hH₀ : ∀ w : ℂ, Complex.im w < -(y₀' : ℝ) → Complex.im (H₀ w) < -(y₁ : ℝ) ∧
      H₀ w ∈ hd.Bl ∧ d.E (H₀ w) - β = w)
    (hinc₀ : ∀ w : ℂ, Complex.im w < -(y₀' : ℝ) → H₀ w = w + (β - cl₀) + ρ₀ w)
    (hρ₀d : DifferentiableOn ℂ ρ₀ {w : ℂ | Complex.im w < -(y₀' : ℝ)})
    (hρ₀bd : ∀ w : ℂ, Complex.im w < -(y₀' : ℝ) → ‖ρ₀ w‖ ≤ κ / 4)
    (hdrift₀ : ∀ w : ℂ, Complex.im w < -(y₀' : ℝ) → Complex.im (H₀ w - w) ≤ -(κ / 2))
    {R : ℂ → ℂ} {DR : Set ℂ} (hDRo : IsOpen DR) (hTeq : MandelDim.IsTEquivariantOn R DR)
    (hRhol : DifferentiableOn ℂ R DR) (hDRmem : ∀ w : ℂ, Complex.im w < -(y₁ : ℝ) → w ∈ DR)
    {δ : ℝ} (hδ : 0 < δ) (hδκ : δ ≤ κ / 16)
    (hclose : ∀ w : ℂ, Complex.im w < -(y₁ : ℝ) → ‖R w - d.E w‖ ≤ δ)
    (hclose' : ∀ w : ℂ, Complex.im w < -(y₁ + 1) → ‖deriv (fun u => R u - d.E u) w‖ ≤ δ) :
    ∃ (H : ℂ → ℂ) (ρ : ℂ → ℂ) (y'' : ℝ) (c : ℂ), y₀' ≤ y'' ∧
      DifferentiableOn ℂ H {w : ℂ | Complex.im w < -(y'' : ℝ)} ∧
      (∀ w : ℂ, Complex.im w < -(y'' : ℝ) → Complex.im (H w) < -(y₁ : ℝ) ∧ H w ∈ DR ∧
        R (H w) - β = w ∧ H w = w + (β - cl₀) + ρ w) ∧
      DifferentiableOn ℂ ρ {w : ℂ | Complex.im w < -(y'' : ℝ)} ∧
      (∀ w : ℂ, Complex.im w < -(y'' : ℝ) → ρ (w + 1) = ρ w) ∧
      (∀ w : ℂ, Complex.im w < -(y'' : ℝ) → ‖ρ w‖ ≤ κ / 2) ∧
      (∀ w : ℂ, Complex.im w < -(y'' : ℝ) → Complex.im (H w - w) ≤ -(κ / 4)) ∧
      Set.InjOn H {w : ℂ | Complex.im w < -(y'' : ℝ)} ∧
      Filter.Tendsto ρ (Filter.comap Complex.im Filter.atBot) (nhds c) := by
  -- 1. the depth at which the perturbation `R - id` carries the near-translation structure
  obtain ⟨cl, hcl⟩ := Work.Horn.MandelDim.ParabData.E_lower_iff d
  obtain ⟨R₁, hR₁⟩ := hcl 1 zero_lt_one
  have hΨbdd : ∀ w : ℂ, w.im < -R₁ → ‖d.E w - w‖ ≤ ‖cl‖ + 1 := by
    intro w hw
    have h := hR₁ w hw
    have h2 : ‖d.E w - w - cl‖ < 1 := by simpa [dist_eq_norm] using h
    calc ‖d.E w - w‖ = ‖(d.E w - w - cl) + cl‖ := by ring_nf
      _ ≤ ‖d.E w - w - cl‖ + ‖cl‖ := norm_add_le _ _
      _ ≤ 1 + ‖cl‖ := by linarith [le_of_lt h2]
      _ = ‖cl‖ + 1 := by ring
  set Yg : ℝ := max (max R₁ y₁) (d.η₀ + 1) + 1 with hYgdef
  have hYgy₁ : y₁ < Yg := by
    rw [hYgdef]
    have h1 : y₁ ≤ max R₁ y₁ := le_max_right _ _
    have h2 : max R₁ y₁ ≤ max (max R₁ y₁) (d.η₀ + 1) := le_max_left _ _
    linarith
  have hYgR₁ : R₁ < Yg := by
    rw [hYgdef]
    have h1 : R₁ ≤ max R₁ y₁ := le_max_left _ _
    have h2 : max R₁ y₁ ≤ max (max R₁ y₁) (d.η₀ + 1) := le_max_left _ _
    linarith
  have hYgmem : ∀ w : ℂ, w.im < -Yg → w ∈ DR := fun w hw => hDRmem w (by linarith)
  -- 2. the near-translation inverse
  have hG_diff : ∀ x : ℂ, x.im < -Yg → DifferentiableAt ℂ (fun x : ℂ => R x - x) x := by
    intro x hx
    have hmem := hYgmem x hx
    have h1 : DifferentiableAt ℂ R x := (hRhol x hmem).differentiableAt (hDRo.mem_nhds hmem)
    exact h1.sub differentiableAt_id
  have hG_per : ∀ x : ℂ, x.im < -Yg → (fun x : ℂ => R x - x) (x + 1) = (fun x : ℂ => R x - x) x := by
    intro x hx
    have hmem := hYgmem x hx
    have hmem1 := hYgmem (x + 1) (by simpa using hx)
    have h1 : R (x + 1) = R x + 1 := hTeq.2 x hmem
    simp only
    rw [h1]
    ring
  have hG_bd : ∀ x : ℂ, x.im < -Yg → ‖(fun x : ℂ => R x - x) x‖ ≤ ‖cl‖ + 1 + δ := by
    intro x hx
    have h1 : x.im < -(y₁ : ℝ) := by linarith
    have h2 := hΨbdd x (by linarith)
    have h3 := hclose x h1
    calc ‖R x - x‖ = ‖(R x - d.E x) + (d.E x - x)‖ := by ring_nf
      _ ≤ ‖R x - d.E x‖ + ‖d.E x - x‖ := norm_add_le _ _
      _ ≤ δ + (‖cl‖ + 1) := add_le_add h3 h2
      _ = ‖cl‖ + 1 + δ := by ring
  obtain ⟨X, YA, hYAYg, hXdiff, hXprop⟩ :=
    near_translation_inverse (G := fun x : ℂ => R x - x) (Y := Yg) (δ := ‖cl‖ + 1 + δ)
      hG_diff hG_per hG_bd
  have hXper : ∀ w : ℂ, w.im < -YA → X (w + 1) = X w + 1 := fun w hw => (hXprop w hw).2.1
  have hXdeep : ∀ w : ℂ, w.im < -YA → (X w).im < -Yg := fun w hw => (hXprop w hw).2.2.1
  have hXbd : ∀ w : ℂ, w.im < -YA → ‖X w - w‖ ≤ ‖cl‖ + 1 + δ := fun w hw => (hXprop w hw).2.2.2
  have hXeq : ∀ w : ℂ, w.im < -YA → R (X w) = w := by
    intro w hw
    have h := (hXprop w hw).1
    have h2 : X w + (R (X w) - X w) = R (X w) := by ring
    rw [h2] at h
    exact h
  -- 3. the flatness of `E - id`, and the comparison with the model branch
  obtain ⟨Ylip₀, hYlip₀⟩ := deriv_E_sub_id_lower d (1/2) (by norm_num)
  set Ylip : ℝ := max (max Ylip₀ (d.η₀ + 1)) 0 with hYlipdef
  have hYlipη : d.η₀ < Ylip := by
    rw [hYlipdef]
    have h1 : d.η₀ + 1 ≤ max Ylip₀ (d.η₀ + 1) := le_max_right _ _
    have h2 : max Ylip₀ (d.η₀ + 1) ≤ max (max Ylip₀ (d.η₀ + 1)) 0 := le_max_left _ _
    linarith
  have hYlip0 : 0 ≤ Ylip := by
    rw [hYlipdef]
    exact le_max_right _ _
  have hYlip : ∀ w : ℂ, w.im < -Ylip → ‖deriv (fun u : ℂ => d.E u - u) w‖ ≤ 1/2 :=
    fun w hw => hYlip₀ w (by
      have h1 : Ylip₀ ≤ max Ylip₀ (d.η₀ + 1) := le_max_left _ _
      have h2 : max Ylip₀ (d.η₀ + 1) ≤ Ylip := le_max_left _ _
      linarith)
  set δ' : ℝ := ‖cl‖ + 1 + δ with hδ'def
  have hδ'0 : 0 ≤ δ' := by rw [hδ'def]; positivity
  -- 4. the branch `H` and its properties on a deep half-plane
  set H : ℂ → ℂ := fun w => X (w + β) with hHdef
  have hYAβ : ∀ w : ℂ, w.im < -(YA + β.im) → (w + β).im < -YA := by
    intro w hw
    have h1 : (w + β).im = w.im + β.im := by simp
    rw [h1]; linarith
  set Yfin : ℝ := max (max (max y₀' (YA + β.im)) (max (Ylip + κ/2) (Ylip + β.im + δ'))) Yg + 1
    with hYfindef
  have hYfin_y₀ : y₀' ≤ Yfin := by
    rw [hYfindef]
    have h1 : y₀' ≤ max y₀' (YA + β.im) := le_max_left _ _
    have h2 : max y₀' (YA + β.im)
        ≤ max (max y₀' (YA + β.im)) (max (Ylip + κ/2) (Ylip + β.im + δ')) := le_max_left _ _
    have h3 := le_max_left (max (max y₀' (YA + β.im)) (max (Ylip + κ/2) (Ylip + β.im + δ'))) Yg
    linarith
  have hYA_le : YA + β.im ≤ Yfin := by
    rw [hYfindef]
    have h1 : YA + β.im ≤ max y₀' (YA + β.im) := le_max_right _ _
    have h2 : max y₀' (YA + β.im)
        ≤ max (max y₀' (YA + β.im)) (max (Ylip + κ/2) (Ylip + β.im + δ')) := le_max_left _ _
    have h3 := le_max_left (max (max y₀' (YA + β.im)) (max (Ylip + κ/2) (Ylip + β.im + δ'))) Yg
    linarith
  have hLip_le : Ylip + κ/2 ≤ Yfin := by
    rw [hYfindef]
    have h1 : Ylip + κ/2 ≤ max (Ylip + κ/2) (Ylip + β.im + δ') := le_max_left _ _
    have h2 : max (Ylip + κ/2) (Ylip + β.im + δ')
        ≤ max (max y₀' (YA + β.im)) (max (Ylip + κ/2) (Ylip + β.im + δ')) := le_max_right _ _
    have h3 := le_max_left (max (max y₀' (YA + β.im)) (max (Ylip + κ/2) (Ylip + β.im + δ'))) Yg
    linarith
  have hLip_le2 : Ylip + β.im + δ' ≤ Yfin := by
    rw [hYfindef]
    have h1 : Ylip + β.im + δ' ≤ max (Ylip + κ/2) (Ylip + β.im + δ') := le_max_right _ _
    have h2 : max (Ylip + κ/2) (Ylip + β.im + δ')
        ≤ max (max y₀' (YA + β.im)) (max (Ylip + κ/2) (Ylip + β.im + δ')) := le_max_right _ _
    have h3 := le_max_left (max (max y₀' (YA + β.im)) (max (Ylip + κ/2) (Ylip + β.im + δ'))) Yg
    linarith
  have hHdeep : ∀ w : ℂ, w.im < -Yfin → (H w).im < -Yg := by
    intro w hw
    have hw' : w.im < -Yfin := hw
    have h1 : (w + β).im < -YA := hYAβ w (by linarith [hYA_le, hw'])
    have h2 := hXdeep (w + β) h1
    simpa [hHdef] using h2
  have hHdiff : DifferentiableOn ℂ H {w : ℂ | w.im < -Yfin} := by
    intro w hw
    have hw' : w.im < -Yfin := hw
    have h1 : (w + β).im < -YA := hYAβ w (by linarith [hYA_le, hw'])
    have h2 : DifferentiableAt ℂ X (w + β) := (hXdiff (w + β) h1).differentiableAt
      ((isOpen_lt continuous_im continuous_const).mem_nhds h1)
    have h3 : DifferentiableAt ℂ (fun w : ℂ => X (w + β)) w := h2.comp w (by fun_prop)
    simpa [hHdef] using h3.differentiableWithinAt
  have hReq : ∀ w : ℂ, w.im < -Yfin → R (H w) - β = w := by
    intro w hw
    have hw' : w.im < -Yfin := hw
    have h1 : (w + β).im < -YA := hYAβ w (by linarith [hYA_le, hw'])
    have h2 : R (X (w + β)) = w + β := hXeq (w + β) h1
    have h3 : R (H w) = w + β := by simpa [hHdef] using h2
    rw [h3]; ring
  have hHper : ∀ w : ℂ, w.im < -Yfin → H (w + 1) = H w + 1 := by
    intro w hw
    have hw' : w.im < -Yfin := hw
    have h1 : (w + β).im < -YA := hYAβ w (by linarith [hYA_le, hw'])
    have h5 := hXper (w + β) h1
    show X (w + 1 + β) = X (w + β) + 1
    rw [show w + 1 + β = (w + β) + 1 by ring]
    exact h5
  have hHbd : ∀ w : ℂ, w.im < -Yfin → ‖H w - w - β‖ ≤ δ' := by
    intro w hw
    have hw' : w.im < -Yfin := hw
    have h1 : (w + β).im < -YA := hYAβ w (by linarith [hYA_le, hw'])
    have h2 := hXbd (w + β) h1
    have h3 : X (w + β) - (w + β) = X (w + β) - w - β := by ring
    rw [hδ'def, ← h3]
    simpa [hHdef] using h2
  -- the comparison with `H₀`
  have hcmp : ∀ w : ℂ, w.im < -Yfin → ‖H w - H₀ w‖ ≤ 2 * δ := by
    intro w hw
    have hw' : w.im < -Yfin := hw
    have hw₀ : w.im < -(y₀' : ℝ) := by linarith [hYfin_y₀]
    obtain ⟨hH₀im, hH₀Bl, hH₀eq⟩ := hH₀ w hw₀
    have hHim : (H w).im < -(y₁ : ℝ) := by
      have h1 := hHdeep w hw'
      have h2 : y₁ < Yg := hYgy₁
      linarith
    have hHb : ‖H w - w - β‖ ≤ δ' := hHbd w hw'
    have hA : (H₀ w).im < -Ylip := by
      have h1 := hdrift₀ w hw₀
      have h2 : (H₀ w - w).im = (H₀ w).im - w.im := by rw [Complex.sub_im]
      rw [h2] at h1
      linarith [hLip_le, hw']
    have hB : (H w).im < -Ylip := by
      have h1 : (H w - w - β).im = (H w).im - w.im - β.im := by
        rw [Complex.sub_im, Complex.sub_im]
      have h2 : (H w - w - β).im ≤ ‖H w - w - β‖ := by
        have h3 := Complex.abs_im_le_norm (H w - w - β)
        linarith [le_abs_self (H w - w - β).im]
      rw [h1] at h2
      linarith [hLip_le2, hw', hHb, h2]
    have hconv : Convex ℝ {z : ℂ | z.im < -Ylip} := convex_halfSpace_im_lt (-Ylip)
    have hdiffLip : DifferentiableOn ℂ (fun u : ℂ => d.E u - u) {z : ℂ | z.im < -Ylip} := by
      intro z hz
      have hz' : z.im < -Ylip := hz
      have hz0 : z.im < 0 := by linarith [hYlip0]
      have hmem : d.η₀ < |z.im| := by
        rw [abs_of_neg hz0]
        linarith [hYlipη, hz']
      have hset : {w : ℂ | d.η₀ < |w.im|} ∈ 𝓝 z :=
        (isOpen_lt continuous_const (continuous_abs.comp Complex.continuous_im)).mem_nhds hmem
      have h1 : DifferentiableAt ℂ (fun u : ℂ => d.E u) z :=
        ((Work.Horn.differentiableOn_E_abs_im_gt d) z hmem).differentiableAt hset
      exact (h1.sub differentiableAt_id).differentiableWithinAt
    have hmvt := Convex.norm_image_sub_le_of_norm_deriv_le (f := fun u : ℂ => d.E u - u)
      (s := {z : ℂ | z.im < -Ylip}) (C := 1/2)
      (fun z hz => (hdiffLip z hz).differentiableAt
        ((isOpen_lt continuous_im continuous_const).mem_nhds hz))
      (fun z hz => hYlip z hz) hconv hA hB
    have hmvt' : ‖(d.E (H₀ w) - H₀ w) - (d.E (H w) - H w)‖ ≤ 1/2 * ‖H w - H₀ w‖ := by
      rwa [norm_sub_rev] at hmvt
    have hid : (d.E (H₀ w) - H₀ w) - (R (H w) - H w) = H w - H₀ w := by
      have h1 : d.E (H₀ w) = w + β := by linear_combination hH₀eq
      have h2 : R (H w) = w + β := by linear_combination hReq w hw'
      rw [h1, h2]; ring
    have hsplit : R (H w) - H w = (d.E (H w) - H w) + (R (H w) - d.E (H w)) := by ring
    rw [hsplit] at hid
    have hclose_w : ‖R (H w) - d.E (H w)‖ ≤ δ := hclose (H w) hHim
    have h5 : ‖H₀ w - H w‖ = ‖H w - H₀ w‖ := norm_sub_rev _ _
    have hkey : ‖H w - H₀ w‖ ≤ 1/2 * ‖H₀ w - H w‖ + δ := by
      have h2 : H w - H₀ w
          = ((d.E (H₀ w) - H₀ w) - (d.E (H w) - H w)) - (R (H w) - d.E (H w)) := by
        rw [← hid]; ring
      have h3 : ‖((d.E (H₀ w) - H₀ w) - (d.E (H w) - H w)) - (R (H w) - d.E (H w))‖
          ≤ 1/2 * ‖H w - H₀ w‖ + δ := by
        calc ‖((d.E (H₀ w) - H₀ w) - (d.E (H w) - H w)) - (R (H w) - d.E (H w))‖
            ≤ ‖(d.E (H₀ w) - H₀ w) - (d.E (H w) - H w)‖ + ‖R (H w) - d.E (H w)‖ :=
              norm_sub_le _ _
          _ ≤ 1/2 * ‖H w - H₀ w‖ + δ := add_le_add hmvt' hclose_w
      rw [h2, h5]
      exact h3
    rw [h5] at hkey
    linarith [hkey]
  -- 5. the conclusion
  set ρ : ℂ → ℂ := fun w => H w - w - (β - cl₀) with hρdef
  have hρper : ∀ w : ℂ, w.im < -Yfin → ρ (w + 1) = ρ w := by
    intro w hw
    have hw' : w.im < -Yfin := hw
    have h1 := hHper w hw'
    show H (w + 1) - (w + 1) - (β - cl₀) = H w - w - (β - cl₀)
    rw [h1]; ring
  have hρbd : ∀ w : ℂ, w.im < -Yfin → ‖ρ w‖ ≤ κ / 2 := by
    intro w hw
    have hw' : w.im < -Yfin := hw
    have hw₀ : w.im < -(y₀' : ℝ) := by linarith [hYfin_y₀]
    have h1 : ρ w = ρ₀ w + (H w - H₀ w) := by
      have h2 := hinc₀ w hw₀
      show H w - w - (β - cl₀) = ρ₀ w + (H w - H₀ w)
      rw [h2]; ring
    rw [h1]
    have h3 := hρ₀bd w hw₀
    have h4 := hcmp w hw'
    have h5 : 2 * δ ≤ κ / 8 := by linarith [hδκ]
    calc ‖ρ₀ w + (H w - H₀ w)‖ ≤ ‖ρ₀ w‖ + ‖H w - H₀ w‖ := norm_add_le _ _
      _ ≤ κ/4 + 2*δ := add_le_add h3 h4
      _ ≤ κ/4 + κ/8 := by linarith
      _ ≤ κ/2 := by linarith [hκ]
  have hρdrift : ∀ w : ℂ, w.im < -Yfin → (H w - w).im ≤ -(κ / 4) := by
    intro w hw
    have hw' : w.im < -Yfin := hw
    have hw₀ : w.im < -(y₀' : ℝ) := by linarith [hYfin_y₀]
    have h1 := hdrift₀ w hw₀
    have h2 := hcmp w hw'
    have h3 : (H w - H₀ w).im ≤ ‖H w - H₀ w‖ := by
      have h4 := Complex.abs_im_le_norm (H w - H₀ w)
      linarith [le_abs_self (H w - H₀ w).im]
    have h4 : (H w - w).im = (H₀ w - w).im + (H w - H₀ w).im := by
      rw [show H w - w = (H₀ w - w) + (H w - H₀ w) by ring, Complex.add_im]
    rw [h4]
    have h6 : 2 * δ ≤ κ/4 := by linarith [hδκ]
    linarith
  have hinj : Set.InjOn H {w : ℂ | w.im < -Yfin} := by
    intro a ha b hb hab
    have ha' : a.im < -Yfin := ha
    have hb' : b.im < -Yfin := hb
    have h1 := hReq a ha'
    have h2 := hReq b hb'
    rw [hab] at h1
    rw [h1] at h2
    exact h2
  have hρhol : DifferentiableOn ℂ ρ {w : ℂ | w.im < -Yfin} := by
    intro w hw
    have h1 : DifferentiableAt ℂ H w := (hHdiff w hw).differentiableAt
      ((isOpen_lt continuous_im continuous_const).mem_nhds hw)
    have h2 : DifferentiableAt ℂ ρ w := by
      have h3 : DifferentiableAt ℂ (fun w : ℂ => H w - w - (β - cl₀)) w :=
        (h1.sub differentiableAt_id).sub_const _
      simpa [hρdef] using h3
    exact h2.differentiableWithinAt
  obtain ⟨c, hc⟩ := tendsto_atBot_of_periodic_bounded (φ := ρ) (Y := Yfin) (B := κ/2)
    (fun w hw => (hρhol w hw).differentiableAt
      ((isOpen_lt continuous_im continuous_const).mem_nhds hw)) hρper hρbd
  refine ⟨H, ρ, Yfin, c, hYfin_y₀, hHdiff, ?_, hρhol, hρper, hρbd, hρdrift, hinj, hc⟩
  intro w hw
  have hw' : w.im < -Yfin := hw
  refine ⟨?_, ?_, hReq w hw', ?_⟩
  · have h1 := hHdeep w hw'
    have h2 : y₁ < Yg := hYgy₁
    linarith
  · exact hDRmem (H w) (by
      have h1 := hHdeep w hw'
      have h2 : y₁ < Yg := hYgy₁
      linarith)
  · show H w = w + (β - cl₀) + ρ w
    simp only [hρdef]
    ring

end

end Work.L62
