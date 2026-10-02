import Mathlib
import Submission.Commons.NumberTheory.Linnik.completedL_zeroCount
import Submission.Commons.NumberTheory.Linnik.completedL_growth_circle
import Submission.Commons.NumberTheory.Linnik.goodRadius_geometric
import Submission.Commons.NumberTheory.Linnik.partialFraction_conv
import Submission.Commons.NumberTheory.Linnik.partialFraction_tail
import Submission.Commons.NumberTheory.Linnik.logDeriv_circle_residue
import Submission.Commons.NumberTheory.Linnik.ell_pow_div_self_tendsto_zero

open Complex DirichletCharacter Metric Filter Function Set MeromorphicOn Topology
open scoped Real Topology BigOperators

set_option autoImplicit false
set_option maxHeartbeats 0
noncomputable section

namespace Commons.NumberTheory.Linnik

def L_N (N : ℕ) (A : ℝ) : ℝ := Real.log (A + 2) + Real.log (N : ℝ) + 2

lemma pf_L_ge_two {N : ℕ} [NeZero N] {A : ℝ} (hA : 0 ≤ A) : 2 ≤ L_N N A := by
  have h1 : 0 ≤ Real.log (A + 2) := by
    refine Real.log_nonneg ?_
    linarith only [hA]
  dsimp [L_N]
  have hN : 0 ≤ Real.log (N : ℝ) := logN_nonneg (N := N)
  linarith only [h1, hN]

lemma pf_L_pos {N : ℕ} [NeZero N] {A : ℝ} (hA : 0 ≤ A) : 0 < L_N N A := by
  linarith [pf_L_ge_two (N := N) hA]

lemma pf_L_mono {N : ℕ} {A B : ℝ} (hA : 0 ≤ A) (h : A ≤ B) : L_N N A ≤ L_N N B := by
  have hp1 : 0 < A + 2 := by linarith only [hA]
  have hp2 : 0 < B + 2 := by linarith only [hA, h]
  have hle : A + 2 ≤ B + 2 := by linarith only [h]
  have hlog : Real.log (A + 2) ≤ Real.log (B + 2) := Real.log_le_log hp1 hle
  dsimp [L_N]
  linarith only [hlog]

lemma pf_log_L_le_L {N : ℕ} [NeZero N] {A : ℝ} (hA : 0 ≤ A) : Real.log (L_N N A) ≤ L_N N A := by
  have h1 : 1 ≤ L_N N A := by linarith [pf_L_ge_two (N := N) hA]
  exact Real.log_le_self (by linarith only [h1])

/-- For 1 ≤ A, L_N(2A) ≤ 2·L_N(A). -/
lemma pf_L_two_mul_le {N : ℕ} [NeZero N] {A : ℝ} (hA : 1 ≤ A) : L_N N (2 * A) ≤ 2 * L_N N A := by
  have hA2 : 0 ≤ A := by linarith only [hA]
  have h₁ : 0 < A + 1 := by linarith only [hA]
  have h₂ : 0 < 2 := by norm_num
  have h₁₂ : (A + 1 : ℝ) ≠ 0 := by linarith only [hA]
  have hlog : Real.log (2 * A + 2) ≤ Real.log (A + 2) + Real.log 2 := by
    calc
      Real.log (2 * A + 2) = Real.log ((A + 1) * 2) := by congr 1; ring
      _ = Real.log (A + 1) + Real.log 2 := by rw [Real.log_mul h₁₂ (by norm_num : (2 : ℝ) ≠ 0)]
      _ ≤ Real.log (A + 2) + Real.log 2 := by
        have hlogle : Real.log (A + 1) ≤ Real.log (A + 2) := Real.log_le_log h₁ (by linarith only [])
        linarith only [hlogle]
  have hlog2 : Real.log 2 ≤ 1 := by
    have hlt := Real.log_two_lt_d9
    norm_num at hlt
    linarith only [hlt]
  have h12 : 1 ≤ Real.log (A + 2) := by
    have he : Real.exp 1 ≤ A + 2 := by
      have h3 : Real.exp 1 ≤ 3 := le_of_lt Real.exp_one_lt_three
      linarith only [hA, h3]
    have h := Real.log_le_log (Real.exp_pos 1) he
    rwa [Real.log_exp] at h
  dsimp [L_N]
  have hN : 0 ≤ Real.log (N : ℝ) := logN_nonneg (N := N)
  linarith only [hlog, hlog2, h12, hN]

/-- (L_N A)^2 / A → 0 -/
lemma pf_L_sq_div_self_tendsto_zero {N : ℕ} [NeZero N] :
    Tendsto (fun A : ℝ => (L_N N A) ^ 2 / A) atTop (𝓝 0) := by
  have h : Tendsto (fun A : ℝ => (Real.log (A + 2) + Real.log (N : ℝ) + 2) ^ 2 / A)
      atTop (𝓝 0) := by
    simpa using (ell_pow_div_self_tendsto_zero (N := N) 2)
  simpa [L_N] using h

/-- no-zero neighbourhood at the origin for the completed L-function -/
lemma pf_zero_free_ball {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (hχprim : χ.IsPrimitive) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ z : ℂ, ‖z‖ < δ →
      DirichletCharacter.completedLFunction χ z ≠ 0 := by
  let Λ : ℂ → ℂ := DirichletCharacter.completedLFunction χ
  have hΛ0 : Λ 0 ≠ 0 := by simpa [Λ] using (completedLFunction_zero_ne_zero χ hχ hχprim)
  have hcont : ContinuousAt Λ 0 := ((differentiable_completedLFunction hχ) 0).continuousAt
  rcases (Metric.tendsto_nhds_nhds.mp hcont) (‖Λ 0‖) (by positivity : 0 < ‖Λ 0‖) with ⟨δ, hδ, hb⟩
  refine ⟨δ, hδ, ?_⟩
  intro z hz hz0
  have hbz : dist z 0 < δ := by simpa [dist_eq_norm] using hz
  have hb' : dist (Λ z) (Λ 0) < ‖Λ 0‖ := hb hbz
  have hz0Λ : Λ z = 0 := by simpa [Λ] using hz0
  have hdist : dist (Λ z) (Λ 0) = ‖Λ 0‖ := by simp [hz0Λ, dist_eq_norm]
  have : ‖Λ 0‖ < ‖Λ 0‖ := by simpa [hdist] using hb'
  exact (lt_irrefl ‖Λ 0‖) this


/-! # Part 1 : local log-derivative difference bound (generic complex analysis) -/

/-- Local log-primitive: `g` analytic and non-zero on a ball admits an analytic `F` on the
ball with `F' = logDeriv g` and `(F w).re = log ‖g w‖`. -/
lemma pf_logPrimitiveOnBall {g : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hg_an : AnalyticOnNhd ℂ g (ball 0 R)) (hg_ne : ∀ w ∈ ball 0 R, g w ≠ 0) :
    ∃ F : ℂ → ℂ,
      DifferentiableOn ℂ F (ball 0 R) ∧
      (∀ w ∈ ball 0 R, HasDerivAt F (deriv g w / g w) w) ∧
      (F 0).re = Real.log ‖g 0‖ ∧
      ∀ w ∈ ball 0 R, (F w).re = Real.log ‖g w‖ := by
  let h : ℂ → ℂ := deriv g / g
  have h0ball : (0 : ℂ) ∈ ball (0 : ℂ) R := Metric.mem_ball_self hR
  have hgne0 : g 0 ≠ 0 := hg_ne 0 h0ball
  have hgDiffOn : DifferentiableOn ℂ g (ball (0 : ℂ) R) := hg_an.differentiableOn
  have hdg_an : AnalyticOnNhd ℂ (deriv g) (ball (0 : ℂ) R) := hg_an.deriv
  have hdgDiffOn : DifferentiableOn ℂ (deriv g) (ball (0 : ℂ) R) := hdg_an.differentiableOn
  have hhDiffOn : DifferentiableOn ℂ h (ball (0 : ℂ) R) := by
    simpa [h] using (DifferentiableOn.div hdgDiffOn hgDiffOn hg_ne)
  have hexact : IsExactOn h (ball (0 : ℂ) R) := hhDiffOn.isExactOn_ball
  obtain ⟨F, hF0, hFh⟩ := hexact.with_val_at (0 : ℂ) (Real.log ‖g 0‖ : ℂ)
  let q : ℂ → ℂ := (fun z : ℂ => cexp (F z)) / g
  have hF0_re : (F 0).re = Real.log ‖g 0‖ := by simp [hF0]
  have hq0 : ∀ x : ℂ, x ∈ ball (0 : ℂ) R → HasDerivAt q 0 x := by
    intro x hx
    have hgx : g x ≠ 0 := hg_ne x hx
    have hFx : HasDerivAt F (deriv g x / g x) x := by simpa [h] using hFh x hx
    have hFexp : HasDerivAt (fun z : ℂ => cexp (F z)) (cexp (F x) * (deriv g x / g x)) x := by
      exact (hFx.cexp : HasDerivAt (fun z : ℂ => cexp (F z)) (cexp (F x) * (deriv g x / g x)) x)
    have hg'_ : HasDerivAt g (deriv g x) x := by
      exact (hgDiffOn.differentiableAt (isOpen_ball.mem_nhds hx)).hasDerivAt
    have hqder := hFexp.div hg'_ hgx
    have hzero : ((cexp (F x) * (deriv g x / g x)) * g x - cexp (F x) * deriv g x) / g x ^ 2 = 0 := by
      have hnum : cexp (F x) * (deriv g x / g x) * g x - cexp (F x) * deriv g x = 0 := by
        field_simp [hgx]
        ring
      rw [hnum, zero_div]
    have hq0x : HasDerivAt q 0 x := by
      simpa [q] using (hqder.congr_deriv hzero)
    exact hq0x
  have hqDiffOn : DifferentiableOn ℂ q (ball (0 : ℂ) R) := by
    intro x hx
    exact (hq0 x hx).differentiableAt.differentiableWithinAt
  have hqderiv0 : EqOn (deriv q) 0 (ball (0 : ℂ) R) := by
    intro x hx
    exact (hq0 x hx).deriv
  have hqconst : ∀ w : ℂ, w ∈ ball (0 : ℂ) R → q w = q 0 := fun w hw =>
    (Metric.isOpen_ball.is_const_of_deriv_eq_zero (convex_ball (0 : ℂ) R).isPreconnected hqDiffOn
      hqderiv0 (x := w) (y := (0 : ℂ)) hw h0ball)
  refine ⟨F, ?_, ?_, ?_, ?_⟩
  · intro x hx
    exact (hFh x hx).differentiableAt.differentiableWithinAt
  · intro w hw
    simpa [h] using hFh w hw
  · exact hF0_re
  · intro w hw
    have hqnorm : ‖q w‖ = ‖q 0‖ := by rw [hqconst w hw]
    have hgnw : g w ≠ 0 := hg_ne w hw
    have hg0nz : ‖g 0‖ ≠ 0 := norm_ne_zero_iff.mpr hgne0
    have hnorm_exp0 : ‖cexp (F 0)‖ = ‖g 0‖ := by
      calc
        ‖cexp (F 0)‖ = Real.exp ((F 0).re) := Complex.norm_exp (F 0)
        _ = ‖g 0‖ := by
          rw [hF0_re, Real.exp_log]
          exact (norm_pos_iff.mpr hgne0)
    have hratio : ‖cexp (F w)‖ / ‖g w‖ = 1 := by
      have hq' : ‖cexp (F w) / g w‖ = ‖cexp (F 0) / g 0‖ := by
        simpa [q] using hqnorm
      rw [norm_div, norm_div] at hq'
      calc
        ‖cexp (F w)‖ / ‖g w‖ = ‖cexp (F 0)‖ / ‖g 0‖ := hq'
        _ = 1 := by
          rw [hnorm_exp0]
          exact div_self hg0nz
    have hnw : ‖g w‖ ≠ 0 := norm_ne_zero_iff.mpr hgnw
    have hnorm_expw : ‖cexp (F w)‖ = ‖g w‖ := by
      exact (div_eq_one_iff_eq hnw).mp hratio
    calc
      (F w).re = Real.log ‖cexp (F w)‖ := by
        rw [Complex.norm_exp, Real.log_exp]
      _ = Real.log ‖g w‖ := by rw [hnorm_expw]

/-- The analyticity of the log-derivative of a nonzero analytic function on a ball. -/
lemma pf_logDeriv_analytic_ball {g : ℂ → ℂ} {R : ℝ}
    (hg_an : AnalyticOnNhd ℂ g (ball 0 R)) (hg_ne : ∀ w ∈ ball 0 R, g w ≠ 0) :
    AnalyticOnNhd ℂ (fun w : ℂ => logDeriv g w) (ball (0 : ℂ) R) := by
  intro w hw
  have h1 : AnalyticAt ℂ (deriv g) w := (hg_an.deriv) w hw
  have h2 : AnalyticAt ℂ g w := hg_an w hw
  have hq : AnalyticAt ℂ (fun z : ℂ => deriv g z / g z) w := h1.div h2 (hg_ne w hw)
  convert hq using 1
  funext z
  rw [logDeriv_apply]

/-- derivative-difference bound for a log-primitive, from a sup bound on log‖g‖. -/
lemma pf_logDeriv_sub_of_sup {g : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hg_an : AnalyticOnNhd ℂ g (ball 0 R)) (hg_ne : ∀ w ∈ ball 0 R, g w ≠ 0)
    {M0 : ℝ} (hM0 : 0 ≤ M0)
    (hgM : ∀ w : ℂ, w ∈ ball 0 R → Real.log ‖g w‖ ≤ M0)
    (hg0 : |Real.log ‖g 0‖| ≤ M0) {s : ℂ} (hs : ‖s‖ ≤ R / 8) :
    ‖logDeriv g s - logDeriv g 0‖ ≤ 1024 * (max M0 1) * ‖s‖ / R ^ 2 := by
  classical
  rcases pf_logPrimitiveOnBall (g := g) (R := R) hR hg_an hg_ne with ⟨F, hFdiff, hFh, hF0re, hFre⟩
  let M : ℝ := 2 * max M0 1
  have hMpos : 0 < M := by dsimp [M]; positivity
  have hMge : 2 * M0 ≤ M := by
    dsimp [M]
    have h1 : M0 ≤ max M0 1 := le_max_left M0 1
    linarith only [h1]
  have hFreM : ∀ w : ℂ, w ∈ ball (0 : ℂ) R → ((F w - F 0).re) ≤ M := by
    intro w hw
    have hle1 : (F w).re ≤ M0 := by
      rw [hFre w hw]
      exact hgM w hw
    have hle2 : -M0 ≤ (F 0).re := by
      rw [hF0re]
      have habs := abs_le.mp hg0
      linarith only [habs]
    have hmain : (F w).re - (F 0).re ≤ 2 * M0 := by linarith only [hle1, hle2]
    have : ((F w - F 0).re) = (F w).re - (F 0).re := by simp
    rw [this]
    exact le_trans hmain hMge
  have hF0eq : (fun w : ℂ => F w - F 0) 0 = 0 := by simp
  have hFdiff2 : DifferentiableOn ℂ (fun w : ℂ => F w - F 0) (ball (0 : ℂ) R) := by
    intro w hw
    exact (DifferentiableAt.sub (hFdiff.differentiableAt (isOpen_ball.mem_nhds hw))
      (differentiableAt_const (F 0))).differentiableWithinAt
  have hsup : ∀ w : ℂ, ‖w‖ ≤ R / 2 → ‖F w - F 0‖ ≤ 2 * M := by
    intro w hw
    have hwb : w ∈ ball (0 : ℂ) R := by
      rw [mem_ball_zero_iff]
      have hR2 : 0 ≤ R / 2 := by positivity
      linarith only [hR, hw]
    have hbc := Complex.borelCaratheodory_zero (M := M) hMpos (f := fun z : ℂ => F z - F 0)
      (R := R) hFdiff2 (by intro z hz; simpa using hFreM z hz) hR hwb hF0eq
    have hden : 0 < R - ‖w‖ := by
      rw [mem_ball_zero_iff] at hwb
      linarith only [hwb]
    have hle : ‖w‖ / (R - ‖w‖) ≤ 1 := by
      rw [div_le_one hden]
      have hR2 : R / 2 ≤ R - ‖w‖ := by linarith only [hw]
      linarith only [hw]
    calc
      ‖F w - F 0‖ ≤ 2 * M * ‖w‖ / (R - ‖w‖) := hbc
      _ = 2 * M * (‖w‖ / (R - ‖w‖)) := by ring
      _ ≤ 2 * M * 1 := by
        exact mul_le_mul_of_nonneg_left hle (by positivity : 0 ≤ 2 * M)
      _ = 2 * M := by ring
  -- ‖logDeriv g z‖ ≤ 16*M/R for ‖z‖ ≤ 3R/8
  have hder1 : ∀ z : ℂ, ‖z‖ ≤ 3 * R / 8 → ‖logDeriv g z‖ ≤ 16 * M / R := by
    intro z hz
    let r : ℝ := R / 8
    have hr : 0 < r := by dsimp [r]; positivity
    have hclosed : Metric.closedBall z r ⊆ ball (0 : ℂ) R := by
      intro x hx
      rw [Metric.mem_closedBall, dist_eq_norm] at hx
      rw [mem_ball_zero_iff]
      have hle : ‖x‖ ≤ ‖z‖ + ‖x - z‖ := by
        have hx2 : ‖x‖ = ‖z + (x - z)‖ := by rw [← add_sub_cancel z x]; ring_nf
        rw [hx2]
        simpa [add_comm] using (norm_add_le z (x - z))
      have hxr : ‖x - z‖ ≤ r := hx
      dsimp [r] at hxr ⊢
      linarith only [hz, hxr, hR, hle]
    have hFz : DifferentiableOn ℂ (fun w : ℂ => F w - F 0) (Metric.closedBall z r) := by
      intro x hx
      have hxR : x ∈ ball (0 : ℂ) R := hclosed hx
      exact (DifferentiableAt.sub (hFdiff.differentiableAt (isOpen_ball.mem_nhds hxR))
        (differentiableAt_const (F 0))).differentiableWithinAt
    have hdiffCl : DiffContOnCl ℂ (fun w : ℂ => F w - F 0) (ball z r) := by
      refine DifferentiableOn.diffContOnCl ?_
      simpa [r, closure_ball z (ne_of_gt hr)] using hFz
    have hC : ∀ w : ℂ, w ∈ sphere z r → ‖F w - F 0‖ ≤ 2 * M := by
      intro w hw
      rw [Metric.mem_sphere] at hw
      have hwz : ‖w - z‖ = r := by simpa [dist_eq_norm] using hw
      have hw' : ‖w‖ ≤ R / 2 := by
        have hle : ‖w‖ ≤ ‖z‖ + ‖w - z‖ := by
          have hw2 : ‖w‖ = ‖z + (w - z)‖ := by rw [← add_sub_cancel z w]; ring_nf
          rw [hw2]
          simpa [add_comm] using (norm_add_le z (w - z))
        dsimp [r] at hwz ⊢
        linarith only [hz, hwz, hle]
      exact hsup w hw'
    have hCau := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (f := fun w : ℂ => F w - F 0)
      (c := z) (R := r) hr hdiffCl (by intro w hw; simpa using hC w hw)
    have hzR : z ∈ ball (0 : ℂ) R := by
      rw [mem_ball_zero_iff]
      linarith only [hz, show 0 < R from hR, hR]
    have hfder : deriv (fun w : ℂ => F w - F 0) z = deriv F z := by
      have hFdz : DifferentiableAt ℂ F z := hFdiff.differentiableAt (isOpen_ball.mem_nhds hzR)
      calc
        deriv (fun w : ℂ => F w - F 0) z
            = deriv ((fun w : ℂ => F w) - (fun _ : ℂ => F 0)) z := by rfl
        _ = deriv F z - deriv (fun _ : ℂ => F 0) z := by
            exact deriv_sub hFdz (differentiableAt_const (F 0))
        _ = deriv F z := by simp
    have hlogz : logDeriv g z = deriv F z := by
      have hFhz := hFh z hzR
      rw [logDeriv_apply, hFhz.deriv]
    calc
      ‖logDeriv g z‖ = ‖deriv F z‖ := by rw [hlogz]
      _ = ‖deriv (fun w : ℂ => F w - F 0) z‖ := by rw [hfder]
      _ ≤ (2 * M) / r := hCau
      _ = 16 * M / R := by
        dsimp [r]
        field_simp [show R ≠ 0 from ne_of_gt hR]
        ring
  -- ‖deriv (logDeriv g) z‖ ≤ 128*M/R^2 for ‖z‖ ≤ R/4
  have hder2 : ∀ z : ℂ, ‖z‖ ≤ R / 4 → ‖deriv (logDeriv g) z‖ ≤ 128 * M / R ^ 2 := by
    intro z hz
    let r : ℝ := R / 8
    have hr : 0 < r := by dsimp [r]; positivity
    have hz3 : ∀ w : ℂ, w ∈ sphere z r → ‖w‖ ≤ 3 * R / 8 := by
      intro w hw
      rw [Metric.mem_sphere] at hw
      have hwz : ‖w - z‖ = r := by simpa [dist_eq_norm] using hw
      have hle : ‖w‖ ≤ ‖z‖ + ‖w - z‖ := by
        have hw2 : ‖w‖ = ‖z + (w - z)‖ := by rw [← add_sub_cancel z w]; ring_nf
        rw [hw2]
        simpa [add_comm] using (norm_add_le z (w - z))
      dsimp [r] at hwz ⊢
      linarith only [hz, hwz, hle]
    have hF' : ∀ w : ℂ, w ∈ sphere z r → ‖logDeriv g w‖ ≤ 16 * M / R := by
      intro w hw
      exact hder1 w (hz3 w hw)
    have hclosed : Metric.closedBall z r ⊆ ball (0 : ℂ) R := by
      intro x hx
      rw [Metric.mem_closedBall, dist_eq_norm] at hx
      rw [mem_ball_zero_iff]
      have hle : ‖x‖ ≤ ‖z‖ + ‖x - z‖ := by
        have hx2 : ‖x‖ = ‖z + (x - z)‖ := by rw [← add_sub_cancel z x]; ring_nf
        rw [hx2]
        simpa [add_comm] using (norm_add_le z (x - z))
      have hxr : ‖x - z‖ ≤ r := hx
      dsimp [r] at hxr ⊢
      linarith only [hz, hxr, hR, hle]
    have hlg_an : AnalyticOnNhd ℂ (fun w : ℂ => logDeriv g w) (ball (0 : ℂ) R) :=
      pf_logDeriv_analytic_ball hg_an hg_ne
    have hlg_z : DifferentiableOn ℂ (fun w : ℂ => logDeriv g w) (Metric.closedBall z r) := by
      intro x hx
      have hxR : x ∈ ball (0 : ℂ) R := hclosed hx
      exact (hlg_an.differentiableOn.differentiableAt (isOpen_ball.mem_nhds hxR)).differentiableWithinAt
    have hdiffCl : DiffContOnCl ℂ (fun w : ℂ => logDeriv g w) (ball z r) := by
      refine DifferentiableOn.diffContOnCl ?_
      simpa [r, closure_ball z (ne_of_gt hr)] using hlg_z
    have hCau := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (f := fun w : ℂ => logDeriv g w)
      (c := z) (R := r) hr hdiffCl hF'
    calc
      ‖deriv (logDeriv g) z‖ ≤ (16 * M / R) / r := hCau
      _ = 128 * M / R ^ 2 := by
        dsimp [r]
        field_simp [show R ≠ 0 from ne_of_gt hR]
        ring
  -- mean value on the convex ball
  have hsR4 : s ∈ ball (0 : ℂ) (R / 4) := by
    rw [mem_ball_zero_iff]
    have hRp : 0 < R / 4 := by positivity
    linarith only [hR, hs]
  have h0R4 : (0 : ℂ) ∈ ball (0 : ℂ) (R / 4) := by
    rw [mem_ball_zero_iff]
    have hR4 : 0 < R / 4 := by positivity
    simpa using hR4
  have hCbound : ∀ z : ℂ, z ∈ ball (0 : ℂ) (R / 4) → ‖deriv (logDeriv g) z‖ ≤ 128 * M / R ^ 2 := by
    intro z hz
    rw [mem_ball_zero_iff] at hz
    exact hder2 z (by linarith only [hz])
  have hdiff_at : ∀ z : ℂ, z ∈ ball (0 : ℂ) (R / 4) → DifferentiableAt ℂ (logDeriv g) z := by
    intro z hz
    have hlg_anR4 : AnalyticOnNhd ℂ (fun w : ℂ => logDeriv g w) (ball (0 : ℂ) (R / 4)) := by
      intro w hw
      have hwR : w ∈ ball (0 : ℂ) R := by
        rw [mem_ball_zero_iff]
        rw [mem_ball_zero_iff] at hw
        linarith only [hR, hw]
      exact (pf_logDeriv_analytic_ball hg_an hg_ne) w hwR
    exact (hlg_anR4.differentiableOn.differentiableAt (isOpen_ball.mem_nhds hz))
  have hmvt := Convex.norm_image_sub_le_of_norm_deriv_le (𝕜 := ℂ) (f := fun w : ℂ => logDeriv g w)
    (s := ball (0 : ℂ) (R / 4)) (C := 128 * M / R ^ 2) hdiff_at hCbound
    (convex_ball (0 : ℂ) (R / 4)) h0R4 hsR4
  have hder : ‖logDeriv g s - logDeriv g 0‖ ≤ 128 * M * ‖s‖ / R ^ 2 := by
    have hmvt' : ‖logDeriv g s - logDeriv g 0‖ ≤ (128 * M / R ^ 2) * ‖s‖ := by simpa using hmvt
    calc
      ‖logDeriv g s - logDeriv g 0‖ ≤ (128 * M / R ^ 2) * ‖s‖ := hmvt'
      _ = 128 * M * ‖s‖ / R ^ 2 := by
        field_simp [show R ^ 2 ≠ 0 from pow_ne_zero 2 (ne_of_gt hR)]
  have hle_mul : 128 * M ≤ 1024 * max M0 1 := by
    dsimp [M]
    linarith only [hMpos]
  have hle1 : 128 * M * ‖s‖ / R ^ 2 ≤ 1024 * (max M0 1) * ‖s‖ / R ^ 2 := by
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hle_mul (norm_nonneg s))
      (sq_pos_of_pos hR).le
  calc
    ‖logDeriv g s - logDeriv g 0‖ ≤ 128 * M * ‖s‖ / R ^ 2 := hder
    _ ≤ 1024 * (max M0 1) * ‖s‖ / R ^ 2 := hle1



/-! # Part 2 : divisor/factorisation bookkeeping and the good-circle log bound -/

/-- Zeros of the completed L-function stay away from 0 (χ primitive non-trivial). -/
lemma pf_zeros_ge_delta {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (hχprim : χ.IsPrimitive) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 ∧
      ∀ u : ℂ, DirichletCharacter.completedLFunction χ u = 0 → δ₀ ≤ ‖u‖ := by
  rcases pf_zero_free_ball χ hχ hχprim with ⟨δ, hδpos, hδ⟩
  let δ₀ : ℝ := min δ 1
  have hδ₀pos : 0 < δ₀ := by dsimp [δ₀]; positivity
  have hδ₀le1 : δ₀ ≤ 1 := by dsimp [δ₀]; exact min_le_right δ 1
  refine ⟨δ₀, hδ₀pos, hδ₀le1, ?_⟩
  intro u hu
  by_contra hlt
  have hδ₀leδ : δ₀ ≤ δ := by dsimp [δ₀]; exact min_le_left δ 1
  have huδ : ‖u‖ < δ := lt_of_lt_of_le (lt_of_not_ge hlt) hδ₀leδ
  exact (hδ u huδ) hu

lemma pf_divisor_nonneg_closedBall {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (R : ℝ) (u : ℂ) :
    0 ≤ (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
      (closedBall (0 : ℂ) R)) u := by
  have hfan : AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction χ)
      (closedBall (0 : ℂ) R) := by
    intro z hz
    exact (differentiable_completedLFunction hχ).analyticAt z
  exact (MeromorphicOn.AnalyticOnNhd.divisor_nonneg hfan) u

lemma pf_divisor_support_finite {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (R : ℝ) :
    (Function.support (fun u : ℂ =>
      MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
        (closedBall (0 : ℂ) R) u)).Finite := by
  have hfan : AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction χ)
      (closedBall (0 : ℂ) R) := by
    intro z hz
    exact (differentiable_completedLFunction hχ).analyticAt z
  exact MeromorphicOn.divisor_support_finite_of_subset
    (f := DirichletCharacter.completedLFunction χ)
    (V := closedBall (0 : ℂ) R) (U := closedBall (0 : ℂ) R)
    hfan.meromorphicOn (isCompact_closedBall (0 : ℂ) R) (by intro z hz; exact hz)

lemma pf_divisor_ne_zero_is_zero {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) {R : ℝ} {z : ℂ}
    (hd : (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
      (closedBall (0 : ℂ) R)) z ≠ 0) :
    DirichletCharacter.completedLFunction χ z = 0 := by
  let Λ : ℂ → ℂ := DirichletCharacter.completedLFunction χ
  have hfan : AnalyticOnNhd ℂ Λ (closedBall (0 : ℂ) R) := by
    intro w hw
    exact (differentiable_completedLFunction hχ).analyticAt w
  have hzB : z ∈ closedBall (0 : ℂ) R := by
    by_contra hout
    rw [MeromorphicOn.divisor_def] at hd
    simp [hout] at hd
  by_contra hfz
  have hord : meromorphicOrderAt Λ z = 0 :=
    Commons.Analysis.Complex.meromorphicOrderAt_eq_zero_of_ne_zero (hfan z hzB) hfz
  have hdiv : MeromorphicOn.divisor Λ (closedBall (0 : ℂ) R) z = 0 := by
    rw [MeromorphicOn.divisor_apply hfan.meromorphicOn hzB]
    simp [hord, Λ]
  exact hd (by simpa [Λ] using hdiv)

lemma pf_norm_finset_prod {ι : Type*} (S : Finset ι) (a : ι → ℂ) :
    ‖∏ i ∈ S, a i‖ = ∏ i ∈ S, ‖a i‖ := by
  classical
  refine Finset.induction_on S ?_ (fun i S hi ih => ?_)
  · simp
  · rw [Finset.prod_insert hi, Finset.prod_insert hi, norm_mul, ih]

lemma pf_pow_zpow_toNat {x : ℝ} {d : ℤ} (hd : 0 ≤ d) : x ^ d = x ^ d.toNat := by
  rw [← Int.toNat_of_nonneg hd]
  exact (zpow_natCast x d.toNat).symm

lemma pf_zpow_le_of_le {x y : ℝ} {d : ℤ} (hx : 0 ≤ x) (hxy : x ≤ y) (hd : 0 ≤ d) :
    x ^ d ≤ y ^ d := by
  rw [pf_pow_zpow_toNat hd, pf_pow_zpow_toNat hd]
  exact pow_le_pow_left₀ hx hxy d.toNat

lemma pf_zpow_pos {x : ℝ} {d : ℤ} (hx : 0 < x) (hd : 0 ≤ d) : 0 < x ^ d := by
  rw [pf_pow_zpow_toNat hd]
  exact pow_pos hx d.toNat

lemma pf_log_zpow {x : ℝ} {d : ℤ} (hx : 0 < x) (hd : 0 ≤ d) :
    Real.log (x ^ d) = (d : ℝ) * Real.log x := by
  rw [pf_pow_zpow_toNat hd]
  have hlog : Real.log (x ^ d.toNat) = (d.toNat : ℝ) * Real.log x := Real.log_pow x d.toNat
  have hcast : (d.toNat : ℝ) = (d : ℝ) := by
    rw [← Int.cast_natCast d.toNat]
    exact congrArg (fun a : ℤ => (a : ℝ)) (Int.toNat_of_nonneg hd)
  simpa [hcast] using hlog

/-- norm of a zpower equals the zpower of the norm. -/
lemma pf_norm_zpow_eq (z : ℂ) (d : ℤ) : ‖z ^ d‖ = ‖z‖ ^ d := norm_zpow z d

/-- `-log ‖P_T ζ‖ ≤ 2·log L · Z_T` for ζ on a good circle of radius T. -/
lemma pf_fac_log_lower {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) {A T : ℝ} (hA0 : 0 ≤ A) (hT0 : 0 < T)
    (hmargin : ∀ u : ℂ, DirichletCharacter.completedLFunction χ u = 0 →
      (L_N N A) ^ 2 * |‖u‖ - T| ≥ 1)
    {ζ : ℂ} (hζ : ‖ζ‖ = T) :
    -Real.log ‖∏ᶠ u : ℂ, (ζ - u) ^ (MeromorphicOn.divisor
        (DirichletCharacter.completedLFunction χ) (closedBall (0 : ℂ) T) u)‖ ≤
      (2 * Real.log (L_N N A)) *
        (∑ᶠ u : ℂ, ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
          (closedBall (0 : ℂ) T)) u : ℝ)) := by
  classical
  let Λ : ℂ → ℂ := DirichletCharacter.completedLFunction χ
  let d : ℂ → ℤ := fun u => MeromorphicOn.divisor Λ (closedBall (0 : ℂ) T) u
  let L : ℝ := L_N N A
  have hLpos : 0 < L := pf_L_pos (N := N) hA0
  have hL2pos : 0 < L ^ 2 := pow_pos hLpos 2
  let m : ℝ := 1 / L ^ 2
  have hmpos : 0 < m := by dsimp [m]; exact div_pos (by norm_num) hL2pos
  have hd_nonneg : ∀ u, 0 ≤ d u := by
    intro u
    dsimp [d]
    exact pf_divisor_nonneg_closedBall χ hχ T u
  have hsupport : (Function.support d).Finite := by
    dsimp [d]
    exact pf_divisor_support_finite χ hχ T
  let S : Finset ℂ := hsupport.toFinset
  have hmemS : ∀ u : ℂ, u ∈ S ↔ d u ≠ 0 := by
    intro u
    dsimp [S]
    rw [Set.Finite.mem_toFinset]
    rfl
  have hdist : ∀ u : ℂ, u ∈ S → m ≤ ‖ζ - u‖ := by
    intro u hu
    have hdne : d u ≠ 0 := (hmemS u).mp hu
    have hzu : Λ u = 0 := by
      dsimp [d] at hdne
      exact pf_divisor_ne_zero_is_zero χ hχ hdne
    have hmarg := hmargin u (by simpa [Λ] using hzu)
    have hmul' : 1 ≤ |‖u‖ - T| * (L ^ 2) := by
      simpa [mul_comm, L] using hmarg
    have hle_m : m ≤ |‖u‖ - T| := (div_le_iff₀ hL2pos).mpr hmul'
    have habs : |‖u‖ - ‖ζ‖| ≤ ‖ζ - u‖ := by
      simpa [abs_sub_comm] using (abs_norm_sub_norm_le ζ u)
    have hrew : |‖u‖ - T| = |‖u‖ - ‖ζ‖| := by rw [hζ]
    exact le_trans hle_m (by rwa [hrew])
  have hprod_pos_fac : ∀ u : ℂ, u ∈ S → 0 < ‖(ζ - u) ^ (d u)‖ := by
    intro u hu
    have hb : 0 < ‖ζ - u‖ := lt_of_lt_of_le hmpos (hdist u hu)
    have hpow : ‖(ζ - u) ^ (d u)‖ = ‖ζ - u‖ ^ (d u) := pf_norm_zpow_eq (ζ - u) (d u)
    rw [hpow]
    exact pf_zpow_pos hb (hd_nonneg u)
  have hlog_per : ∀ u : ℂ, u ∈ S →
      -Real.log ‖(ζ - u) ^ (d u)‖ ≤ (d u : ℝ) * (2 * Real.log L) := by
    intro u hu
    have hmle : m ≤ ‖ζ - u‖ := hdist u hu
    have hb : 0 < ‖ζ - u‖ := lt_of_lt_of_le hmpos hmle
    have hpow_le : m ^ (d u) ≤ ‖ζ - u‖ ^ (d u) :=
      pf_zpow_le_of_le (le_of_lt hmpos) hmle (hd_nonneg u)
    have hnorm : ‖(ζ - u) ^ (d u)‖ = ‖ζ - u‖ ^ (d u) := pf_norm_zpow_eq (ζ - u) (d u)
    have h1 : 0 < m ^ (d u) := pf_zpow_pos hmpos (hd_nonneg u)
    have h2 : 0 < ‖ζ - u‖ ^ (d u) := pf_zpow_pos hb (hd_nonneg u)
    have hlog_ge : Real.log (m ^ (d u)) ≤ Real.log ‖(ζ - u) ^ (d u)‖ := by
      rw [hnorm]
      exact Real.log_le_log h1 hpow_le
    have hlogm : Real.log (m ^ (d u)) = (d u : ℝ) * Real.log m := pf_log_zpow hmpos (hd_nonneg u)
    have hlogmval : Real.log m = -2 * Real.log L := by
      dsimp [m]
      rw [one_div, Real.log_inv, Real.log_pow]
      ring
    have hstep : (d u : ℝ) * Real.log m ≤ Real.log ‖(ζ - u) ^ (d u)‖ := by
      simpa [hlogm] using hlog_ge
    have hmain : -Real.log ‖(ζ - u) ^ (d u)‖ ≤ (d u : ℝ) * (2 * Real.log L) := by
      have hcalc : -Real.log ‖(ζ - u) ^ (d u)‖ ≤ -(d u : ℝ) * Real.log m := by linarith only [hlog_ge, hlogm]
      have hmval : -(d u : ℝ) * Real.log m = (d u : ℝ) * (2 * Real.log L) := by
        rw [hlogmval]
        ring
      linarith only [hlog_ge, hlogm, hmval]
    exact hmain
  have hsubP : mulSupport (fun u : ℂ => (ζ - u) ^ (d u)) ⊆ (S : Set ℂ) := by
    intro u hu
    rw [Function.mem_mulSupport] at hu
    have hdne : d u ≠ 0 := by
      intro hd0
      have : (ζ - u) ^ (d u) = 1 := by simp [hd0]
      exact hu this
    exact (hmemS u).mpr hdne
  have hprod_eq : (∏ᶠ u : ℂ, (ζ - u) ^ (d u)) = ∏ u ∈ S, (ζ - u) ^ (d u) :=
    finprod_eq_prod_of_mulSupport_subset (fun u : ℂ => (ζ - u) ^ (d u)) hsubP
  have hfin_eq : (∑ᶠ u : ℂ, ((d u : ℤ) : ℝ)) = ∑ u ∈ S, ((d u : ℤ) : ℝ) := by
    refine finsum_eq_sum_of_support_subset (fun u : ℂ => ((d u : ℤ) : ℝ)) ?_
    intro u hu
    rw [Function.mem_support] at hu
    have hdne : d u ≠ 0 := by
      intro hd0
      exact hu (by simp [hd0])
    exact (hmemS u).mpr hdne
  have hZge0 : 0 ≤ ∑ᶠ u : ℂ, ((d u : ℤ) : ℝ) := by
    rw [hfin_eq]
    exact Finset.sum_nonneg (by intro u hu; exact_mod_cast (hd_nonneg u))
  have h2L : 0 ≤ 2 * Real.log L := by
    have h1 : 1 ≤ L := by linarith [pf_L_ge_two (N := N) hA0]
    have hlog : 0 ≤ Real.log L := Real.log_nonneg (by linarith only [h1])
    linarith only [hlog]
  calc
    -Real.log ‖∏ᶠ u : ℂ, (ζ - u) ^ (d u)‖
        = -Real.log ‖∏ u ∈ S, (ζ - u) ^ (d u)‖ := by rw [hprod_eq]
    _ = -Real.log (∏ u ∈ S, ‖(ζ - u) ^ (d u)‖) := by
        rw [pf_norm_finset_prod S (fun u => (ζ - u) ^ (d u))]
    _ = -(∑ u ∈ S, Real.log ‖(ζ - u) ^ (d u)‖) := by
        rw [Real.log_prod]
        intro u hu
        exact (hprod_pos_fac u hu).ne'
    _ = ∑ u ∈ S, -Real.log ‖(ζ - u) ^ (d u)‖ := by simp [Finset.sum_neg_distrib]
    _ ≤ ∑ u ∈ S, ((d u : ℤ) : ℝ) * (2 * Real.log L) := by
        refine Finset.sum_le_sum (fun u hu => ?_)
        have hlogp := hlog_per u hu
        -- hlog_per has (d u : ℝ) as ℤ-cast of the int d; align casts
        have hcastd : ((d u : ℤ) : ℝ) = (d u : ℝ) := rfl
        simpa [hcastd] using hlogp
    _ = (∑ u ∈ S, ((d u : ℤ) : ℝ)) * (2 * Real.log L) := by rw [Finset.sum_mul]
    _ = (∑ᶠ u : ℂ, ((d u : ℤ) : ℝ)) * (2 * Real.log L) := by rw [hfin_eq]
    _ = (2 * Real.log L) * (∑ᶠ u : ℂ, ((d u : ℤ) : ℝ)) := by ring
    _ = (2 * Real.log (L_N N A)) * (∑ᶠ u : ℂ, (((MeromorphicOn.divisor Λ
          (closedBall (0 : ℂ) T)) u : ℤ) : ℝ)) := by simp [d, L]



def pfZ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (T : ℝ) : ℝ :=
  ∑ᶠ u : ℂ, (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
      (Metric.closedBall (0 : ℂ) T)) u : ℤ) : ℝ)

def pfP (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (T : ℝ) (z : ℂ) : ℂ :=
  ∏ᶠ u : ℂ, (z - u) ^ (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
      (closedBall (0 : ℂ) T) u)

lemma pf_log_eq_of_mul {x y : ℂ} (hx : x ≠ 0) (hy : y ≠ 0) :
    Real.log ‖x * y‖ = Real.log ‖x‖ + Real.log ‖y‖ := by
  rw [norm_mul]
  exact Real.log_mul (norm_ne_zero_iff.mpr hx) (norm_ne_zero_iff.mpr hy)

/-- completedL: zero count bound rearranged into pfZ notation. -/
lemma pf_LogΛ_bound {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {T : ℝ} (hT2 : 2 ≤ T)
    {gc : ℝ} (hgc : ∀ R : ℝ, 2 ≤ R → ∀ z : ℂ, ‖z‖ = R →
      ‖DirichletCharacter.completedLFunction χ z‖ ≤ Real.exp (gc * R * L_N N R))
    {ζ : ℂ} (hζ : ‖ζ‖ = T) (hζnz : DirichletCharacter.completedLFunction χ ζ ≠ 0) :
    Real.log ‖DirichletCharacter.completedLFunction χ ζ‖ ≤ gc * T * L_N N T := by
  have hb := hgc T hT2 ζ hζ
  have hle : Real.log ‖DirichletCharacter.completedLFunction χ ζ‖ ≤
      Real.log (Real.exp (gc * T * L_N N T)) := by
    exact Real.log_le_log (norm_pos_iff.mpr hζnz) hb
  rwa [Real.log_exp] at hle

/-- The divisor product is nonzero at a point of the good circle. -/
lemma pf_P_ne_zero_circle {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (hχprim : χ.IsPrimitive) {T : ℝ} (hTpos : 0 < T)
    (hcirc : ∀ u : ℂ, ‖u‖ = T → DirichletCharacter.completedLFunction χ u ≠ 0)
    {ζ : ℂ} (hζ : ‖ζ‖ = T) : pfP N χ T ζ ≠ 0 := by
  classical
  let Λ : ℂ → ℂ := DirichletCharacter.completedLFunction χ
  have hΛ0 : Λ 0 ≠ 0 := by simpa [Λ] using (completedLFunction_zero_ne_zero χ hχ hχprim)
  have hΛdiff : Differentiable ℂ Λ := by simpa [Λ] using (differentiable_completedLFunction hχ)
  rcases factorization_open (f := Λ) (R := T) hTpos hΛdiff hΛ0 hcirc with ⟨g, ε, hε, hg_an, hg_nz, hfac⟩
  have hζε : ζ ∈ ball (0 : ℂ) (T + ε) := by
    rw [mem_ball_zero_iff]
    linarith only [hζ, hε]
  have hgζ : g ζ ≠ 0 := hg_nz ζ hζε
  have hfacζ := hfac ζ hζε
  have hΛζ : Λ ζ ≠ 0 := by simpa [Λ] using hcirc ζ hζ
  have hmul : Λ ζ = (∏ᶠ u : ℂ, (ζ - u) ^ (MeromorphicOn.divisor Λ (closedBall (0 : ℂ) T) u)) * g ζ := hfacζ
  have hmul' : pfP N χ T ζ * g ζ ≠ 0 := by simpa [pfP, Λ, hmul] using hΛζ
  exact (mul_ne_zero_iff.mp hmul').1

/-- |log‖P_T 0‖| ≤ Z·(log T + |log δ₀|) for the divisor product at 0. -/
lemma pf_P0_log_bound {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    {T : ℝ} (hT : 1 ≤ T) (δ₀ : ℝ) (hδ₀pos : 0 < δ₀)
    (hδ₀ : ∀ u : ℂ, DirichletCharacter.completedLFunction χ u = 0 → δ₀ ≤ ‖u‖) :
    |Real.log ‖pfP N χ T 0‖| ≤
      (pfZ N χ T) * (Real.log T + |Real.log δ₀|) := by
  classical
  let Λc : ℂ → ℂ := DirichletCharacter.completedLFunction χ
  let d : ℂ → ℤ := fun u => MeromorphicOn.divisor Λc (closedBall (0 : ℂ) T) u
  have hd_nonneg : ∀ u : ℂ, 0 ≤ d u := by
    intro u
    dsimp [d]
    exact pf_divisor_nonneg_closedBall χ hχ T u
  have hsupp : (Function.support d).Finite := by
    dsimp [d]
    exact pf_divisor_support_finite χ hχ T
  let S : Finset ℂ := hsupp.toFinset
  have hmemS : ∀ u : ℂ, u ∈ S ↔ d u ≠ 0 := by
    intro u
    dsimp [S]
    rw [Set.Finite.mem_toFinset]
    rfl
  have hδT : ∀ u : ℂ, u ∈ S → δ₀ ≤ ‖u‖ ∧ ‖u‖ ≤ T := by
    intro u hu
    have hdne : d u ≠ 0 := (hmemS u).mp hu
    have hzu : Λc u = 0 := by
      dsimp [d] at hdne
      exact pf_divisor_ne_zero_is_zero χ hχ hdne
    have huδ : δ₀ ≤ ‖u‖ := hδ₀ u (by simpa [Λc] using hzu)
    have huT : ‖u‖ ≤ T := by
      by_contra hout
      have hdne0 : MeromorphicOn.divisor Λc (closedBall (0 : ℂ) T) u ≠ 0 := by simpa [d] using hdne
      rw [MeromorphicOn.divisor_def] at hdne0
      simp [hout] at hdne0
    exact ⟨huδ, huT⟩
  have hlogTnonneg : 0 ≤ Real.log T := Real.log_nonneg hT
  let B : ℝ := Real.log T + |Real.log δ₀|
  have hB_nonneg : 0 ≤ B := by dsimp [B]; positivity
  have hlogB : ∀ u : ℂ, u ∈ S → |Real.log ‖u‖| ≤ B := by
    intro u hu
    have hδle : δ₀ ≤ ‖u‖ := (hδT u hu).1
    have hTge : ‖u‖ ≤ T := (hδT u hu).2
    have hpos : 0 < ‖u‖ := lt_of_lt_of_le hδ₀pos hδle
    have hle1 : Real.log ‖u‖ ≤ B := by
      have h : Real.log ‖u‖ ≤ Real.log T := Real.log_le_log hpos hTge
      have habs : 0 ≤ |Real.log δ₀| := abs_nonneg _
      dsimp [B]
      linarith only [h, habs]
    have hle2 : -B ≤ Real.log ‖u‖ := by
      have h : Real.log δ₀ ≤ Real.log ‖u‖ := Real.log_le_log hδ₀pos hδle
      have hnegabs : -|Real.log δ₀| ≤ Real.log δ₀ := neg_abs_le (Real.log δ₀)
      have h3 : -B ≤ -|Real.log δ₀| := by
        dsimp [B]
        linarith only [hlogTnonneg]
      exact le_trans (le_trans h3 hnegabs) h
    exact abs_le.mpr ⟨hle2, hle1⟩
  have hprod_pos_fac : ∀ u : ℂ, u ∈ S → 0 < ‖(0 : ℂ) - u‖ := by
    intro u hu
    exact lt_of_lt_of_le hδ₀pos (by simpa [norm_sub_rev] using (hδT u hu).1)
  have hlog_per : ∀ u : ℂ, u ∈ S → -B ≤ Real.log ‖(0 : ℂ) - u‖ ∧ Real.log ‖(0 : ℂ) - u‖ ≤ B := by
    intro u hu
    have hb : |Real.log ‖(0 : ℂ) - u‖| ≤ B := by
      simpa [norm_sub_rev] using hlogB u hu
    exact abs_le.mp hb
  have hsubP : mulSupport (fun u : ℂ => (0 - u) ^ (d u)) ⊆ (S : Set ℂ) := by
    intro u hu
    rw [Function.mem_mulSupport] at hu
    have hdne : d u ≠ 0 := by
      intro hd0
      have : (0 - u) ^ (d u) = 1 := by simp [hd0]
      exact hu this
    exact (hmemS u).mpr hdne
  have hprod_eq : (∏ᶠ u : ℂ, (0 - u) ^ (d u)) = ∏ u ∈ S, (0 - u) ^ (d u) :=
    finprod_eq_prod_of_mulSupport_subset (fun u : ℂ => (0 - u) ^ (d u)) hsubP
  have hfac_pos : ∀ u : ℂ, u ∈ S → 0 < ‖(0 - u) ^ (d u)‖ := by
    intro u hu
    have hb : 0 < ‖(0 : ℂ) - u‖ := hprod_pos_fac u hu
    have hpow : ‖(0 - u) ^ (d u)‖ = ‖(0 : ℂ) - u‖ ^ (d u) := pf_norm_zpow_eq (0 - u) (d u)
    rw [hpow]
    exact pf_zpow_pos hb (hd_nonneg u)
  have hlog_all :
      Real.log ‖∏ᶠ u : ℂ, (0 - u) ^ (d u)‖ = ∑ u ∈ S, ((d u : ℤ) : ℝ) * Real.log ‖(0 : ℂ) - u‖ := by
    calc
      Real.log ‖∏ᶠ u : ℂ, (0 - u) ^ (d u)‖ = Real.log ‖∏ u ∈ S, (0 - u) ^ (d u)‖ := by rw [hprod_eq]
      _ = Real.log (∏ u ∈ S, ‖(0 - u) ^ (d u)‖) := by
          rw [pf_norm_finset_prod S (fun u => (0 - u) ^ (d u))]
      _ = ∑ u ∈ S, Real.log ‖(0 - u) ^ (d u)‖ := by
          exact Real.log_prod (fun u hu => (hfac_pos u hu).ne')
      _ = ∑ u ∈ S, ((d u : ℤ) : ℝ) * Real.log ‖(0 : ℂ) - u‖ := by
          apply Finset.sum_congr rfl
          intro u hu
          have hpow : ‖(0 - u) ^ (d u)‖ = ‖(0 : ℂ) - u‖ ^ (d u) := pf_norm_zpow_eq (0 - u) (d u)
          rw [hpow]
          have hlog : Real.log (‖(0 : ℂ) - u‖ ^ (d u)) = (d u : ℝ) * Real.log ‖(0 : ℂ) - u‖ :=
            pf_log_zpow (hprod_pos_fac u hu) (hd_nonneg u)
          rw [hlog]
  have hlog_abs :
      |Real.log ‖∏ᶠ u : ℂ, (0 - u) ^ (d u)‖| ≤ (∑ u ∈ S, ((d u : ℤ) : ℝ)) * B := by
    rw [hlog_all]
    calc
      |∑ u ∈ S, ((d u : ℤ) : ℝ) * Real.log ‖(0 : ℂ) - u‖|
          ≤ ∑ u ∈ S, |((d u : ℤ) : ℝ) * Real.log ‖(0 : ℂ) - u‖| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ u ∈ S, ((d u : ℤ) : ℝ) * |Real.log ‖(0 : ℂ) - u‖| := by
          apply Finset.sum_congr rfl
          intro u hu
          have hdn : 0 ≤ ((d u : ℤ) : ℝ) := by exact_mod_cast (hd_nonneg u)
          rw [abs_mul, abs_of_nonneg hdn]
      _ ≤ ∑ u ∈ S, ((d u : ℤ) : ℝ) * B := by
          refine Finset.sum_le_sum (fun u hu => ?_)
          have hb := hlog_per u hu
          have hdn : 0 ≤ ((d u : ℤ) : ℝ) := by exact_mod_cast (hd_nonneg u)
          exact mul_le_mul_of_nonneg_left (abs_le.mpr hb) hdn
      _ = (∑ u ∈ S, ((d u : ℤ) : ℝ)) * B := by rw [Finset.sum_mul]
  have hfin_eq : (∑ᶠ u : ℂ, ((d u : ℤ) : ℝ)) = ∑ u ∈ S, ((d u : ℤ) : ℝ) := by
    refine finsum_eq_sum_of_support_subset (fun u : ℂ => ((d u : ℤ) : ℝ)) ?_
    intro u hu
    rw [Function.mem_support] at hu
    have hdne : d u ≠ 0 := by
      intro hd0
      exact hu (by simp [hd0])
    exact (hmemS u).mpr hdne
  have hZ : pfZ N χ T = ∑ᶠ u : ℂ, ((d u : ℤ) : ℝ) := by
    dsimp [pfZ, d, Λc]
  calc
    |Real.log ‖pfP N χ T 0‖| = |Real.log ‖∏ᶠ u : ℂ, (0 - u) ^ (d u)‖| := by
        dsimp [pfP, d, Λc]
    _ ≤ (∑ᶠ u : ℂ, ((d u : ℤ) : ℝ)) * B := by
        rw [hfin_eq]
        exact hlog_abs
    _ = (pfZ N χ T) * (Real.log T + |Real.log δ₀|) := by
        rw [hZ]

/-! ## Constants witnessing growth / zero-count / zero-separation -/

/-- growth constant (nonneg) for |Λ| on circles. -/
noncomputable def pfr_gc {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    (hχprim : χ.IsPrimitive) : ℝ :=
  max ((Commons.NumberTheory.Linnik.completedL_growth_circle χ hχ hχprim).choose) 0

/-- zero-count constant (nonneg). -/
noncomputable def pfr_zc {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    (hχprim : χ.IsPrimitive) : ℝ :=
  max ((Commons.NumberTheory.Linnik.completedL_zeroCount χ hχ hχprim).choose) 0

/-- lower bound for |zeros|. -/
noncomputable def pfr_delta {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    (hχprim : χ.IsPrimitive) : ℝ :=
  (pf_zeros_ge_delta χ hχ hχprim).choose

lemma pfr_gc_nonneg {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    (hχprim : χ.IsPrimitive) : 0 ≤ pfr_gc χ hχ hχprim := by
  dsimp [pfr_gc]
  exact le_max_right _ 0

lemma pfr_zc_nonneg {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    (hχprim : χ.IsPrimitive) : 0 ≤ pfr_zc χ hχ hχprim := by
  dsimp [pfr_zc]
  exact le_max_right _ 0

lemma pfr_delta_spec {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    (hχprim : χ.IsPrimitive) :
    0 < pfr_delta χ hχ hχprim ∧ pfr_delta χ hχ hχprim ≤ 1 ∧
      ∀ u : ℂ, DirichletCharacter.completedLFunction χ u = 0 →
        pfr_delta χ hχ hχprim ≤ ‖u‖ := by
  exact (pf_zeros_ge_delta χ hχ hχprim).choose_spec

lemma pfr_gc_spec {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    (hχprim : χ.IsPrimitive) : ∀ R : ℝ, 2 ≤ R → ∀ z : ℂ, ‖z‖ = R →
      ‖DirichletCharacter.completedLFunction χ z‖ ≤
        rexp (pfr_gc χ hχ hχprim * R * L_N N R) := by
  intro R hR z hz
  let c : ℝ := (Commons.NumberTheory.Linnik.completedL_growth_circle χ hχ hχprim).choose
  have hc : ‖DirichletCharacter.completedLFunction χ z‖ ≤
      rexp (c * R * (Real.log (R + 2) + Real.log (N : ℝ) + 2)) := by
    simpa using ((Commons.NumberTheory.Linnik.completedL_growth_circle χ hχ hχprim).choose_spec R hR z hz)
  have hle : c * R * L_N N R ≤ pfr_gc χ hχ hχprim * R * L_N N R := by
    have hR0 : 0 ≤ R := by linarith only [hR]
    have hL : 0 ≤ L_N N R := le_of_lt (pf_L_pos (N := N) hR0)
    dsimp [pfr_gc]
    have hcm : c ≤ max c 0 := le_max_left c 0
    calc
      c * R * L_N N R = (c * R) * L_N N R := by ring
      _ ≤ (max c 0 * R) * L_N N R := by
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcm hR0) hL
  refine le_trans hc ?_
  rw [Real.exp_le_exp]
  have hlog : Real.log (R + 2) + Real.log (N : ℝ) + 2 = L_N N R := by
    rfl
  rw [hlog]
  exact hle

lemma pfr_zc_spec {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    (hχprim : χ.IsPrimitive) : ∀ R : ℝ, 2 ≤ R →
      (∑ᶠ u : ℂ, (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
          (closedBall (0 : ℂ) R)) u : ℤ) : ℝ)) ≤
        pfr_zc χ hχ hχprim * R * L_N N R := by
  intro R hR
  let c : ℝ := (Commons.NumberTheory.Linnik.completedL_zeroCount χ hχ hχprim).choose
  have hc : (∑ᶠ u : ℂ, (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
          (closedBall (0 : ℂ) R)) u : ℤ) : ℝ)) ≤
      c * R * (Real.log (R + 2) + Real.log (N : ℝ) + 2) := by
    simpa using ((Commons.NumberTheory.Linnik.completedL_zeroCount χ hχ hχprim).choose_spec R hR)
  have hle : c * R * L_N N R ≤ pfr_zc χ hχ hχprim * R * L_N N R := by
    have hR0 : 0 ≤ R := by linarith only [hR]
    have hL : 0 ≤ L_N N R := le_of_lt (pf_L_pos (N := N) hR0)
    dsimp [pfr_zc]
    have hcm : c ≤ max c 0 := le_max_left c 0
    calc
      c * R * L_N N R = (c * R) * L_N N R := by ring
      _ ≤ (max c 0 * R) * L_N N R := by
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcm hR0) hL
  have hlog : Real.log (R + 2) + Real.log (N : ℝ) + 2 = L_N N R := by
    rfl
  calc
    (∑ᶠ u : ℂ, (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
        (closedBall (0 : ℂ) R)) u : ℤ) : ℝ)) ≤ c * R * (Real.log (R + 2) + Real.log (N : ℝ) + 2) := hc
    _ = c * R * L_N N R := by rw [hlog]
    _ ≤ pfr_zc χ hχ hχprim * R * L_N N R := hle

/-- The log-cofactor scale `M0` at a good radius. -/
noncomputable def pfr_M0 {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    (hχprim : χ.IsPrimitive) (A T : ℝ) : ℝ :=
  pfr_gc χ hχ hχprim * T * L_N N T
  + 2 * Real.log (L_N N A) * pfr_zc χ hχ hχprim * T * L_N N T
  + |Real.log ‖DirichletCharacter.completedLFunction χ 0‖|
  + pfr_zc χ hχ hχprim * T * L_N N T * (Real.log T + |Real.log (pfr_delta χ hχ hχprim)|)
  + 1

lemma pfr_M0_nonneg {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    (hχprim : χ.IsPrimitive) {A T : ℝ} (hA : 0 ≤ A) (hT1 : 1 ≤ T) :
    0 ≤ pfr_M0 χ hχ hχprim A T := by
  have hgc : 0 ≤ pfr_gc χ hχ hχprim := pfr_gc_nonneg χ hχ hχprim
  have hzc : 0 ≤ pfr_zc χ hχ hχprim := pfr_zc_nonneg χ hχ hχprim
  have hT0 : 0 ≤ T := by linarith only [hT1]
  have hLT : 0 ≤ L_N N T := le_of_lt (pf_L_pos (N := N) hT0)
  have hLA : 0 ≤ L_N N A := le_of_lt (pf_L_pos (N := N) hA)
  have hlogLA : 0 ≤ Real.log (L_N N A) := by
    have hLA1 : 1 ≤ L_N N A := by linarith [pf_L_ge_two (N := N) hA]
    exact Real.log_nonneg hLA1
  have hlogT : 0 ≤ Real.log T := Real.log_nonneg hT1
  have h1 : 0 ≤ pfr_gc χ hχ hχprim * T * L_N N T := by positivity
  have h2 : 0 ≤ 2 * Real.log (L_N N A) * pfr_zc χ hχ hχprim * T * L_N N T := by positivity
  have h3 : 0 ≤ |Real.log ‖DirichletCharacter.completedLFunction χ 0‖| := abs_nonneg _
  have h4 : 0 ≤ pfr_zc χ hχ hχprim * T * L_N N T * (Real.log T + |Real.log (pfr_delta χ hχ hχprim)|) := by
    have hb : 0 ≤ Real.log T + |Real.log (pfr_delta χ hχ hχprim)| := by positivity
    positivity
  dsimp [pfr_M0]
  nlinarith

/-- Cofactor bound at a good radius: factorization of `Λ` on `ball 0 (T+ε)` with
`log‖g‖ ≤ M0` on `ball 0 T` and `|log‖g 0‖| ≤ M0`, where `M0 = pfr_M0 χ hχ hχprim A T`. -/
lemma pfr_cofactor_bound {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    (hχprim : χ.IsPrimitive) {A T : ℝ} (hA : 0 ≤ A) (hTpos : 0 < T) (hT2 : 2 ≤ T)
    (hmargin : ∀ u : ℂ, DirichletCharacter.completedLFunction χ u = 0 →
      (L_N N A) ^ 2 * |‖u‖ - T| ≥ 1) :
    ∃ (g : ℂ → ℂ) (ε : ℝ), 0 < ε ∧
      AnalyticOnNhd ℂ g (ball 0 (T + ε)) ∧
      (∀ w : ℂ, w ∈ ball 0 (T + ε) → g w ≠ 0) ∧
      (∀ z : ℂ, z ∈ ball 0 (T + ε) →
        DirichletCharacter.completedLFunction χ z =
          pfP N χ T z * g z) ∧
      (∀ w : ℂ, w ∈ ball 0 T → Real.log ‖g w‖ ≤ pfr_M0 χ hχ hχprim A T) ∧
      |Real.log ‖g 0‖| ≤ pfr_M0 χ hχ hχprim A T := by
  classical
  let Λc : ℂ → ℂ := DirichletCharacter.completedLFunction χ
  let gc : ℝ := pfr_gc χ hχ hχprim
  let zc : ℝ := pfr_zc χ hχ hχprim
  let δ₀ : ℝ := pfr_delta χ hχ hχprim
  let LT : ℝ := L_N N T
  let LA : ℝ := L_N N A
  let Q1 : ℝ := gc * T * LT
  let Q2 : ℝ := (2 * Real.log LA) * (zc * T * LT)
  let Q3 : ℝ := |Real.log ‖Λc 0‖|
  let Q4 : ℝ := zc * T * LT * (Real.log T + |Real.log δ₀|)
  let M0 : ℝ := Q1 + Q2 + Q3 + Q4 + 1
  have hΛ0 : Λc 0 ≠ 0 := by simpa [Λc] using (completedLFunction_zero_ne_zero χ hχ hχprim)
  have hΛdiff : Differentiable ℂ Λc := by simpa [Λc] using (differentiable_completedLFunction hχ)
  have hLApos : 0 < LA := pf_L_pos (N := N) hA
  have hLTpos : 0 < LT := pf_L_pos (N := N) (le_of_lt hTpos)
  have hcirc : ∀ u : ℂ, ‖u‖ = T → Λc u ≠ 0 := by
    intro u hu hzu
    have hmm := hmargin u (by simpa [Λc] using hzu)
    have hL2 : 0 < (L_N N A) ^ 2 := by positivity
    have hzero : |‖u‖ - T| = 0 := by simp [hu]
    have hb : (1 : ℝ) ≤ 0 := by simpa [hzero, mul_zero] using hmm
    linarith only [hb]
  rcases factorization_open (f := Λc) (R := T) hTpos hΛdiff hΛ0 hcirc with ⟨g, ε, hε, hg_an, hg_nz, hfac⟩
  have hg_nz_T : ∀ w : ℂ, w ∈ ball 0 T → g w ≠ 0 := by
    intro w hw
    have hwε : w ∈ ball 0 (T + ε) := by
      rw [mem_ball_zero_iff] at hw ⊢
      linarith only [hε, hw]
    exact hg_nz w hwε
  have hM0_eq : M0 = pfr_M0 χ hχ hχprim A T := by
    dsimp [M0, Q1, Q2, Q3, Q4, gc, zc, δ₀, LT, LA, Λc, pfr_M0]
    ring
  have hQ3 : 0 ≤ Q3 := by dsimp [Q3]; exact abs_nonneg _
  have hQ4 : 0 ≤ Q4 := by
    dsimp [Q4]
    have hlogT0 : 0 ≤ Real.log T := Real.log_nonneg (by linarith only [hT2] : (1 : ℝ) ≤ T)
    have hzc0 : 0 ≤ zc := pfr_zc_nonneg χ hχ hχprim
    positivity
  have hQ1 : 0 ≤ Q1 := by
    have hgc0 : 0 ≤ gc := by dsimp [gc]; exact pfr_gc_nonneg χ hχ hχprim
    have hT0 : 0 ≤ T := le_of_lt hTpos
    dsimp [Q1]
    positivity
  have hQ2 : 0 ≤ Q2 := by
    have hzc0 : 0 ≤ zc := by dsimp [zc]; exact pfr_zc_nonneg χ hχ hχprim
    have hlogLA0 : 0 ≤ Real.log (L_N N A) := by
      have hA1 : 1 ≤ L_N N A := by linarith [pf_L_ge_two (N := N) hA]
      exact Real.log_nonneg hA1
    dsimp [Q2, zc, LA]
    positivity
  have hQ1Q2_le_M0 : Q1 + Q2 ≤ M0 := by
    dsimp [M0]
    linarith only [hQ3, hQ4]
  have hQ34_le_M0 : Q3 + Q4 ≤ M0 := by
    dsimp [M0]
    linarith only [hQ1, hQ2]
  -- boundary bound on the sphere
  have hbnd_ζ : ∀ ζ : ℂ, ‖ζ‖ = T → Real.log ‖g ζ‖ ≤ Q1 + Q2 := by
    intro ζ hζ
    have hζε : ζ ∈ ball 0 (T + ε) := by
      rw [mem_ball_zero_iff]
      linarith only [hζ, hε]
    have hΛζ : Λc ζ ≠ 0 := hcirc ζ hζ
    have hPζ : pfP N χ T ζ ≠ 0 := pf_P_ne_zero_circle χ hχ hχprim hTpos (by intro u hu; simpa [Λc] using hcirc u hu) (hζ := hζ)
    have hgζ : g ζ ≠ 0 := hg_nz ζ hζε
    have hfacζ := hfac ζ hζε
    have hlog_mul : Real.log ‖Λc ζ‖ = Real.log ‖pfP N χ T ζ‖ + Real.log ‖g ζ‖ := by
      have h1 : ‖Λc ζ‖ = ‖pfP N χ T ζ * g ζ‖ := by
        rw [hfacζ]
        congr 1
      rw [h1]
      exact pf_log_eq_of_mul hPζ hgζ
    have hlogΛ : Real.log ‖Λc ζ‖ ≤ gc * T * LT := by
      have hb := pf_LogΛ_bound χ (T := T) (hT2 := hT2) (gc := gc)
        (by
          intro R' hR' z' hz'
          exact pfr_gc_spec χ hχ hχprim R' hR' z' hz')
        (hζ := hζ) (hζnz := by simpa [Λc] using hΛζ)
      simpa [gc, LT, Λc] using hb
    have hfaclow : -Real.log ‖pfP N χ T ζ‖ ≤ (2 * Real.log LA) * pfZ N χ T := by
      have hb := pf_fac_log_lower (χ := χ) (hχ := hχ) (A := A) (T := T) hA hTpos
        (by intro u hu; simpa [Λc] using (hmargin u hu)) (hζ := hζ)
      simpa [pfP, pfZ, LA, Λc] using hb
    have hZle : pfZ N χ T ≤ zc * T * LT := by
      have hb := pfr_zc_spec χ hχ hχprim T hT2
      simpa [pfZ, zc, LT, Λc] using hb
    have hmain : Real.log ‖g ζ‖ ≤ gc * T * LT + (2 * Real.log LA) * pfZ N χ T := by
      have hstep : Real.log ‖g ζ‖ = Real.log ‖Λc ζ‖ - Real.log ‖pfP N χ T ζ‖ := by
        rw [hlog_mul]
        ring
      rw [hstep]
      have h1 : Real.log ‖Λc ζ‖ ≤ gc * T * LT := hlogΛ
      have h2 : -Real.log ‖pfP N χ T ζ‖ ≤ (2 * Real.log LA) * pfZ N χ T := hfaclow
      linarith
    have hstep2 : gc * T * LT + (2 * Real.log LA) * pfZ N χ T ≤ Q1 + Q2 := by
      dsimp [Q1, Q2]
      have hz0 : 0 ≤ 2 * Real.log LA := by
        have hLA1 : 1 ≤ LA := by dsimp [LA]; linarith [pf_L_ge_two (N := N) hA]
        have hlog : 0 ≤ Real.log LA := Real.log_nonneg hLA1
        positivity
      nlinarith
    exact le_trans hmain hstep2
  -- ball bound via maximum modulus on the frontier
  have hbnd_ball : ∀ w : ℂ, w ∈ ball 0 T → Real.log ‖g w‖ ≤ M0 := by
    intro w hw
    have hcl : DifferentiableOn ℂ g (closedBall 0 T) := by
      intro x hx
      have hxε : x ∈ ball 0 (T + ε) := by
        rw [mem_ball_zero_iff]
        have hxT : ‖x‖ ≤ T := by simpa [Metric.mem_closedBall, dist_eq_norm] using hx
        linarith only [hε, hxT]
      exact (hg_an.differentiableOn.differentiableAt (isOpen_ball.mem_nhds hxε)).differentiableWithinAt
    have hdiffCl : DiffContOnCl ℂ g (ball 0 T) := by
      refine DifferentiableOn.diffContOnCl ?_
      simpa [closure_ball (0 : ℂ) (ne_of_gt hTpos)] using hcl
    have hfront : ∀ ζ : ℂ, ζ ∈ frontier (ball 0 T) → ‖g ζ‖ ≤ rexp M0 := by
      intro ζ hζf
      rw [frontier_ball (0 : ℂ) (ne_of_gt hTpos), Metric.mem_sphere, dist_eq_norm] at hζf
      have hζ : ‖ζ‖ = T := by simpa using hζf
      have hb := hbnd_ζ ζ hζ
      have hleM : Real.log ‖g ζ‖ ≤ M0 := le_trans hb hQ1Q2_le_M0
      have hgζnz : g ζ ≠ 0 := by
        have hζε : ζ ∈ ball 0 (T + ε) := by rw [mem_ball_zero_iff]; linarith only [hζ, hε]
        exact hg_nz ζ hζε
      have hnormpos : 0 < ‖g ζ‖ := norm_pos_iff.mpr hgζnz
      calc
        ‖g ζ‖ = rexp (Real.log ‖g ζ‖) := by rw [Real.exp_log hnormpos]
        _ ≤ rexp M0 := Real.exp_le_exp.mpr hleM
    have hwT : ‖w‖ < T := by simpa [mem_ball_zero_iff] using hw
    have hwcl : w ∈ closure (ball 0 T) := by
      rw [closure_ball (0 : ℂ) (ne_of_gt hTpos), Metric.mem_closedBall, dist_eq_norm]
      simpa using hwT.le
    have hnorm : ‖g w‖ ≤ rexp M0 := Complex.norm_le_of_forall_mem_frontier_norm_le
      Metric.isBounded_ball hdiffCl hfront hwcl
    have hgwpos : 0 < ‖g w‖ := norm_pos_iff.mpr (hg_nz_T w hw)
    have hlogle : Real.log ‖g w‖ ≤ Real.log (rexp M0) := Real.log_le_log hgwpos hnorm
    rwa [Real.log_exp] at hlogle
  -- origin bound
  have h0ε : (0 : ℂ) ∈ ball 0 (T + ε) := by
    rw [mem_ball_zero_iff]
    simp
    positivity
  have hfac0 := hfac 0 h0ε
  have hP0nz : pfP N χ T 0 ≠ 0 := by
    have hmul0 : pfP N χ T 0 * g 0 ≠ 0 := by
      change ¬((∏ᶠ u : ℂ, (0 - u) ^ (divisor Λc (closedBall (0 : ℂ) T)) u) * g 0 = 0)
      rw [← hfac0]
      exact hΛ0
    exact (mul_ne_zero_iff.mp hmul0).1
  have hg0nz : g 0 ≠ 0 := hg_nz 0 h0ε
  have hlog_mul0 : Real.log ‖Λc 0‖ = Real.log ‖pfP N χ T 0‖ + Real.log ‖g 0‖ := by
    have h1 : ‖Λc 0‖ = ‖pfP N χ T 0 * g 0‖ := by
      rw [hfac0]
      congr 1
    rw [h1]
    exact pf_log_eq_of_mul hP0nz hg0nz
  have hP0_bound : |Real.log ‖pfP N χ T 0‖| ≤ (pfZ N χ T) * (Real.log T + |Real.log δ₀|) := by
    have hδspec := pfr_delta_spec χ hχ hχprim
    exact pf_P0_log_bound χ hχ (hT := by linarith only [hT2]) δ₀ hδspec.1 (by intro u hu; simpa [δ₀, Λc] using (hδspec.2.2 u hu))
  have hlogg0 : |Real.log ‖g 0‖| ≤ Q3 + Q4 := by
    have hrew : Real.log ‖g 0‖ = Real.log ‖Λc 0‖ - Real.log ‖pfP N χ T 0‖ := by
      rw [hlog_mul0]
      ring
    have h1 : |Real.log ‖Λc 0‖ - Real.log ‖pfP N χ T 0‖| ≤ Q3 + zc * T * LT * (Real.log T + |Real.log δ₀|) := by
      have hA1 : |Real.log ‖Λc 0‖ - Real.log ‖pfP N χ T 0‖| ≤
          |Real.log ‖Λc 0‖| + |Real.log ‖pfP N χ T 0‖| := by
        simpa [sub_eq_add_neg, abs_neg] using (abs_add_le (Real.log ‖Λc 0‖) (-Real.log ‖pfP N χ T 0‖))
      have hZle : pfZ N χ T ≤ zc * T * LT := by
        have hb := pfr_zc_spec χ hχ hχprim T hT2
        simpa [pfZ, zc, LT, Λc] using hb
      have hb1 : |Real.log ‖pfP N χ T 0‖| ≤ zc * T * LT * (Real.log T + |Real.log δ₀|) := by
        have hb0 : (pfZ N χ T) * (Real.log T + |Real.log δ₀|) ≤
            (zc * T * LT) * (Real.log T + |Real.log δ₀|) := by
          have hnon : 0 ≤ Real.log T + |Real.log δ₀| := by
            have hlogT0 : 0 ≤ Real.log T := Real.log_nonneg (by linarith only [hT2] : (1 : ℝ) ≤ T)
            positivity
          exact mul_le_mul_of_nonneg_right hZle hnon
        exact le_trans hP0_bound hb0
      dsimp [Q3]
      linarith
    have hrew2 : Q3 + zc * T * LT * (Real.log T + |Real.log δ₀|) = Q3 + Q4 := by
      rfl
    rw [hrew]
    rw [hrew2]
    exact h1
  have horigin : |Real.log ‖g 0‖| ≤ M0 := by
    exact le_trans hlogg0 hQ34_le_M0
  refine ⟨g, ε, hε, hg_an, hg_nz, hfac, ?_, ?_⟩
  · intro w hw
    exact le_trans (hbnd_ball w hw) (le_of_eq hM0_eq)
  · exact le_trans horigin (le_of_eq hM0_eq)

/-- `log T ≤ 1 + log-scale(A)` when `1 ≤ A`, `A ≤ T`, `T ≤ 2A`. -/
lemma pfr_logT_le {N : ℕ} [NeZero N] {A T : ℝ} (hA1 : 1 ≤ A) (hT2A : T ≤ 2 * A) (hAT : A ≤ T) :
    Real.log T ≤ 1 + L_N N A := by
  have hApos : 0 < A := by linarith only [hA1]
  have hTpos : 0 < T := by linarith only [hA1, hAT]
  have h1 : Real.log T ≤ Real.log (2 * A) := by
    apply Real.log_le_log hTpos
    exact hT2A
  have h2 : Real.log (2 * A) ≤ 1 + Real.log A := by
    calc
      Real.log (2 * A) = Real.log 2 + Real.log A := by
        rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt hApos)]
      _ ≤ 1 + Real.log A := by
        have hlog2 : Real.log 2 ≤ 1 := by
          have h := Real.log_le_sub_one_of_pos (x := (2 : ℝ)) (by norm_num : (0 : ℝ) < 2)
          linarith only [h]
        linarith only [hlog2]
  have h3 : Real.log A ≤ Real.log (A + 2) := by
    apply Real.log_le_log (by linarith only [hA1] : 0 < A)
    linarith only []
  have h4 : Real.log (A + 2) ≤ L_N N A := by
    dsimp [L_N]
    have hlogN : 0 ≤ Real.log (N : ℝ) := logN_nonneg (N := N)
    linarith only [hlogN]
  linarith only [h1, h2, h3, h4]

/-- `T·log-scale(T) ≤ 4·A·log-scale(A)` when `1 ≤ A ≤ T ≤ 2A`. -/
lemma pfr_mul_bound {N : ℕ} [NeZero N] {A T : ℝ} (hA1 : 1 ≤ A) (hAT : A ≤ T) (hT2A : T ≤ 2 * A) :
    T * L_N N T ≤ 4 * A * L_N N A := by
  have hT0 : 0 ≤ T := by linarith only [hA1, hAT]
  have h2A0 : 0 ≤ 2 * A := by linarith only [hA1]
  have hLT0 : 0 ≤ L_N N T := le_of_lt (pf_L_pos (N := N) hT0)
  have hLTle : L_N N T ≤ L_N N (2 * A) := pf_L_mono (N := N) hT0 hT2A
  have hLTle2 : L_N N T ≤ 2 * L_N N A := by
    calc
      L_N N T ≤ L_N N (2 * A) := hLTle
      _ ≤ 2 * L_N N A := pf_L_two_mul_le (N := N) hA1
  calc
    T * L_N N T ≤ (2 * A) * L_N N T := mul_le_mul_of_nonneg_right hT2A hLT0
    _ ≤ (2 * A) * (2 * L_N N A) := mul_le_mul_of_nonneg_left hLTle2 h2A0
    _ = 4 * A * L_N N A := by ring

/-- Coefficient `C0` in the `M0` upper bound. -/
noncomputable def pfr_C0 {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    (hχprim : χ.IsPrimitive) : ℝ :=
  4 * pfr_gc χ hχ hχprim + 8 * pfr_zc χ hχ hχprim +
    4 * pfr_zc χ hχ hχprim * (2 + |Real.log (pfr_delta χ hχ hχprim)|)

/-- Coefficient `C1` in the `M0` upper bound. -/
noncomputable def pfr_C1 {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    (hχprim : χ.IsPrimitive) : ℝ :=
  |Real.log ‖DirichletCharacter.completedLFunction χ 0‖| + 2

/-- `M0(A,T) ≤ C0·A·(log-scale A)² + C1` for `1 ≤ A ≤ T ≤ 2A`. -/
lemma pfr_M0_le {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    (hχprim : χ.IsPrimitive) {A T : ℝ} (hA1 : 1 ≤ A) (hAT : A ≤ T) (hT2A : T ≤ 2 * A) :
    pfr_M0 χ hχ hχprim A T ≤ pfr_C0 χ hχ hχprim * A * (L_N N A) ^ 2 + pfr_C1 χ hχ hχprim := by
  classical
  let gc : ℝ := pfr_gc χ hχ hχprim
  let zc : ℝ := pfr_zc χ hχ hχprim
  let del : ℝ := pfr_delta χ hχ hχprim
  let LA : ℝ := L_N N A
  have hA0 : 0 ≤ A := by linarith only [hA1]
  have hT0 : 0 ≤ T := by linarith only [hA1, hAT]
  have hLA0 : 0 ≤ LA := le_of_lt (pf_L_pos (N := N) hA0)
  have hLA1 : 1 ≤ LA := by dsimp [LA]; linarith [pf_L_ge_two (N := N) hA0]
  have hgc0 : 0 ≤ gc := by dsimp [gc]; exact pfr_gc_nonneg χ hχ hχprim
  have hzc0 : 0 ≤ zc := by dsimp [zc]; exact pfr_zc_nonneg χ hχ hχprim
  have hlogLA0 : 0 ≤ Real.log (L_N N A) := Real.log_nonneg (by linarith only [hLA1] : 1 ≤ L_N N A)
  have hlogT0 : 0 ≤ Real.log T := Real.log_nonneg (by linarith only [hA1, hAT])
  have hLT0 : 0 ≤ L_N N T := le_of_lt (pf_L_pos (N := N) hT0)
  have hlogLAle : Real.log (L_N N A) ≤ LA := by
    dsimp [LA]
    exact pf_log_L_le_L (N := N) hA0
  have hLT2 : L_N N T ≤ 2 * LA := by
    dsimp [LA]
    have hm := pf_L_mono (N := N) hT0 hT2A
    have h2 := pf_L_two_mul_le (N := N) hA1
    calc
      L_N N T ≤ L_N N (2 * A) := hm
      _ ≤ 2 * L_N N A := h2
  have hTL4 : T * L_N N T ≤ 4 * A * LA := by
    dsimp [LA]
    exact pfr_mul_bound (N := N) hA1 hAT hT2A
  have hlogTle : Real.log T ≤ 1 + LA := by
    dsimp [LA]
    exact pfr_logT_le (N := N) hA1 hT2A hAT
  have hlogd : |Real.log del| ≤ |Real.log del| * LA := by
    have h : 1 ≤ LA := hLA1
    rw [mul_comm]
    exact le_mul_of_one_le_left (abs_nonneg _) h
  have hLTleLA2 : Real.log T + |Real.log del| ≤ LA * (2 + |Real.log del|) := by
    linarith only [hlogTle, hlogd, hLA1]
  -- term bounds
  have hterm1 : gc * T * L_N N T ≤ 4 * gc * A * LA ^ 2 := by
    have h1 := mul_le_mul_of_nonneg_left hTL4 hgc0   -- gc·(T·LT) ≤ gc·(4·A·LA)
    have h2 : gc * (4 * A * LA) ≤ gc * (4 * A * LA) * LA := by
      have h4gcA0 : 0 ≤ gc * (4 * A * LA) := by positivity
      exact le_mul_of_one_le_right h4gcA0 hLA1
    dsimp [LA] at h2
    linarith only [h1, h2]
  have hterm2 : 2 * Real.log (L_N N A) * zc * T * L_N N T ≤ 8 * zc * A * (L_N N A) ^ 2 := by
    have hzcT : zc * (T * L_N N T) ≤ zc * (4 * A * LA) := mul_le_mul_of_nonneg_left hTL4 hzc0
    have hlog2 : (2 * Real.log (L_N N A)) ≤ (2 * LA) := by linarith only [hlogLAle]
    have hpart : (2 * LA) * (zc * (4 * A * LA)) ≤ 8 * zc * A * LA ^ 2 := by
      have h1 : 0 ≤ 2 * LA := by positivity
      have h2 : 0 ≤ zc * (4 * A * LA) := by positivity
      linarith only []
    have hzcT0 : 0 ≤ zc * (T * L_N N T) := by positivity
    have h2LA0 : 0 ≤ 2 * LA := by positivity
    have hprod : (2 * Real.log (L_N N A)) * (zc * (T * L_N N T)) ≤ (2 * LA) * (zc * (4 * A * LA)) :=
      mul_le_mul hlog2 hzcT hzcT0 h2LA0
    dsimp [LA] at hpart
    linarith only [hprod, hpart]
  have hterm4 : zc * T * L_N N T * (Real.log T + |Real.log del|)
      ≤ 4 * zc * (2 + |Real.log del|) * A * (L_N N A) ^ 2 := by
    have hzcT : zc * (T * L_N N T) ≤ zc * (4 * A * LA) := mul_le_mul_of_nonneg_left hTL4 hzc0
    have hx0 : 0 ≤ Real.log T + |Real.log del| := by positivity
    have hX : Real.log T + |Real.log del| ≤ LA * (2 + |Real.log del|) := hLTleLA2
    have hzX0 : 0 ≤ LA * (2 + |Real.log del|) := by positivity
    have h1 : (zc * (T * L_N N T)) * (Real.log T + |Real.log del|) ≤
        (zc * (4 * A * LA)) * (LA * (2 + |Real.log del|)) :=
        mul_le_mul hzcT hX hx0 (by positivity : 0 ≤ zc * (4 * A * LA))
    have h2 : (zc * (4 * A * LA)) * (LA * (2 + |Real.log del|)) ≤
        4 * zc * (2 + |Real.log del|) * A * (L_N N A) ^ 2 := by
      have heq : (zc * (4 * A * LA)) * (LA * (2 + |Real.log del|)) =
          4 * zc * (2 + |Real.log del|) * A * LA ^ 2 := by ring
      have hLA0' : 0 ≤ LA ^ 2 := by positivity
      have hzc0' : 0 ≤ zc := hzc0
      have hd0 : 0 ≤ 2 + |Real.log del| := by positivity
      have hA0' : 0 ≤ A := hA0
      rw [heq]
    dsimp [LA] at h2
    linarith only [h1, h2]
  have hq3 : |Real.log ‖DirichletCharacter.completedLFunction χ 0‖| ≤
      |Real.log ‖DirichletCharacter.completedLFunction χ 0‖| := le_rfl
  calc
    pfr_M0 χ hχ hχprim A T
        = pfr_gc χ hχ hχprim * T * L_N N T
            + 2 * Real.log (L_N N A) * pfr_zc χ hχ hχprim * T * L_N N T
            + |Real.log ‖DirichletCharacter.completedLFunction χ 0‖|
            + pfr_zc χ hχ hχprim * T * L_N N T * (Real.log T + |Real.log (pfr_delta χ hχ hχprim)|)
            + 1 := by
            dsimp [pfr_M0]
    _ ≤ 4 * gc * A * LA ^ 2 + 8 * zc * A * LA ^ 2
            + |Real.log ‖DirichletCharacter.completedLFunction χ 0‖|
            + 4 * zc * (2 + |Real.log del|) * A * LA ^ 2 + 1 := by
            nlinarith [hterm1, hterm2, hterm4]
    _ ≤ pfr_C0 χ hχ hχprim * A * (L_N N A) ^ 2 + pfr_C1 χ hχ hχprim := by
            dsimp [pfr_C0, pfr_C1, gc, zc, del]
            nlinarith
/-- Partial-fraction identity (strong form) for the completed Dirichlet L-function:
`∑_{|u| ≤ R} ord(u)·(1/(s-u) + 1/u) ⟶ Λ'(s)/Λ(s) − Λ'(0)/Λ(0)` as `R → ∞`. -/
lemma pfr_pf_tendsto {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    (hχprim : χ.IsPrimitive) (s : ℂ)
    (hΛs : DirichletCharacter.completedLFunction χ s ≠ 0) :
    Tendsto (fun R : ℝ =>
        (∑ᶠ u : ℂ, (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
            (Metric.closedBall 0 R)) u : ℤ) : ℂ) * (1 / (s - u) + 1 / u)))
      atTop (nhds (deriv (DirichletCharacter.completedLFunction χ) s /
        DirichletCharacter.completedLFunction χ s -
        deriv (DirichletCharacter.completedLFunction χ) 0 /
          DirichletCharacter.completedLFunction χ 0)) := by
  classical
  let Λc : ℂ → ℂ := DirichletCharacter.completedLFunction χ
  let PF : ℝ → ℂ := fun R : ℝ =>
        ∑ᶠ u : ℂ, (((MeromorphicOn.divisor Λc (Metric.closedBall 0 R)) u : ℤ) : ℂ) * (1 / (s - u) + 1 / u)
  let K : ℂ := deriv Λc s / Λc s - deriv Λc 0 / Λc 0
  have hΛ0 : Λc 0 ≠ 0 := by simpa [Λc] using (completedLFunction_zero_ne_zero χ hχ hχprim)
  have hΛdiff : Differentiable ℂ Λc := by simpa [Λc] using (differentiable_completedLFunction hχ)
  have hΛs' : Λc s ≠ 0 := by simpa [Λc] using hΛs
  have hPF_def : ∀ R : ℝ, PF R = (∑ᶠ u : ℂ, (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
            (Metric.closedBall 0 R)) u : ℤ) : ℂ) * (1 / (s - u) + 1 / u)) := by
    intro R
    rfl
  -- the full family converges (partialFraction_conv)
  rcases partialFraction_conv χ hχ hχprim s with ⟨L, hL⟩
  have hL' : Tendsto PF atTop (𝓝 L) := by
    simpa [PF] using hL
  -- good-radius selector
  rcases goodRadius_geometric χ hχ hχprim with ⟨A₀, hA₀pos, hA₀R⟩
  let τ : ℝ → ℝ := fun A => if h : A₀ ≤ A then (hA₀R A h).choose else 1
  have hτ_spec : ∀ A : ℝ, A₀ ≤ A → A ≤ τ A ∧ τ A ≤ 2 * A ∧
      ∀ u : ℂ, Λc u = 0 → (L_N N A) ^ 2 * |‖u‖ - τ A| ≥ 1 := by
    intro A hA
    dsimp [τ]
    rw [dif_pos hA]
    have hs := (hA₀R A hA).choose_spec
    exact hs
  have hτ_top : Tendsto τ atTop atTop := by
    have hev : ∀ᶠ A : ℝ in atTop, A ≤ τ A := by
      filter_upwards [eventually_ge_atTop A₀] with A hA
      exact (hτ_spec A hA).1
    exact tendsto_atTop_mono' atTop hev tendsto_id
  -- constants for the decay bound
  let gc : ℝ := pfr_gc χ hχ hχprim
  let zc : ℝ := pfr_zc χ hχ hχprim
  let del : ℝ := pfr_delta χ hχ hχprim
  let C0 : ℝ := 4 * gc + 8 * zc + 4 * zc * (2 + |Real.log del|)
  let C1 : ℝ := |Real.log ‖Λc 0‖| + 2
  let D : ℝ := C1 + 1
  let E : ℝ → ℝ := fun A : ℝ => 1024 * ‖s‖ * (C0 * (L_N N A) ^ 2 / A + D / A ^ 2)
  have hgc0 : 0 ≤ gc := by dsimp [gc]; exact pfr_gc_nonneg χ hχ hχprim
  have hzc0 : 0 ≤ zc := by dsimp [zc]; exact pfr_zc_nonneg χ hχ hχprim
  have hC0 : 0 ≤ C0 := by dsimp [C0]; positivity
  have hC1 : 0 ≤ C1 := by dsimp [C1]; positivity
  have hdec_E : Tendsto E atTop (𝓝 0) := by
    have h1 : Tendsto (fun A : ℝ => (L_N N A) ^ 2 / A) atTop (𝓝 0) := by
      simpa [L_N] using (ell_pow_div_self_tendsto_zero (N := N) 2)
    have h1' : Tendsto (fun A : ℝ => C0 * ((L_N N A) ^ 2 / A)) atTop (𝓝 0) := by
      simpa using ((tendsto_const_nhds (x := C0)).mul h1)
    have h1'' : (fun A : ℝ => C0 * ((L_N N A) ^ 2 / A)) =ᶠ[atTop] fun A => C0 * (L_N N A) ^ 2 / A := by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with A hA
      ring
    have hA1 : Tendsto (fun A : ℝ => C0 * (L_N N A) ^ 2 / A) atTop (𝓝 0) := h1'.congr' h1''
    have hinv : Tendsto (fun A : ℝ => A⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
    have hDinv : Tendsto (fun A : ℝ => D * A⁻¹) atTop (𝓝 0) := by
      simpa using ((tendsto_const_nhds (x := D)).mul hinv)
    have hDinv2 : Tendsto (fun A : ℝ => D * A⁻¹ * A⁻¹) atTop (𝓝 0) := by
      simpa using (hDinv.mul hinv)
    have h2 : Tendsto (fun A : ℝ => D / A ^ 2) atTop (𝓝 0) := by
      have hsq : (fun A : ℝ => D / A ^ 2) =ᶠ[atTop] fun A : ℝ => D * A⁻¹ * A⁻¹ := by
        filter_upwards [eventually_gt_atTop (0 : ℝ)] with A hA
        field_simp [ne_of_gt hA]
      exact hDinv2.congr' hsq.symm
    have hsum : Tendsto (fun A : ℝ => C0 * (L_N N A) ^ 2 / A + D / A ^ 2) atTop (𝓝 0) := by
      simpa using (hA1.add h2)
    have h3 : Tendsto (fun A : ℝ => 1024 * ‖s‖ * (C0 * (L_N N A) ^ 2 / A + D / A ^ 2)) atTop (𝓝 0) := by
      simpa using ((tendsto_const_nhds (x := 1024 * ‖s‖)).mul hsum)
    have h4 : (fun A : ℝ => 1024 * ‖s‖ * (C0 * (L_N N A) ^ 2 / A + D / A ^ 2)) =ᶠ[atTop] fun A => E A := by
      filter_upwards with A
      dsimp [E]
    exact h3.congr' h4
  -- bound of the error along good radii
  have hmain : ∀ᶠ A : ℝ in atTop, ‖PF (τ A) - K‖ ≤ E A := by
    filter_upwards [eventually_ge_atTop A₀, eventually_ge_atTop (8 * ‖s‖),
      eventually_ge_atTop (2 : ℝ)] with A hA₀ hA8 hA2
    let T : ℝ := τ A
    have hspec := hτ_spec A hA₀
    have hA_le_T : A ≤ T := hspec.1
    have hT_le_2A : T ≤ 2 * A := hspec.2.1
    have hmargin : ∀ u : ℂ, Λc u = 0 → (L_N N A) ^ 2 * |‖u‖ - T| ≥ 1 := hspec.2.2
    have hA0 : 0 ≤ A := by linarith only [hA2]
    have hTpos : 0 < T := by dsimp [T]; linarith only [hA2, hspec]
    have hT2 : 2 ≤ T := by dsimp [T]; linarith only [hA2, hspec]
    have hT1 : 1 ≤ T := by linarith only [hA2, hspec]
    have hsT : ‖s‖ ≤ T / 8 := by
      dsimp [T]
      have h1 : 8 * ‖s‖ ≤ A := hA8
      have hle : A ≤ τ A := hA_le_T
      linarith only [hA8, hspec]
    rcases pfr_cofactor_bound χ hχ hχprim (A := A) (T := T) hA0 hTpos hT2 hmargin with
      ⟨g, ε, hε, hg_an, hg_nz, hfac, hgM, hg0M⟩
    have hg_an_T : AnalyticOnNhd ℂ g (ball 0 T) := by
      refine AnalyticOnNhd.mono hg_an ?_
      intro w hw
      rw [mem_ball_zero_iff] at hw ⊢
      linarith only [hε, hw]
    have hg_nz_T : ∀ w : ℂ, w ∈ ball 0 T → g w ≠ 0 := by
      intro w hw
      have hwε : w ∈ ball 0 (T + ε) := by
        rw [mem_ball_zero_iff]
        rw [mem_ball_zero_iff] at hw
        linarith only [hε, hw]
      exact hg_nz w hwε
    have hM0nn : 0 ≤ pfr_M0 χ hχ hχprim A T := pfr_M0_nonneg χ hχ hχprim (A := A) (T := T) hA0 hT1
    have hsub := pf_logDeriv_sub_of_sup (g := g) (R := T) hTpos hg_an_T hg_nz_T
      (M0 := pfr_M0 χ hχ hχprim A T) hM0nn hgM hg0M hsT
    -- decompositions at s and at 0
    have hfac_sT : ∀ z : ℂ, z ∈ ball 0 (T + ε) →
        Λc z = (∏ᶠ u : ℂ, (z - u) ^ (MeromorphicOn.divisor Λc (closedBall (0 : ℂ) T)) u) * g z := hfac
    have hdec_s := logDeriv_decompose (f := Λc) (g := g) (R := T) (ε := ε) hΛdiff hfac_sT
      (x := s) (hx := by
        rw [mem_ball_zero_iff]
        have hsT' : ‖s‖ < T := by linarith only [hsT, show 0 < T from hTpos, hA8, hA2, hspec]
        linarith only [hε, hA8, hA2, hspec]) hΛs' (hg_an s (by
          rw [mem_ball_zero_iff]
          have hsT' : ‖s‖ < T := by linarith only [hsT, show 0 < T from hTpos, hA8, hA2, hspec]
          linarith only [hε, hA8, hA2, hspec])).differentiableAt (hg_nz s (by
            rw [mem_ball_zero_iff]
            have hsT' : ‖s‖ < T := by linarith only [hsT, show 0 < T from hTpos, hA8, hA2, hspec]
            linarith only [hε, hA8, hA2, hspec]))
    have hdec_0 := logDeriv_decompose (f := Λc) (g := g) (R := T) (ε := ε) hΛdiff hfac_sT
      (x := 0) (hx := by rw [mem_ball_zero_iff]; simp; positivity) hΛ0
      (hg_an 0 (by rw [mem_ball_zero_iff]; simp; positivity)).differentiableAt
        (hg_nz 0 (by rw [mem_ball_zero_iff]; simp; positivity))
    -- finsum bookkeeping over the common support
    let dT : ℂ → ℤ := fun u => MeromorphicOn.divisor Λc (closedBall (0 : ℂ) T) u
    let cT : ℂ → ℂ := fun u => (dT u : ℂ)
    have hsuppZ : (Function.support dT).Finite := by
      dsimp [dT]
      exact pf_divisor_support_finite χ hχ T
    have hsuppC : (Function.support cT).Finite := by
      have hsub : Function.support cT ⊆ Function.support dT := by
        intro u hu
        rw [Function.mem_support] at hu
        rw [Function.mem_support]
        intro hz
        exact hu (by
          dsimp [cT]
          exact_mod_cast hz)
      exact hsuppZ.subset hsub
    let S : Finset ℂ := hsuppC.toFinset
    have hmemS : ∀ u : ℂ, u ∈ S ↔ cT u ≠ 0 := by
      intro u
      dsimp [S]
      rw [Set.Finite.mem_toFinset]
      rfl
    have hS_cT : ∀ u : ℂ, u ∉ S → cT u = 0 := by
      intro u hu
      have hne : cT u = 0 := by
        by_contra h
        exact hu ((hmemS u).mpr h)
      exact hne
    have hsub_sums : ∀ (f : ℂ → ℂ), (∀ u : ℂ, cT u = 0 → f u = 0) →
        (Function.support f) ⊆ (S : Set ℂ) := by
      intro f hf u hu
      rw [Function.mem_support] at hu
      by_contra hS'
      have hc0 : cT u = 0 := hS_cT u hS'
      exact hu (hf u hc0)
    have hPF_T : PF T = ∑ u ∈ S, cT u * (1 / (s - u) + 1 / u) := by
      have hconv : PF T = ∑ᶠ u : ℂ, cT u * (1 / (s - u) + 1 / u) := by
        dsimp [PF, cT, dT]
      rw [hconv]
      refine finsum_eq_sum_of_support_subset (fun u : ℂ => cT u * (1 / (s - u) + 1 / u)) ?_
      exact hsub_sums (fun u : ℂ => cT u * (1 / (s - u) + 1 / u)) (fun u hc0 => by simp [hc0])
    have hdec_s_sum : (∑ᶠ u : ℂ, cT u * (1 / (s - u))) = ∑ u ∈ S, cT u * (1 / (s - u)) := by
      refine finsum_eq_sum_of_support_subset (fun u : ℂ => cT u * (1 / (s - u))) ?_
      exact hsub_sums (fun u : ℂ => cT u * (1 / (s - u))) (fun u hc0 => by simp [hc0])
    have hdec_0_sum : (∑ᶠ u : ℂ, cT u * (1 / ((0 : ℂ) - u))) = ∑ u ∈ S, cT u * (1 / ((0 : ℂ) - u)) := by
      refine finsum_eq_sum_of_support_subset (fun u : ℂ => cT u * (1 / ((0 : ℂ) - u))) ?_
      exact hsub_sums (fun u : ℂ => cT u * (1 / ((0 : ℂ) - u))) (fun u hc0 => by simp [hc0])
    have hB_sum : (∑ᶠ u : ℂ, cT u * (1 / u)) = ∑ u ∈ S, cT u * (1 / u) := by
      refine finsum_eq_sum_of_support_subset (fun u : ℂ => cT u * (1 / u)) ?_
      exact hsub_sums (fun u : ℂ => cT u * (1 / u)) (fun u hc0 => by simp [hc0])
    have hsumB_neg : (∑ u ∈ S, cT u * (1 / ((0 : ℂ) - u))) = -∑ u ∈ S, cT u * (1 / u) := by
      calc
        (∑ u ∈ S, cT u * (1 / ((0 : ℂ) - u))) = ∑ u ∈ S, -(cT u * (1 / u)) := by
          apply Finset.sum_congr rfl
          intro u hu
          congr 1
          ring
        _ = -∑ u ∈ S, cT u * (1 / u) := by rw [Finset.sum_neg_distrib]
    -- the key identity PF(T) - K = -(logDeriv g s - logDeriv g 0)
    have hdec_s' : logDeriv Λc s = (∑ u ∈ S, cT u * (1 / (s - u))) + logDeriv g s := by
      rw [← hdec_s_sum]
      simpa [cT, one_div] using hdec_s
    have hdec_0' : logDeriv Λc 0 = (∑ u ∈ S, cT u * (1 / ((0 : ℂ) - u))) + logDeriv g 0 := by
      rw [← hdec_0_sum]
      simpa [cT, one_div] using hdec_0
    have hK : K = logDeriv Λc s - logDeriv Λc 0 := by
      dsimp [K]
      rw [← logDeriv_apply]
      rw [← logDeriv_apply]
    have hrel : PF T = K - (logDeriv g s - logDeriv g 0) := by
      have hterm : (fun u : ℂ => cT u * (1 / (s - u) + 1 / u)) =
          fun u : ℂ => cT u * (1 / (s - u)) + cT u * (1 / u) := by
        funext u
        ring
      calc
        PF T = (∑ u ∈ S, cT u * (1 / (s - u))) + (∑ u ∈ S, cT u * (1 / u)) := by
            rw [hPF_T]
            rw [hterm]
            rw [Finset.sum_add_distrib]
        _ = (logDeriv Λc s - logDeriv Λc 0) - (logDeriv g s - logDeriv g 0) := by
            rw [hdec_s', hdec_0', hsumB_neg]
            ring
        _ = K - (logDeriv g s - logDeriv g 0) := by
            rw [← hK]
    have hnorm_bound : ‖PF (τ A) - K‖ ≤ 1024 * (max (pfr_M0 χ hχ hχprim A T) 1) * ‖s‖ / T ^ 2 := by
      have hPFK : PF (τ A) = K - (logDeriv g s - logDeriv g 0) := by
        simpa [T] using hrel
      have hn : ‖PF (τ A) - K‖ = ‖logDeriv g s - logDeriv g 0‖ := by
        rw [hPFK]
        have hEq : (K - (logDeriv g s - logDeriv g 0)) - K = -(logDeriv g s - logDeriv g 0) := by
          abel
        rw [hEq]
        rw [norm_neg]
      rw [hn]
      exact hsub
    -- decay of the explicit bound:  ‖PF(τA) − K‖ ≤ 1024·(M0+1)·‖s‖/T² ≤ E A
    have hnorm_lin : 1024 * (max (pfr_M0 χ hχ hχprim A T) 1) * ‖s‖ / T ^ 2 ≤
        1024 * (pfr_M0 χ hχ hχprim A T + 1) * ‖s‖ / T ^ 2 := by
      have hT2nn : 0 ≤ T ^ 2 := by positivity
      have h1 : max (pfr_M0 χ hχ hχprim A T) 1 ≤ pfr_M0 χ hχ hχprim A T + 1 := by
        by_cases h : pfr_M0 χ hχ hχprim A T ≤ 1
        · simpa [max_eq_right h]
        · have hlt : 1 < pfr_M0 χ hχ hχprim A T := lt_of_not_ge h
          simpa [max_eq_left (le_of_lt hlt)]
      have h2 : 1024 * max (pfr_M0 χ hχ hχprim A T) 1 * ‖s‖ ≤
          1024 * (pfr_M0 χ hχ hχprim A T + 1) * ‖s‖ := by
        have h1024 : 0 ≤ (1024 : ℝ) := by norm_num
        have hmm := mul_le_mul_of_nonneg_left h1 h1024
        exact mul_le_mul_of_nonneg_right hmm (norm_nonneg s)
      exact div_le_div_of_nonneg_right h2 hT2nn
    have hmain' : 1024 * (pfr_M0 χ hχ hχprim A T + 1) * ‖s‖ / T ^ 2 ≤ E A := by
      have hM0le : pfr_M0 χ hχ hχprim A T ≤ pfr_C0 χ hχ hχprim * A * (L_N N A) ^ 2 + pfr_C1 χ hχ hχprim := by
        exact pfr_M0_le χ hχ hχprim (hA1 := (by linarith only [hA2] : 1 ≤ A)) hA_le_T hT_le_2A
      have hA2le : A ^ 2 ≤ T ^ 2 := by
        have hTmA : 0 ≤ T - A := by linarith only [hspec]
        have hTpA : 0 ≤ T + A := by
          have hT0' : 0 ≤ T := le_of_lt hTpos
          linarith only [hA2, hspec]
        have hprod : 0 ≤ (T - A) * (T + A) := mul_nonneg hTmA hTpA
        linarith only [hprod]
      have hdenpos : 0 < A ^ 2 := by positivity
      have hdenpos' : 0 < T ^ 2 := by positivity
      have hnumle : (pfr_M0 χ hχ hχprim A T + 1) / T ^ 2 ≤
          (pfr_C0 χ hχ hχprim * A * (L_N N A) ^ 2 + pfr_C1 χ hχ hχprim + 1) / A ^ 2 := by
        rw [div_le_div_iff₀ hdenpos' hdenpos]
        have hnn0 : 0 ≤ pfr_M0 χ hχ hχprim A T + 1 := by linarith [hM0nn]
        have hle_num : pfr_M0 χ hχ hχprim A T + 1 ≤
            pfr_C0 χ hχ hχprim * A * (L_N N A) ^ 2 + pfr_C1 χ hχ hχprim + 1 := by linarith
        have hT0 : 0 ≤ T ^ 2 := by positivity
        have hA0s : 0 ≤ A ^ 2 := by positivity
        nlinarith [hA2le, hle_num, hT0, hA0s]
      calc
        1024 * (pfr_M0 χ hχ hχprim A T + 1) * ‖s‖ / T ^ 2
            = 1024 * ‖s‖ * ((pfr_M0 χ hχ hχprim A T + 1) / T ^ 2) := by
                have hT2nz : T ^ 2 ≠ 0 := by positivity
                field_simp [hT2nz]
        _ ≤ 1024 * ‖s‖ * ((pfr_C0 χ hχ hχprim * A * (L_N N A) ^ 2 + pfr_C1 χ hχ hχprim + 1) / A ^ 2) := by
              exact mul_le_mul_of_nonneg_left hnumle (by positivity : 0 ≤ 1024 * ‖s‖)
        _ = E A := by
              dsimp [E, C0, C1, D, pfr_C0, pfr_C1, gc, zc, del, Λc]
              have hAne : A ≠ 0 := by positivity
              have hA2nz : A ^ 2 ≠ 0 := by positivity
              field_simp [hAne, hA2nz]
              ring_nf
    exact le_trans hnorm_bound (le_trans hnorm_lin hmain')

  have hnorm0 : Tendsto (fun A : ℝ => ‖PF (τ A) - K‖) atTop (𝓝 0) := by
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' (tendsto_const_nhds (x := (0 : ℝ))) hdec_E
      (by filter_upwards with A; exact norm_nonneg _) hmain
  have hseq : Tendsto (fun A : ℝ => PF (τ A)) atTop (𝓝 K) := by
    have hzero : Tendsto (fun A : ℝ => PF (τ A) - K) atTop (𝓝 0) :=
      tendsto_zero_iff_norm_tendsto_zero.mpr hnorm0
    have hadd : Tendsto (fun A : ℝ => (PF (τ A) - K) + K) atTop (𝓝 (0 + K)) := hzero.add tendsto_const_nhds
    have heq : (fun A : ℝ => (PF (τ A) - K) + K) =ᶠ[atTop] fun A : ℝ => PF (τ A) := by
      filter_upwards with A
      abel
    simpa using (hadd.congr' heq)
  have hcompL : Tendsto (fun A : ℝ => PF (τ A)) atTop (𝓝 L) := hL'.comp hτ_top
  have hLK : L = K := tendsto_nhds_unique hcompL hseq
  have hPFK : Tendsto PF atTop (𝓝 K) := by
    simpa [hLK] using hL'
  simpa [PF, Λc, K, logDeriv_apply] using hPFK


theorem completedL_pf_identity_rect {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (hχprim : χ.IsPrimitive) :
    ∃ B : ℂ, ∀ s : ℂ,
      DirichletCharacter.completedLFunction χ s ≠ 0 →
      Filter.Tendsto (fun R : ℝ =>
        (∑ᶠ u : ℂ, (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
            (Metric.closedBall 0 R)) u : ℤ) : ℂ) * (1 / (s - u) + 1 / u)))
        Filter.atTop (nhds (deriv (DirichletCharacter.completedLFunction χ) s /
          DirichletCharacter.completedLFunction χ s - B)) := by
  classical
  refine ⟨deriv (DirichletCharacter.completedLFunction χ) 0 /
    DirichletCharacter.completedLFunction χ 0, ?_⟩
  intro s hs
  exact pfr_pf_tendsto χ hχ hχprim s hs

end Commons.NumberTheory.Linnik
