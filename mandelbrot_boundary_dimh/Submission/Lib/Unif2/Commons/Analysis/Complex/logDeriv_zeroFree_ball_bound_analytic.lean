import Mathlib
import Submission.Lib.Unif2.Commons.Analysis.Complex.logDeriv_zeroFree_ball_bound

open Complex Metric Set Filter Function
open scoped Real Topology

namespace Commons.Analysis.Complex

/-! # Log-derivative bound for a zero-free analytic function on a ball

This file proves the ball-analytic variant of the commons theorem
`logDeriv_zeroFree_ball_bound`: the hypothesis there is global holomorphy
(`Differentiable ℂ g`), here we only assume `g` is analytic on the open ball
`Metric.ball c R` (`AnalyticOnNhd ℂ g (Metric.ball c R)`), which is the setting
used for functions given by power series / Euler products inside a zero-free
region.

The argument is identical to the commons one: build a holomorphic logarithm
`F` of `g` on the ball (possible because `g` is zero-free there and the ball is
simply connected — here obtained from the exactness of `deriv g / g` on the
ball, which needs only ball-analyticity), then apply Borel–Carathéodory
(`normSubLeOfReLeOnBall`) together with Cauchy's estimate on a circle
(`logDerivBoundOfReLeOnBall`).
-/

/-- Ball-analytic version of `logPrimitiveOnBall`: a holomorphic function on the
ball whose derivative is `g'/g` and whose real part is `log ‖g‖`. -/
lemma logPrimitiveOnBall_analytic {g : ℂ → ℂ} {c : ℂ} {R : ℝ}
    (hg : AnalyticOnNhd ℂ g (Metric.ball c R)) (hR : 0 < R)
    (hgne : ∀ w : ℂ, w ∈ Metric.ball c R → g w ≠ 0) :
    ∃ F : ℂ → ℂ,
      DifferentiableOn ℂ F (Metric.ball c R) ∧
      (∀ w : ℂ, w ∈ Metric.ball c R → HasDerivAt F (deriv g w / g w) w) ∧
      (F c).re = Real.log ‖g c‖ ∧
      ∀ w : ℂ, w ∈ Metric.ball c R → (F w).re = Real.log ‖g w‖ := by
  let h : ℂ → ℂ := deriv g / g
  have hcBall : c ∈ Metric.ball c R := Metric.mem_ball_self hR
  have hgne_c : g c ≠ 0 := hgne c hcBall
  have hgDiffOn : DifferentiableOn ℂ g (Metric.ball c R) := hg.differentiableOn
  have hdgDiffOn : DifferentiableOn ℂ (deriv g) (Metric.ball c R) := hg.deriv.differentiableOn
  have hhDiffOn : DifferentiableOn ℂ h (Metric.ball c R) := by
    simpa [h] using (DifferentiableOn.div hdgDiffOn hgDiffOn hgne)
  have hexact : IsExactOn h (Metric.ball c R) := hhDiffOn.isExactOn_ball
  obtain ⟨F, hFc, hFh⟩ := hexact.with_val_at c (Real.log ‖g c‖ : ℂ)
  let q : ℂ → ℂ := (fun z : ℂ => cexp (F z)) / g
  have hFc_re : (F c).re = Real.log ‖g c‖ := by simp [hFc]
  have hq0 : ∀ x : ℂ, x ∈ Metric.ball c R → HasDerivAt q 0 x := by
    intro x hx
    have hF : HasDerivAt F (deriv g x / g x) x := by simpa [h] using hFh x hx
    have hFexp : HasDerivAt (fun z : ℂ => cexp (F z)) (cexp (F x) * (deriv g x / g x)) x := by
      exact (hF.cexp : HasDerivAt (fun z : ℂ => cexp (F z)) (cexp (F x) * (deriv g x / g x)) x)
    have hg' : HasDerivAt g (deriv g x) x := (hg x hx).differentiableAt.hasDerivAt
    have hqder := hFexp.div hg' (hgne x hx)
    have hzero : ((cexp (F x) * (deriv g x / g x)) * g x - cexp (F x) * deriv g x) / g x ^ 2 = 0 := by
      have hnum : cexp (F x) * (deriv g x / g x) * g x - cexp (F x) * deriv g x = 0 := by
        field_simp [hgne x hx]
        ring
      rw [hnum, zero_div]
    have hq0x : HasDerivAt q 0 x := by
      simpa [q] using (hqder.congr_deriv hzero)
    exact hq0x
  have hqDiffOn : DifferentiableOn ℂ q (Metric.ball c R) := by
    intro x hx
    exact (hq0 x hx).differentiableAt.differentiableWithinAt
  have hqderiv0 : EqOn (deriv q) 0 (Metric.ball c R) := by
    intro x hx
    exact (hq0 x hx).deriv
  have hqconst : ∀ w : ℂ, w ∈ Metric.ball c R → q w = q c := fun w hw =>
    (Metric.isOpen_ball.is_const_of_deriv_eq_zero (convex_ball c R).isPreconnected hqDiffOn hqderiv0
      (x := w) (y := c) hw hcBall)
  refine ⟨F, ?_, ?_, ?_, ?_⟩
  · intro x hx
    exact (hFh x hx).differentiableAt.differentiableWithinAt
  · intro w hw
    simpa [h] using hFh w hw
  · exact hFc_re
  · intro w hw
    have hqnorm : ‖q w‖ = ‖q c‖ := by rw [hqconst w hw]
    have hgwn : g w ≠ 0 := hgne w hw
    have hnc : ‖g c‖ ≠ 0 := norm_ne_zero_iff.mpr hgne_c
    have hnorm_expc : ‖cexp (F c)‖ = ‖g c‖ := by
      calc
        ‖cexp (F c)‖ = Real.exp ((F c).re) := Complex.norm_exp (F c)
        _ = ‖g c‖ := by
          rw [hFc_re, Real.exp_log]
          exact (norm_pos_iff.mpr hgne_c)
    have hratio : ‖cexp (F w)‖ / ‖g w‖ = 1 := by
      have hq' : ‖cexp (F w) / g w‖ = ‖cexp (F c) / g c‖ := by
        simpa [q] using hqnorm
      rw [norm_div, norm_div] at hq'
      calc
        ‖cexp (F w)‖ / ‖g w‖ = ‖cexp (F c)‖ / ‖g c‖ := hq'
        _ = 1 := by
          rw [hnorm_expc]
          exact div_self hnc
    have hnw : ‖g w‖ ≠ 0 := norm_ne_zero_iff.mpr hgwn
    have hnorm_expw : ‖cexp (F w)‖ = ‖g w‖ := by
      exact (div_eq_one_iff_eq hnw).mp hratio
    calc
      (F w).re = Real.log ‖cexp (F w)‖ := by
        rw [Complex.norm_exp, Real.log_exp]
      _ = Real.log ‖g w‖ := by rw [hnorm_expw]

/-- **Log-derivative bound for a zero-free analytic function on a ball.**
If `g` is analytic and zero-free on `Metric.ball c R`, with `‖g‖ ≤ M` there and
`m ≤ ‖g c‖`, then for `z₀` inside the ball and any `0 < ρ < R - ‖z₀ - c‖` we
have

`‖g'(z₀)/g(z₀)‖ ≤ 2 (log (2M) - log m) (‖z₀ - c‖ + ρ) / ((R - ‖z₀ - c‖ - ρ) ρ)`.

This is the Cauchy–Borel–Carathéodory estimate used in zero-free-region
arguments (e.g. for Dirichlet `L`-functions). -/
theorem logDeriv_zeroFree_ball_bound_analytic {g : ℂ → ℂ} {c : ℂ} {R m M : ℝ}
    (hR : 0 < R) (hm : 0 < m) (hMm : m ≤ M)
    (hg : AnalyticOnNhd ℂ g (Metric.ball c R))
    (hgne : ∀ w : ℂ, w ∈ Metric.ball c R → g w ≠ 0)
    (hgM : ∀ w : ℂ, w ∈ Metric.ball c R → ‖g w‖ ≤ M)
    (hgm : m ≤ ‖g c‖) :
    ∀ ⦃z₀ : ℂ⦄, z₀ ∈ Metric.ball c R → ∀ ρ : ℝ, 0 < ρ → ρ < R - ‖z₀ - c‖ →
      ‖deriv g z₀ / g z₀‖ ≤
        2 * (Real.log (2 * M) - Real.log m) * (‖z₀ - c‖ + ρ) /
          ((R - ‖z₀ - c‖ - ρ) * ρ) := by
  intro z₀ hz₀ ρ hρ hρR
  rcases logPrimitiveOnBall_analytic hg hR hgne with ⟨F, hFdiff, hFh, hFc_re, hFre⟩
  have hFle : ∀ w : ℂ, w ∈ Metric.ball c R → (F w).re ≤ Real.log M := by
    intro w hw
    rw [hFre w hw]
    exact Real.log_le_log (norm_pos_iff.mpr (hgne w hw)) (hgM w hw)
  have hFc : Real.log m ≤ (F c).re := by
    rw [hFc_re]
    exact Real.log_le_log hm hgm
  have hb := logDerivBoundOfReLeOnBall (F := F) (z₀ := z₀) (ρ := ρ) hR hm hMm hFdiff hFle hFc hz₀ hρ hρR
  have hzF : deriv F z₀ = deriv g z₀ / g z₀ := (hFh z₀ hz₀).deriv
  calc
    ‖deriv g z₀ / g z₀‖ = ‖deriv F z₀‖ := by rw [hzF]
    _ ≤ 2 * (Real.log (2 * M) - Real.log m) * (‖z₀ - c‖ + ρ) /
          ((R - ‖z₀ - c‖ - ρ) * ρ) := hb

end Commons.Analysis.Complex
