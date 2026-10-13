import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.StrongEps.Basic
import Submission.Work.FTS.StrongEps.Kernel
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsE4Thr.FstarJepsSmoothAux

open MeasureTheory Set Filter

theorem Jeps_eq_iterated {ρ : ℝ × ℝ → ℝ} (hρ : Work.FTS.StrongEps.IsMollKernel ρ) {ε : ℝ}
    (hε : 0 < ε) {W : ℝ → ℝ → ℝ} (hsm : Work.FTS.EllipticEst.SmoothOpen W) {s θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Work.FTS.StrongEps.Jeps ρ ε W (Real.exp s) θ
      = ∫ q in Set.Icc (-ε) ε, ∫ a : ℝ,
          Work.FTS.StrongEps.Jker ρ ε (a, q) * W (Real.exp (s - a))
            (Work.FTS.StrongEps.thShift θ q) := by
  rw [Work.FTS.StrongEps.Jeps_eq_integral ρ ε W (Real.exp_pos s) hθ]
  have hshift : ∀ p : ℝ × ℝ,
      Work.FTS.StrongEps.zShift (Real.exp s) p.1 = Real.exp (s - p.1) := by
    intro p
    simp only [Work.FTS.StrongEps.zShift, sub_eq_add_neg, Real.exp_add]
  simp only [hshift]
  -- the integrand is integrable: the kernel has compact support and the profile is continuous
  -- and bounded on the (compact) image of that support.
  have hInt : Integrable (fun p : ℝ × ℝ => Work.FTS.StrongEps.Jker ρ ε p *
      W (Real.exp (s - p.1)) (Work.FTS.StrongEps.thShift θ p.2)) := by
    have hΦcont : Continuous fun p : ℝ × ℝ =>
        (Real.exp (s - p.1), Work.FTS.StrongEps.thShift θ p.2) :=
      (Real.continuous_exp.comp (continuous_const.sub continuous_fst)).prodMk
        ((Work.FTS.StrongEps.continuous_thShift θ).comp continuous_snd)
    have hmap : MapsTo (fun p : ℝ × ℝ =>
        (Real.exp (s - p.1), Work.FTS.StrongEps.thShift θ p.2))
        (Metric.closedBall (0 : ℝ × ℝ) ε) Work.FTS.EllipticEst.Q0 := by
      intro p _
      rw [Work.FTS.EllipticEst.mem_Q0]
      exact ⟨Real.exp_pos _, Work.FTS.StrongEps.thShift_mem hθ⟩
    have hcontA : ContinuousOn (fun p : ℝ × ℝ =>
        W (Real.exp (s - p.1)) (Work.FTS.StrongEps.thShift θ p.2))
        (Metric.closedBall (0 : ℝ × ℝ) ε) :=
      hsm.continuousOn.comp hΦcont.continuousOn hmap
    have hIntOn : IntegrableOn (fun p : ℝ × ℝ => Work.FTS.StrongEps.Jker ρ ε p *
        W (Real.exp (s - p.1)) (Work.FTS.StrongEps.thShift θ p.2))
        (Metric.closedBall (0 : ℝ × ℝ) ε) :=
      Work.FTS.StrongEps.integrableOn_Jker_mul_ball hρ hε hcontA
    have hzero : ∀ p : ℝ × ℝ, p ∉ Metric.closedBall (0 : ℝ × ℝ) ε →
        Work.FTS.StrongEps.Jker ρ ε p *
          W (Real.exp (s - p.1)) (Work.FTS.StrongEps.thShift θ p.2) = 0 := fun p hp => by
      rw [Work.FTS.StrongEps.Jker_eq_zero_of_not_mem hρ hε hp, zero_mul]
    have hfun : (fun p : ℝ × ℝ => Work.FTS.StrongEps.Jker ρ ε p *
        W (Real.exp (s - p.1)) (Work.FTS.StrongEps.thShift θ p.2))
        = (Metric.closedBall (0 : ℝ × ℝ) ε).indicator (fun p : ℝ × ℝ =>
            Work.FTS.StrongEps.Jker ρ ε p *
              W (Real.exp (s - p.1)) (Work.FTS.StrongEps.thShift θ p.2)) := by
      funext p
      by_cases hp : p ∈ Metric.closedBall (0 : ℝ × ℝ) ε
      · rw [Set.indicator_of_mem hp]
      · rw [Set.indicator_of_notMem hp, hzero p hp]
    rw [hfun]
    exact (MeasureTheory.integrable_indicator_iff measurableSet_closedBall).2 hIntOn
  rw [show (∫ p : ℝ × ℝ, Work.FTS.StrongEps.Jker ρ ε p *
        W (Real.exp (s - p.1)) (Work.FTS.StrongEps.thShift θ p.2))
      = ∫ y : ℝ, ∫ x : ℝ, Work.FTS.StrongEps.Jker ρ ε (x, y) *
        W (Real.exp (s - x)) (Work.FTS.StrongEps.thShift θ y) from
    MeasureTheory.integral_prod_symm (μ := volume) (ν := volume) _ hInt]
  -- the inner integral vanishes unless `q ∈ [-ε, ε]`
  have hH : ∀ q : ℝ, q ∉ Set.Icc (-ε) ε →
      (∫ a : ℝ, Work.FTS.StrongEps.Jker ρ ε (a, q) * W (Real.exp (s - a))
        (Work.FTS.StrongEps.thShift θ q)) = 0 := by
    intro q hq
    have hqabs : ε < |q| := by
      have hq' : q < -ε ∨ ε < q := by
        simpa only [Set.mem_Icc, not_and_or, not_le] using hq
      rcases hq' with h | h
      · have hεq : ε < -q := by linarith
        exact lt_of_lt_of_le hεq (neg_le_abs q)
      · exact lt_of_lt_of_le h (le_abs_self q)
    have hJ : ∀ a : ℝ, Work.FTS.StrongEps.Jker ρ ε (a, q) = 0 := by
      intro a
      by_contra hne
      have hb := Work.FTS.StrongEps.Jker_ne_zero_support hρ hε hne
      have h1 : q ^ 2 ≤ ε ^ 2 := by nlinarith [sq_nonneg a]
      have h2 : |q| ≤ ε := by
        rw [sq_le_sq] at h1
        rwa [abs_of_nonneg hε.le] at h1
      linarith
    simp [hJ]
  rw [MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero hH]

end Work.FTS.StrongEps.EpsE4Thr.FstarJepsSmoothAux
