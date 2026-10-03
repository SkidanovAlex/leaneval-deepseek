import Mathlib
import Submission.Work.FIPiChain.Defs

namespace Work.FIPiChain.P3S3

open MeasureTheory Finset
open scoped BigOperators Interval

noncomputable section

/-- Joint Borel measurability of `(s, t) ↦ XrhoC a N m s t (2t)`: a finite sum, over
`n ≤ N`, of the step functions `(s,t) ↦ 1_{-∞<t}1_{2t≥n}(t) · γ(n;s) · μ(mn) · a(mn)`. -/
lemma measurable_XrhoC_joint (a : ℕ → ℝ) (N m : ℕ) :
    Measurable (fun p : ℝ × ℝ => Work.FITop.XrhoC a N m p.1 p.2 (2 * p.2)) := by
  simp only [Work.FITop.XrhoC]
  refine Finset.measurable_sum _ (fun n _ => ?_)
  refine Measurable.ite ?hset ?hthen ?helse
  · exact (measurableSet_lt measurable_snd measurable_const).inter
      (measurableSet_le measurable_const (by fun_prop : Measurable (fun p : ℝ × ℝ => 2 * p.2)))
  · have heq : (fun p : ℝ × ℝ => Work.FIPlan.gammaTrunc p.1 n
        * (ArithmeticFunction.moebius (m * n) : ℝ) * a (m * n))
        = fun p : ℝ × ℝ =>
          ((ArithmeticFunction.moebius (m * n) : ℝ) * a (m * n))
            * Work.FIPlan.gammaTrunc p.1 n := by
      funext p; ring
    rw [heq]
    exact measurable_const.mul ((Submission.ASP.measurable_rhoTrunc n).comp measurable_fst)
  · exact measurable_const

theorem Grho_measurable_u (x : ℕ) (C : ℝ) :
    Measurable (fun u : ℝ => Work.FIPiChain.Grho x C u) := by
  -- The `s`-integrand, as a function of the pair `(t, s)`, is jointly measurable.
  have hG : Measurable (fun p : ℝ × ℝ =>
      (∑ m ∈ Finset.Icc 1 x, Work.FIChain.wc m
        * |Work.FITop.XrhoC Work.FIChain.atilc x m p.2 p.1 (2 * p.1)|) / p.2) := by
    refine Measurable.div ?_ measurable_snd
    refine Finset.measurable_sum _ (fun m _ => ?_)
    exact measurable_const.mul
      (((measurable_XrhoC_joint Work.FIChain.atilc x m).comp measurable_swap).abs)
  -- Parametric interval integral: `t ↦ ∫ s in 1..C, G (t, s)` is measurable.
  have h := Work.FIChain.measurable_intervalIntegral_param (α := ℝ) (a := (1 : ℝ))
      (G := fun p : ℝ × ℝ =>
        (∑ m ∈ Finset.Icc 1 x, Work.FIChain.wc m
          * |Work.FITop.XrhoC Work.FIChain.atilc x m p.2 p.1 (2 * p.1)|) / p.2)
      hG (U := fun _ : ℝ => C) measurable_const
  simpa only [Work.FIPiChain.Grho] using h

end

end Work.FIPiChain.P3S3
