import Mathlib
import Submission.Work.FIPiChain.Defs
import Submission.Work.FIChain.measurable_s3halves
import Submission.Work.FIChain.abs_S3minusC_le

set_option autoImplicit false

namespace Work.FIPiChain.P3S3

open Finset MeasureTheory
open scoped BigOperators Interval

attribute [local instance] Classical.propDecidable

noncomputable section

/-- Joint measurability of `(s,t) ↦ XrhoC a N m s t (2t)`: the pair `(s,t)` enters only through
the measurable `gammaTrunc s ·` factor and the two range conditions `t < n`, `n ≤ 2t`. -/
lemma measurable_XrhoC_pair (a : ℕ → ℝ) (N m : ℕ) :
    Measurable (fun p : ℝ × ℝ => Work.FITop.XrhoC a N m p.1 p.2 (2 * p.2)) := by
  have h : (fun p : ℝ × ℝ => Work.FITop.XrhoC a N m p.1 p.2 (2 * p.2))
      = fun p : ℝ × ℝ => ∑ n ∈ (Finset.Icc 1 N).filter (fun n => m * n ≤ N),
          (if p.2 < ((n : ℕ) : ℝ) ∧ ((n : ℕ) : ℝ) ≤ 2 * p.2
            then Work.FIPlan.gammaTrunc p.1 n * (ArithmeticFunction.moebius (m * n) : ℝ)
              * a (m * n) else 0) := by
    funext p
    rw [Work.FITop.XrhoC]
  rw [h]
  refine Finset.measurable_sum _ (fun n _ => ?_)
  have hS : MeasurableSet {p : ℝ × ℝ | p.2 < ((n : ℕ) : ℝ) ∧ ((n : ℕ) : ℝ) ≤ 2 * p.2} :=
    (measurableSet_lt measurable_snd measurable_const).inter
      (measurableSet_le measurable_const (measurable_const.mul measurable_snd))
  refine Measurable.ite hS ?_ measurable_const
  have hg : Measurable (fun p : ℝ × ℝ => Work.FIPlan.gammaTrunc p.1 n) := by
    have hg' : (fun p : ℝ × ℝ => Work.FIPlan.gammaTrunc p.1 n)
        = fun p : ℝ × ℝ => Submission.ASP.rhoTrunc n p.1 := by
      funext p; exact Work.FIChain.gammaTrunc_eq_rhoTrunc p.1 n
    rw [hg']
    exact (Submission.ASP.measurable_rhoTrunc n).comp measurable_fst
  have hc : (fun p : ℝ × ℝ => Work.FIPlan.gammaTrunc p.1 n
        * (ArithmeticFunction.moebius (m * n) : ℝ) * a (m * n))
      = fun p : ℝ × ℝ => ((ArithmeticFunction.moebius (m * n) : ℝ) * a (m * n))
        * Work.FIPlan.gammaTrunc p.1 n := by
    funext p; ring
  rw [hc]
  exact measurable_const.mul hg

theorem Grho_measurable_t (N : ℕ) (C : ℝ) :
    Measurable (fun t : ℝ => Work.FIPiChain.Grho N C t) := by
  have hG : Measurable (fun p : ℝ × ℝ =>
      (∑ m ∈ Finset.Icc 1 N, Work.FIChain.wc m
        * |Work.FITop.XrhoC Work.FIChain.atilc N m p.2 p.1 (2 * p.1)|) / p.2) := by
    refine Measurable.div ?_ measurable_snd
    refine Finset.measurable_sum _ (fun m _ => ?_)
    have hswap : Measurable (fun p : ℝ × ℝ => (p.2, p.1)) :=
      measurable_snd.prod measurable_fst
    have hX : Measurable (fun p : ℝ × ℝ =>
        Work.FITop.XrhoC Work.FIChain.atilc N m p.2 p.1 (2 * p.1)) :=
      (measurable_XrhoC_pair Work.FIChain.atilc N m).comp hswap
    exact measurable_const.mul hX.abs
  have hmain := Work.FIChain.measurable_intervalIntegral_param (α := ℝ) (1 : ℝ) hG
    (U := fun _ : ℝ => C) measurable_const
  simpa only [Work.FIPiChain.Grho] using hmain

end

end Work.FIPiChain.P3S3
