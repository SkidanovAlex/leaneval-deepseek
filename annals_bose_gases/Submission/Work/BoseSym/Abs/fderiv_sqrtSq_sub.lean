import Mathlib.Tactic.Have
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Submission.Work.BoseSym.Interface
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseSym.Abs

open scoped Topology Real ContDiff

theorem fderiv_sqrtSq_sub {N : ℕ} {L : ℝ} (F : Work.BoseSym.testSub N L) {a : ℝ} (ha : 0 < a)
    (x v : Work.BoseSym.Conf N) :
    fderiv ℝ (fun y => Real.sqrt (((F : Work.BoseSym.Conf N → ℝ) y) ^ 2 + a ^ 2) - a) x v
      = ((F : Work.BoseSym.Conf N → ℝ) x / Real.sqrt (((F : Work.BoseSym.Conf N → ℝ) x) ^ 2 + a ^ 2))
          * fderiv ℝ (F : Work.BoseSym.Conf N → ℝ) x v := by
  set f : Work.BoseSym.Conf N → ℝ := (F : Work.BoseSym.Conf N → ℝ) with hf
  have hFcd : ContDiff ℝ ∞ f := F.2.1
  have hdiff : Differentiable ℝ f := hFcd.differentiable (by simp)
  have hfd : HasFDerivAt f (fderiv ℝ f x) x := (hdiff x).hasFDerivAt
  have hpow : HasFDerivAt (fun y => f y ^ 2) ((2 * f x) • fderiv ℝ f x) x := by
    have := hfd.pow 2
    simpa using this
  have hplus : HasFDerivAt (fun y => f y ^ 2 + a ^ 2) ((2 * f x) • fderiv ℝ f x) x :=
    hpow.add_const _
  have hu : f x ^ 2 + a ^ 2 ≠ 0 := by positivity
  have hsqrt : HasDerivAt Real.sqrt (1 / (2 * Real.sqrt (f x ^ 2 + a ^ 2))) (f x ^ 2 + a ^ 2) :=
    Real.hasDerivAt_sqrt hu
  have hcomp := hsqrt.comp_hasFDerivAt x hplus
  have hsub := hcomp.sub_const a
  change (fderiv ℝ (fun x => (Real.sqrt ∘ fun y => f y ^ 2 + a ^ 2) x - a) x) v
    = f x / Real.sqrt (f x ^ 2 + a ^ 2) * (fderiv ℝ f x) v
  rw [hsub.fderiv]
  simp only [smul_apply, smul_eq_mul]
  have hs : Real.sqrt (f x ^ 2 + a ^ 2) ≠ 0 := by positivity
  field_simp

end Work.BoseSym.Abs
