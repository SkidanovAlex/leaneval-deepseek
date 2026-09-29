import Mathlib
import Submission.Work.TMContract.Defs

namespace Work.TMComp.Kotani

open Work.TMContract

/-- `tmC lam · ·` is continuous in `(E, x)`. -/
private lemma continuous_tmC (lam : ℝ) :
    Continuous (fun q : ℂ × ℝ => tmC lam q.1 q.2) := by
  unfold tmC
  fun_prop

theorem continuous_iterC_prod (α lam : ℝ) (k : ℕ) :
    Continuous (fun p : ℂ × ℝ => Work.TMContract.iterC α lam p.1 k p.2) := by
  induction k with
  | zero => simp only [iterC]; exact continuous_const
  | succ n ih =>
    have hA : Continuous (fun p : ℂ × ℝ => tmC lam p.1 (p.2 + (n : ℝ) * α)) :=
      (continuous_tmC lam).comp
        (continuous_fst.prodMk (continuous_snd.add continuous_const))
    have hfun : (fun p : ℂ × ℝ => iterC α lam p.1 (n + 1) p.2)
        = fun p => tmC lam p.1 (p.2 + (n : ℝ) * α) * iterC α lam p.1 n p.2 := by
      funext p; simp only [iterC]
    rw [hfun]
    exact hA.matrix_mul ih

end Work.TMComp.Kotani
