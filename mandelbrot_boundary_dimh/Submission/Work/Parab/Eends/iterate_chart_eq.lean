import Mathlib
import Submission.Work.FatouCoord.Setup

namespace Work.Parab.Eends

open Function

/-- **Iterating the chart conjugacy.**  If none of the `wMap`-iterates of `w` up to step `n` vanishes, then the `f`-iterates of `chart w` are the charts of the `wMap`-iterates of `w`. -/
theorem iterate_chart_eq {f : ℂ → ℂ} {w : ℂ} {n : ℕ}
    (hw : ∀ k ≤ n, (Work.FatouCoord.wMap f)^[k] w ≠ 0) :
    ∀ k ≤ n, f^[k] (Work.FatouCoord.chart w)
      = Work.FatouCoord.chart ((Work.FatouCoord.wMap f)^[k] w) := by
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
    intro hk
    -- the induction hypothesis applies at the smaller index `k`
    have hk' : k ≤ n := Nat.le_trans (Nat.le_succ k) hk
    rw [Function.iterate_succ_apply', ih hk']
    -- the single step: `f (chart x) = chart (wMap f x)` as long as `f (chart x) ≠ 0`
    have hne : (Work.FatouCoord.wMap f)^[k+1] w ≠ 0 := hw (k+1) hk
    have hfz : f (Work.FatouCoord.chart ((Work.FatouCoord.wMap f)^[k] w)) ≠ 0 := by
      intro h0
      apply hne
      rw [Function.iterate_succ_apply']
      simp only [Work.FatouCoord.wMap, h0, Work.FatouCoord.chart_zero]
    rw [Function.iterate_succ_apply']
    simp only [Work.FatouCoord.wMap]
    rw [Work.FatouCoord.chart_chart hfz]

end Work.Parab.Eends
