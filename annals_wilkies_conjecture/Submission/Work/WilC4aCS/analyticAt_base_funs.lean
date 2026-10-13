import Mathlib
import Submission.Work.WilC4aCS.Defs
import Submission.Work.WilC4aCS.analyticAt_coefFun
import Submission.Work.WilC4aCS.analyticAt_ev0_comp

namespace Work.WilC4aCS

open WilkiesDesign.E

theorem analyticAt_base_funs {n l : ℕ} (d : Fin (l + 1) → ℕ)
    (a : ∀ i, Fin (d i) → (Fin n → ℝ) → ℝ) (ha : ∀ i j, AnalyticAt ℝ (a i j) 0)
    (B : WilkiesDesign.E.Basic (∑ i, d i) 0) :
    AnalyticAt ℝ (fun x' : Fin n → ℝ => ∑ f ∈ B.eqs.toFinset,
        (Work.WilC4aCS.ev0 (Work.WilC4aCS.coefFun d a x') f) ^ 2) 0 ∧
      (∀ j : Fin B.pos.length, AnalyticAt ℝ (fun x' : Fin n → ℝ =>
        Work.WilC4aCS.ev0 (Work.WilC4aCS.coefFun d a x') (B.pos.get j)) 0) := by
  -- The coefficient components `x' ↦ coefFun d a x' t` are the given analytic functions `a i j`.
  have hcoef : ∀ t : Fin (∑ i, d i),
      AnalyticAt ℝ (fun x' : Fin n → ℝ => Work.WilC4aCS.coefFun d a x' t) 0 :=
    fun t => analyticAt_coefFun d a ha t
  -- Hence every semialgebraic atom evaluates analytically along the coefficient vector.
  have hev : ∀ p : EAPoly (∑ i, d i) 0,
      AnalyticAt ℝ (fun x' : Fin n → ℝ => Work.WilC4aCS.ev0 (Work.WilC4aCS.coefFun d a x') p) 0 :=
    fun p => analyticAt_ev0_comp (Work.WilC4aCS.coefFun d a) p hcoef
  constructor
  · -- The defining equation of the base is a finite sum of squares of analytic functions.
    rw [show (fun x' : Fin n → ℝ => ∑ f ∈ B.eqs.toFinset,
            (Work.WilC4aCS.ev0 (Work.WilC4aCS.coefFun d a x') f) ^ 2)
        = ∑ f ∈ B.eqs.toFinset,
            (fun x' : Fin n → ℝ => (Work.WilC4aCS.ev0 (Work.WilC4aCS.coefFun d a x') f) ^ 2) from by
          funext x'; simp [Finset.sum_apply]]
    exact Finset.analyticAt_sum B.eqs.toFinset (fun f _ => (hev f).pow 2)
  · -- Each inequality function is one such atom.
    intro j
    exact hev (B.pos.get j)

end Work.WilC4aCS
