import Mathlib
import Submission.Work.Wilkies.Defs
import Submission.Work.WilG5.Basic
import Submission.Work.WilG5.Reindex3
import Submission.Work.WilkiesH.Strat.BadCell
import Submission.Work.WilkiesH.Strat.thin_union_cyl
import Submission.Work.WilG1.Cell.thin_union

namespace Work.WilkiesH.Strat

open WilkiesDesign WilkiesConjecture

theorem dimLE_iUnion_fin {S : WilkiesDesign.SOMin} (hcd : S.SharpCD) {n μ k F D : ℕ}
    (A : Fin k → Set (Fin n → ℝ)) (hΩ : ∀ i, A i ∈ S.Ω F D n)
    (hA : ∀ i, WilkiesDesign.DimLE (A i) μ) :
    WilkiesDesign.DimLE (⋃ i, A i) μ := by
  intro e
  rw [Set.image_iUnion]
  refine Work.WilG1.Cell.thin_union hcd k
    (F + 64 * (n + (μ + 1)) + 64) Polynomial.X (D + 32 * (n + (μ + 1)) + 32)
    (fun i => (fun x : Fin n → ℝ => x ∘ e) '' (A i)) ?_ ?_
  · intro i
    have h := Work.WilG5.coordImage_mem (S := S) (ι := e) (hΩ i)
    rw [Polynomial.eval_X]
    exact h
  · intro i
    exact hA i e

end Work.WilkiesH.Strat
