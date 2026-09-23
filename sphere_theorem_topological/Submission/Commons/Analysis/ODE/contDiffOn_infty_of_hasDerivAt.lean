import Mathlib
import Submission.Commons.Analysis.ODE.contDiffOn_of_hasDerivAt_of_contDiffOn

namespace Commons.Analysis.ODE

open Set Filter
open scoped Topology ContDiff

/-- Bootstrap: if `y` solves `y' = F(y)` on `[a,b]`, with `F` smooth along the values of `y`
(contained in `V`) and `y` continuous on `[a,b]`, then `y` is smooth on `[a,b]`. -/
theorem contDiffOn_infty_of_hasDerivAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : E → E} {V : Set E} {y : ℝ → E} {a b : ℝ} (hab : a < b)
    (hF : ContDiffOn ℝ ((⊤ : ENat) : WithTop ENat) F V)
    (hyV : ∀ t ∈ Set.Icc a b, y t ∈ V)
    (hy : ∀ t ∈ Set.Icc a b, HasDerivAt y (F (y t)) t)
    (hyc : ContinuousOn y (Set.Icc a b)) :
    ContDiffOn ℝ ((⊤ : ENat) : WithTop ENat) y (Set.Icc a b) := by
  rw [contDiffOn_infty]
  intro n
  have hFk : ∀ k : ℕ, ContDiffOn ℝ k F V := fun k => (contDiffOn_infty.mp hF) k
  have hs : UniqueDiffOn ℝ (Set.Icc a b) := uniqueDiffOn_Icc hab
  have key : ∀ k : ℕ, ContDiffOn ℝ k y (Set.Icc a b) := by
    intro k
    induction k with
    | zero =>
      rw [Nat.cast_zero, contDiffOn_zero]
      exact hyc
    | succ k ih =>
      have hcomp : ContDiffOn ℝ k (fun t => F (y t)) (Set.Icc a b) :=
        (hFk k).comp ih hyV
      exact contDiffOn_succ_of_hasDerivAt_of_contDiffOn hs hcomp hy
  exact key n

end Commons.Analysis.ODE
