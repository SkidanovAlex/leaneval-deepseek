import Mathlib
import Submission.Work.WilG4c.Defs
import Submission.Work.WilG4c.Pullback

namespace Work.WilG4c

/-- `ValuesIn01` (values in `(0,1)` on `Λ`) is preserved by the affine `x`-pullback of a
family, `pullX F α β i l t = F i l (pt (α l + β l · t 0) (Fin.tail t))`, whenever the chart
maps the cube into the cube: `0 ≤ α l`, `0 < β l`, `α l + β l ≤ 1`.  -/
theorem valuesIn01_pullX {k p n : ℕ} {Λ : Set (Fin p → ℝ)}
    {F : Work.WilkG4c.Family k p (n + 1)} {α β : (Fin p → ℝ) → ℝ}
    (h : Work.WilkG4c.ValuesIn01 Λ F) (hα : ∀ l : Fin p → ℝ, 0 ≤ α l)
    (hβ : ∀ l : Fin p → ℝ, 0 < β l) (hαβ : ∀ l : Fin p → ℝ, α l + β l ≤ 1) :
    Work.WilkG4c.ValuesIn01 Λ (Work.WilkG4c.pullX F α β) := by
  intro i l hl t ht
  rw [Work.WilkG4c.pullX_apply]
  exact h i l hl _ (Work.WilkG4c.chartPt_mem_openCube (hα l) (hβ l) (hαβ l) ht)

end Work.WilG4c
