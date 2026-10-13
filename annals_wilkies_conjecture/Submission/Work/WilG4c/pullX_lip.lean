import Mathlib
import Submission.Work.WilG4c.Pullback

namespace Work.WilG4c

open Work.WilkG4c
open WilkiesDesign WilkiesDesign.CG

/-- `LipOnCube` (1-Lipschitz on the open cube) is preserved by the affine `x`-pullback
`pullX F α β` (defined in `Submission/Work/WilG4c/Pullback.lean`) when the chart maps the cube
into the cube (`0 ≤ α l`, `0 < β l`, `α l + β l ≤ 1`, so also `β l ≤ 1`): the chart
`t ↦ (α l + β l · t 0, tail t)` is `1`-Lipschitz in the sup-metric because the first coordinate
is shrunk by the factor `β l ≤ 1` and the other coordinates are unchanged.  (The strict
`0 < β l` is needed: at `β l = 0`, `α l = 0` the chart lands on the boundary of the cube, where
`LipOnCube F 1` says nothing.) -/
theorem pullX_lip {k p n : ℕ} {F : Family k p (n + 1)} {α β : (Fin p → ℝ) → ℝ}
    (hL : LipOnCube F 1) (hα : ∀ l, 0 ≤ α l) (hβ : ∀ l, 0 < β l)
    (hαβ : ∀ l, α l + β l ≤ 1) : LipOnCube (pullX F α β) 1 := by
  -- Unfold `LipOnCube` and reduce both family members to `F` evaluated at the chart points.
  intro i l z z' hz hz'
  -- `β l ≤ 1`, so the first coordinate of the chart is shrunk.
  have hβ1 : β l ≤ 1 := by linarith [hα l, hαβ l]
  -- The chart maps the open cube into itself.
  have hmem : ∀ {t : Fin (n + 1) → ℝ}, t ∈ openCube (n + 1) →
      chartPt α β l t ∈ openCube (n + 1) :=
    fun {t} ht => chartPt_mem_openCube (hα l) (hβ l) (hαβ l) ht
  -- The chart is `1`-Lipschitz in the sup-metric: coordinate `0` is multiplied by
  -- `β l ≤ 1`, all other coordinates are unchanged, and the sup-metric on `Fin (n+1) → ℝ`
  -- is characterized by its coordinatewise inequalities.
  have hchart : dist (chartPt α β l z) (chartPt α β l z') ≤ dist z z' := by
    rw [dist_pi_le_iff dist_nonneg]
    intro j
    induction j using Fin.cases with
    | zero =>
        rw [chartPt_zero, chartPt_zero, Real.dist_eq]
        have h2 : |z 0 - z' 0| ≤ dist z z' := by
          simpa [Real.dist_eq] using dist_le_pi_dist z z' (0 : Fin (n + 1))
        calc |(α l + β l * z 0) - (α l + β l * z' 0)|
            = β l * |z 0 - z' 0| := by
              rw [show (α l + β l * z 0) - (α l + β l * z' 0) = β l * (z 0 - z' 0) by ring,
                abs_mul, abs_of_pos (hβ l)]
          _ ≤ 1 * |z 0 - z' 0| := mul_le_mul_of_nonneg_right hβ1 (abs_nonneg _)
          _ = |z 0 - z' 0| := one_mul _
          _ ≤ dist z z' := h2
    | succ j =>
        rw [chartPt_succ, chartPt_succ]
        exact dist_le_pi_dist z z' j.succ
  -- Assemble: `pullX F α β i l t = F i l (chartPt α β l t)`, `F` is `1`-Lipschitz on the
  -- cube, and the chart does not increase distances.
  calc |pullX F α β i l z - pullX F α β i l z'|
      = |F i l (chartPt α β l z) - F i l (chartPt α β l z')| := rfl
    _ ≤ 1 * dist (chartPt α β l z) (chartPt α β l z') :=
        hL i l (chartPt α β l z) (chartPt α β l z') (hmem hz) (hmem hz')
    _ ≤ 1 * dist z z' := mul_le_mul_of_nonneg_left hchart zero_le_one

end Work.WilG4c

namespace Work.WilkG4c

open Work.WilkG4c

/-- Compatibility alias: the same statement under the namespace spelling `Work.WilkG4c` in
which the core vocabulary of this area (`Defs.lean`, `Pullback.lean`) is defined, so that
consumers of either spelling of the pullback lemma build.  The canonical name of this lemma is
`Work.WilG4c.pullX_lip`. -/
theorem pullX_lip {k p n : ℕ} {F : Family k p (n + 1)} {α β : (Fin p → ℝ) → ℝ}
    (hL : LipOnCube F 1) (hα : ∀ l, 0 ≤ α l) (hβ : ∀ l, 0 < β l)
    (hαβ : ∀ l, α l + β l ≤ 1) : LipOnCube (pullX F α β) 1 :=
  Work.WilG4c.pullX_lip hL hα hβ hαβ

end Work.WilkG4c
