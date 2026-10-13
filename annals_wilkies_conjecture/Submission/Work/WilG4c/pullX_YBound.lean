import Mathlib
import Submission.Work.WilG4c.Pullback

namespace Work.WilG4c

open Work.WilkG4c

/-- `YBound` (unit `y`-derivatives, BNZ `‖F_λ(x,·)‖_r ≤ 1`) is preserved by the affine
`x`-pullback `pullX F α β` (defined in `Submission/Work/WilG4c/Pullback.lean` as
`t ↦ F i l (α l + β l · t 0, tail t)`) whenever the chart maps the open interval into itself:
`0 ≤ α l`, `0 < β l`, `α l + β l ≤ 1`.  (The slice of the pullback at `s` is the slice of `F`
at `α l + β l · s` composed with the projection `t ↦ tail t`; both `YBound` conditions hold
because `α l + β l · s ∈ (0,1)` for `s ∈ (0,1)`.) -/
theorem pullX_YBound {k p n : ℕ} {F : Family k p (n + 1)} {r : ℕ} {α β : (Fin p → ℝ) → ℝ}
    (hY : YBound F r) (hα : ∀ l, 0 ≤ α l) (hβ : ∀ l, 0 < β l)
    (hαβ : ∀ l, α l + β l ≤ 1) : YBound (pullX F α β) r := by
  intro i l x hx m hm y hy
  rw [slice_pullX]
  have hxI : α l + β l * x ∈ I := by
    obtain ⟨hx0, hx1⟩ := hx
    refine ⟨?_, ?_⟩
    · have : 0 < β l * x := mul_pos (hβ l) hx0
      linarith [hα l]
    · have hlt : β l * x < β l * 1 := mul_lt_mul_of_pos_left hx1 (hβ l)
      linarith [hαβ l]
  exact hY i l (α l + β l * x) hxI m hm y hy

end Work.WilG4c
