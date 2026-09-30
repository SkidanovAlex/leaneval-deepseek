import Mathlib
import Submission.Work.BMF.fam_card_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.SD

/-- Points of an `(X, H)`-family lying below `(1+ρ)X/10` all lie in the window
`[X/10, (1+ρ)X/10)`, of length `ρX/10`, and are `500H`-separated; hence there are at most
`(ρX/10)/(500H) + 1 = ρ(X/H)/5000 + 1` of them. -/
theorem low_sources_card_le {X H ρ : ℝ} (hX : 0 < X) (hH : 0 < H) (hρ : 0 < ρ)
    {S : Finset ℝ} (hS : Work.BMF.IsFam X H S) :
    ((S.filter (fun y => ¬ ((1 + ρ) * X / 10 ≤ y))).card : ℝ) ≤ ρ * (X / H) / 5000 + 1 := by
  have hbound := hS.1
  have hsep := hS.2
  have hmain : ((S.filter (fun y => ¬ ((1 + ρ) * X / 10 ≤ y))).card : ℝ) ≤
      ((1 + ρ) * X / 10 - X / 10) / (500 * H) + 1 := by
    refine Work.BMF.card_le_of_sep (S := S.filter (fun y => ¬ ((1 + ρ) * X / 10 ≤ y)))
      (a := X / 10) (b := (1 + ρ) * X / 10) (d := 500 * H) ?_ ?_ ?_ ?_ ?_
    · nlinarith [hX, hρ]
    · linarith
    · intro x hx
      rw [Finset.mem_filter] at hx
      exact (hbound x hx.1).1
    · intro x hx
      rw [Finset.mem_filter] at hx
      exact le_of_lt (not_le.mp hx.2)
    · intro x hx y hy hne
      rw [Finset.mem_filter] at hx hy
      exact hsep x hx.1 y hy.1 hne
  have harith : ((1 + ρ) * X / 10 - X / 10) / (500 * H) = ρ * (X / H) / 5000 := by
    field_simp
    ring
  linarith [hmain, harith]

end Work.BMF.SD
