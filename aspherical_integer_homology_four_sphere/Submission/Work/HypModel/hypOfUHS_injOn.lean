import Mathlib
import Submission.Work.HypModel.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.HypModel

/-- The difference of the last two coordinates of `hypOfUHS q` is the reciprocal of the height
`q 3`: `(‖q‖²+1)/(2(q 3)) − (‖q‖²−1)/(2(q 3)) = 1/(q 3)`.  This is the quantity that
`uhsOfHyp` inverts, and it isolates the height from the coordinates of the hyperboloid point. -/
theorem hypOfUHS_sub_three (q : E4) : hypOfUHS q 4 - hypOfUHS q 3 = (q 3)⁻¹ := by
  rw [hypOfUHS_apply_three, hypOfUHS_apply_four, ← sub_div]
  by_cases h : q 3 = 0
  · simp [h]
  · field_simp
    ring

/-- `hypOfUHS` is injective on the upper half space `{q : 0 < q 3}`.

Two points of the upper half space with the same image on the hyperboloid have the same height —
the difference of the last two coordinates of the image recovers `(q 3)⁻¹` — and then the first
three coordinates, which are `q i / q 3`, agree as well. -/
theorem hypOfUHS_injOn : Set.InjOn hypOfUHS upperHalfSpace := by
  intro q hq q' hq' h
  have hq3 : q 3 ≠ 0 := ne_of_gt hq
  -- the height is read off from the difference of the last two coordinates
  have h34 : q 3 = q' 3 := by
    have h4 := congrFun h (4 : Fin 5)
    have h3 := congrFun h (3 : Fin 5)
    have hinv : (q 3)⁻¹ = (q' 3)⁻¹ := by
      rw [← hypOfUHS_sub_three q, ← hypOfUHS_sub_three q', h4, h3]
    exact inv_inj.mp hinv
  -- the horizontal coordinates are `q i / q 3` and agree once the heights are equal
  refine PiLp.ext (fun i => ?_)
  fin_cases i
  · have hi := congrFun h (0 : Fin 5)
    simp only [hypOfUHS_apply_zero] at hi
    rw [← h34] at hi
    exact mul_right_cancel₀ hq3 ((div_eq_div_iff hq3 hq3).mp hi)
  · have hi := congrFun h (1 : Fin 5)
    simp only [hypOfUHS_apply_one] at hi
    rw [← h34] at hi
    exact mul_right_cancel₀ hq3 ((div_eq_div_iff hq3 hq3).mp hi)
  · have hi := congrFun h (2 : Fin 5)
    simp only [hypOfUHS_apply_two] at hi
    rw [← h34] at hi
    exact mul_right_cancel₀ hq3 ((div_eq_div_iff hq3 hq3).mp hi)
  · exact h34

end Work.HypModel
