import Mathlib
import Submission.Work.FoldInst.Atlas

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.FoldInst

set_option maxHeartbeats 4000000

/-- The midpoint of the edge of the 24-cell whose side `S = 10` is tight.  The side `10` has type
index `2`, whose type generator `typeGen 2` has copy bit `1`: the two copies of `Q̄` are therefore
identified at this point. -/
noncomputable def y0 : E4 := WithLp.toLp 2 ![0, (1 / 2 : ℝ), -(1 / 2 : ℝ), 0]

/-- The point `y0` lies in the truncated 24-cell. -/
theorem y0_mem_Qbar : y0 ∈ Qbar := by
  constructor
  · intro S
    fin_cases S <;>
      (simp only [sideSlack, sideNormal, y0, Fin.sum_univ_four]; norm_num)
  · intro w
    fin_cases w <;>
      (simp only [truncSlack, truncNormal2, y0, Fin.sum_univ_four]; norm_num)

/-- The side `10` is tight at `y0`. -/
theorem sideSlack_ten_y0 : sideSlack 10 y0 = 0 := by
  simp only [sideSlack, sideNormal, y0, Fin.sum_univ_four]; norm_num

theorem copies_meet : ∃ x y : Xbar, x.1 = 0 ∧ y.1 = 1 ∧ rel x y := by
  refine ⟨(0, ⟨y0, y0_mem_Qbar⟩), actX (sideType 10) (0, ⟨y0, y0_mem_Qbar⟩), rfl, ?_, ?_⟩
  · -- the copy bit of `sideType 10` is `1`
    simp [actX_fst, sideType, sideTypeIdx, typeGenFlip]
  · -- `sideType 10 ∈ Ksub y0`, so the pairing identifies the point with its image
    exact ⟨sideType 10, AddSubgroup.subset_closure ⟨10, sideSlack_ten_y0, rfl⟩, rfl⟩

end Work.FoldInst
