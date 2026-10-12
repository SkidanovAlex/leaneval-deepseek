import Mathlib.Algebra.Order.Archimedean.Real.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBogFS

/-- The final pure-real arithmetic of the `hEpsLog` row: with `B ∈ (0, 1/1024]`, `L ≥ 0`,
`X ≤ 58 + (1293/1292)L` and `B(1 + (156/323)L) ≤ ε`, one has `B² X ≤ ε`. -/
lemma bogEpsLogArith {B L X ε : ℝ} (hB0 : 0 < B) (hB : B ≤ 1 / 1024) (hL : 0 ≤ L)
    (hX : X ≤ 58 + (1293 / 1292) * L) (hε : B * (1 + (156 / 323) * L) ≤ ε) :
    B ^ 2 * X ≤ ε := by
  -- `B ≤ 1/1024` and `L ≥ 0` give `B * L ≤ (1/1024) * L`
  have hBL : B * L ≤ (1 / 1024) * L := mul_le_mul_of_nonneg_right hB hL
  -- hence `B * (58 + (1293/1292) * L) ≤ 1 + (156/323) * L`
  have hkey : B * (58 + (1293 / 1292) * L) ≤ 1 + (156 / 323) * L := by
    nlinarith [hBL]
  calc B ^ 2 * X = B * (B * X) := by ring
    _ ≤ B * (B * (58 + (1293 / 1292) * L)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hX (le_of_lt hB0))
          (le_of_lt hB0)
    _ ≤ B * (1 + (156 / 323) * L) := mul_le_mul_of_nonneg_left hkey (le_of_lt hB0)
    _ ≤ ε := hε

end Work.BoseBogFS
