/-
# The column checks of the boundary compatibility of `M̄`

Each theorem below is one `decide` over the columns of a fixed degree: it evaluates the geometric
sparse vector `gcol n e` (over the facets of the root face of the `e`-th cell in degree `n + 1`)
and compares it with the column `imgCol n e` of `mbarBd n` (read in the cell numbering of `M̄`).

These are the finite checks of `Work.MbarHomology.BdFiber.mbarBd_fiber`.
-/
import Submission.Work.MbarHomology.BdFiber.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option autoImplicit false

namespace Work.MbarHomology.BdFiber

/-- The `168` columns in degree `1`. -/
theorem colOk_zero : ∀ e : Fin (Work.HomologyIso.Gen.mbarDim 1), colOk 0 e = true := by
  decide

/-- The `192` columns in degree `2`. -/
theorem colOk_one : ∀ e : Fin (Work.HomologyIso.Gen.mbarDim 2), colOk 1 e = true := by
  decide

/-- The `72` columns in degree `3`. -/
theorem colOk_two : ∀ e : Fin (Work.HomologyIso.Gen.mbarDim 3), colOk 2 e = true := by
  decide

/-- The `2` columns in degree `4`. -/
theorem colOk_three : ∀ e : Fin (Work.HomologyIso.Gen.mbarDim 4), colOk 3 e = true := by
  decide

/-- **All the column checks** of the boundary compatibility. -/
theorem colOk_all (n : ℕ) (hn : n + 1 < 5)
    (e : Fin (Work.HomologyIso.Gen.mbarDim (n + 1))) : colOk n e = true := by
  have h : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 := by omega
  rcases h with rfl | rfl | rfl | rfl
  · exact colOk_zero e
  · exact colOk_one e
  · exact colOk_two e
  · exact colOk_three e

end Work.MbarHomology.BdFiber
