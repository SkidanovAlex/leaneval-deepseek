import Mathlib
import Submission.Work.NAKANE2.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.NAKANE2.Surgery

/-- A point already inside `W` is its own first entrance, so the invariant coefficient
`glueMuW F W` vanishes there: no pull-back is performed. -/
theorem glueMuW_eq_zero_of_mem {F : ℂ → ℂ} {W : Set ℂ} {z : ℂ} (hz : z ∈ W) :
    Work.NAKANE2.glueMuW F W z = 0 := by
  classical
  have h : ∃ n : ℕ, (F^[n]) z ∈ W := ⟨0, by simpa using hz⟩
  have hfind : Nat.find h = 0 := (Nat.find_eq_zero h).mpr (by simpa using hz)
  rw [Work.NAKANE2.glueMuW_of_hit h, hfind, Work.FBif.pullIter_zero]

end Work.NAKANE2.Surgery
