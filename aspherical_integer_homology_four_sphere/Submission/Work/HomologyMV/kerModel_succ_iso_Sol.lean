import Mathlib
import Submission.Work.HomologyMV.Model

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.HomologyMV

open CategoryTheory

/-- The model group `kerModel (j-1)` for the kernel of `φ_{j-1}` matches the answer `Sol j` in every degree `j ≥ 1`: `ℤ` when `j = 4` and the zero module otherwise. -/
theorem kerModel_succ_iso_Sol (j : ℕ) (hj : 1 ≤ j) : Nonempty (kerModel ((j : ℤ) - 1) ≅ Sol j) := by
  rcases eq_or_ne j 4 with h4 | h4
  · subst h4
    simp only [kerModel, Sol]
    exact ⟨Iso.refl _⟩
  · have hk : ((j : ℤ) - 1) ≠ 3 := by
      intro h
      omega
    refine iso_of_isZero ?_ (isZero_Sol_of_ne (by omega) h4)
    rw [kerModel_eq_zero _ hk]
    exact isZero_freeMod_zero

end Work.HomologyMV
