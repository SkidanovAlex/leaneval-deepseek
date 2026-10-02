import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.ELRig

/-- In any nonempty open interval of the real line one can find a point outside a
prescribed countable set: `(0, ε)` has cardinality continuum, hence is not countable,
so it cannot be contained in the countable set `s`. -/
theorem exists_Ioo_notMem_of_countable {ε : ℝ} (hε : 0 < ε) {s : Set ℝ} (hs : s.Countable) :
    ∃ η : ℝ, η ∈ Set.Ioo 0 ε ∧ η ∉ s := by
  by_contra h
  push Not at h
  exact absurd (hs.mono fun x hx => h x hx)
    (by rw [Cardinal.Real.Ioo_countable_iff]; linarith)

end Work.ELRig
