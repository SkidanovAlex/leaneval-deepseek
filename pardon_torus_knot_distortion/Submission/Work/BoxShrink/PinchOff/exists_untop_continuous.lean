import Mathlib

namespace Work.BoxShrink.PinchOff

/-- **A continuous "finite part" for the Riemann sphere.**

There is a function `u : OnePoint ℂ → ℂ` which is a section of the inclusion `ℂ ↪ OnePoint ℂ` on
the complement of `∞` (i.e. `↑(u z) = z` for `z ≠ ∞`) and which is continuous at every point
different from `∞`.  (`u` may be taken to be the inverse of the open embedding
`OnePoint.some : ℂ → OnePoint ℂ` extended by `0` at `∞`.)
-/
theorem exists_untop_continuous :
    ∃ u : OnePoint ℂ → ℂ, (∀ z : OnePoint ℂ, z ≠ OnePoint.infty → (u z : OnePoint ℂ) = z) ∧
      (∀ z : OnePoint ℂ, z ≠ OnePoint.infty → ContinuousAt u z) := by
  refine ⟨fun z => z.elim 0 (fun w => w), ?_, ?_⟩
  · intro z hz
    obtain ⟨w, rfl⟩ := OnePoint.ne_infty_iff_exists.mp hz
    rfl
  · intro z hz
    obtain ⟨w, rfl⟩ := OnePoint.ne_infty_iff_exists.mp hz
    rw [OnePoint.continuousAt_coe]
    exact continuousAt_id

end Work.BoxShrink.PinchOff
