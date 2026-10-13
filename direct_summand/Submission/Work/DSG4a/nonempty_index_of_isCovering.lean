import Mathlib

namespace Work.DSG4a

open CategoryTheory AlgebraicGeometry Limits
universe u
-- A family of opens of a nonempty scheme that covers the scheme must be indexed by a nonempty
-- type.  Reviewer advice: the cleanest route is by contradiction on `¬ Nonempty ι`
-- (`not_nonempty_iff` gives `IsEmpty ι`, then `iSup_eq_bot.mpr (fun i => isEmptyElim i)` gives
-- `⨆ i, U i = ⊥`, so `hcov` gives `⊤ = ⊥` in `X.Opens`, which is absurd since a point of `X`
-- lies in `⊤`).
theorem nonempty_index_of_isCovering {X : AlgebraicGeometry.Scheme.{u}} [Nonempty X] {ι : Type u}
    (U : ι → X.Opens) (hcov : ⨆ i, U i = ⊤) : Nonempty ι := by
  by_contra h
  -- If `ι` is empty, the supremum of the `U i` is `⊥`.
  have hbot : (⨆ i, U i) = (⊥ : X.Opens) :=
    iSup_eq_bot.mpr fun i => absurd ⟨i⟩ h
  -- Hence `⊤ = ⊥` in `X.Opens`, which is absurd because `X` has a point.
  obtain ⟨x⟩ := ‹Nonempty X›
  have hx : x ∈ (⊤ : X.Opens) := trivial
  rw [← hcov, hbot] at hx
  exact hx

end Work.DSG4a
