import Mathlib

/-!
# Self-maps of the disk model of `ℝP²`

A *disk model* of `ℝP²` is the closed unit disk in which antipodal points of the boundary circle are
identified.  A map `χ : ℂ → ℂ` which presents the disk model against itself — the reparametrisations
that the end contribution's sweeps need, `END_CONTRIBUTION_STATUS.md` §5 — is a map of the closed disk
onto itself that is injective off the antipodal pairs of the boundary.  This file fixes that
vocabulary (`Work.Drive.DiskModelMap`) and proves the one elementary consequence the count of the
plane charts uses:

> **the preimage of an interior point of the disk is unique and interior.**

The conditions are exactly what a *continuous* self-map of the closed disk factoring through the
antipodal identification satisfies (plus surjectivity): `norm_le_one` and `norm_eq_one` say that the
closed disk and its boundary are preserved, `surjOn` that the disk is covered, and `injOn` that the
only identifications made are the antipodal pairs of the boundary circle.  No regularity is required
for the counting statement.

The relation to the seam of a plane chart is recorded separately: a chart `Q ∘ χ` is invariant under
the antipodal involution of the boundary circle when either `χ` is *odd* on the circle
(`χ (-z) = -χ z`, the case of a genuine self-map of `ℝP²`) or *even* there, together with the
antipodal invariance of `Q` itself.
-/

namespace Work.Drive

noncomputable section

/-- **A self-map of the disk model of `ℝP²`**: it maps the closed unit disk into itself and its
boundary into itself, covers the disk, and makes no identification other than the antipodal pairs of
the boundary circle. -/
structure DiskModelMap (χ : ℂ → ℂ) : Prop where
  /-- The closed disk is mapped into itself. -/
  norm_le_one : ∀ z : ℂ, ‖z‖ ≤ 1 → ‖χ z‖ ≤ 1
  /-- The boundary circle is mapped into itself. -/
  norm_eq_one : ∀ z : ℂ, ‖z‖ = 1 → ‖χ z‖ = 1
  /-- Every point of the closed disk is attained. -/
  surjOn : ∀ w : ℂ, ‖w‖ ≤ 1 → ∃ z : ℂ, ‖z‖ ≤ 1 ∧ χ z = w
  /-- The only collisions are the antipodal pairs of the boundary circle. -/
  injOn : ∀ z z' : ℂ, ‖z‖ ≤ 1 → ‖z'‖ ≤ 1 → χ z = χ z' → z = z' ∨ (‖z‖ = 1 ∧ z' = -z)

/-- The identity is a self-map of the disk model. -/
theorem DiskModelMap.id : DiskModelMap id where
  norm_le_one _ h := h
  norm_eq_one _ h := h
  surjOn w hw := ⟨w, hw, rfl⟩
  injOn z z' _ _ h := Or.inl h

/-- The antipodal map is a self-map of the disk model. -/
theorem DiskModelMap.neg : DiskModelMap (fun z : ℂ => -z) where
  norm_le_one z hz := by simpa using hz
  norm_eq_one z hz := by simpa using hz
  surjOn w hw := ⟨-w, by simpa using hw, by simp⟩
  injOn z z' _ _ h := Or.inl (neg_inj.mp h)

/-- **The preimage of an interior point of the disk model is unique and interior.** -/
theorem DiskModelMap.existsUnique_norm_lt_one {χ : ℂ → ℂ} (hχ : DiskModelMap χ) {w : ℂ}
    (hw : ‖w‖ < 1) : ∃! z : ℂ, ‖z‖ < 1 ∧ χ z = w := by
  obtain ⟨z, hz, hzw⟩ := hχ.surjOn w (le_of_lt hw)
  have hzne : ‖z‖ ≠ 1 := by
    intro hz1
    have : ‖w‖ = 1 := by rw [← hzw, hχ.norm_eq_one z hz1]
    exact absurd this (ne_of_lt hw)
  refine ⟨z, ⟨lt_of_le_of_ne hz hzne, hzw⟩, ?_⟩
  rintro z' ⟨hz'lt, hz'w⟩
  rcases hχ.injOn z' z (le_of_lt hz'lt) hz (by rw [hz'w, hzw]) with h | ⟨hz'1, -⟩
  · exact h
  · exact absurd hz'1 (ne_of_lt hz'lt)

end

end Work.Drive
