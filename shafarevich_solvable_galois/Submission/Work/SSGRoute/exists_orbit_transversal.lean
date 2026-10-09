import Mathlib
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.style.haveILetI false

namespace Work.SSGRoute

/-- Given an involution `σ` on a finite type `X` with no fixed points, there is a
function `r : X → X` choosing one representative from each two-element orbit
`{x, σ x}`: `r` is idempotent, satisfies `r x = x ∨ r x = σ x`, and is invariant
under `σ` (`r (σ x) = r x`). -/
theorem exists_orbit_transversal {X : Type*} [Finite X] (σ : X ≃ X)
    (hσ : ∀ x, σ (σ x) = x) (hfree : ∀ x, σ x ≠ x) :
    ∃ r : X → X, (∀ x, r (r x) = r x) ∧ (∀ x, r x = x ∨ r x = σ x) ∧
      (∀ x, r (σ x) = r x) := by
  classical
  haveI : Fintype X := Fintype.ofFinite X
  -- A linear order on `X` obtained from a fixed enumeration `X ≃ Fin (card X)`.
  let e : X ≃ Fin (Fintype.card X) := Fintype.equivFin X
  -- Pick, from each pair `{x, σ x}`, the smaller element.
  let r : X → X := fun x => if e x ≤ e (σ x) then x else σ x
  have hne : ∀ x, e (σ x) ≠ e x := fun x h => hfree x (e.injective h)
  have hr : ∀ x, r x = x ∨ r x = σ x := by
    intro x
    by_cases h : e x ≤ e (σ x)
    · left; simp only [r, if_pos h]
    · right; simp only [r, if_neg h]
  have hfix : ∀ x, r (σ x) = r x := by
    intro x
    simp only [r]
    rw [hσ x]
    by_cases h : e x ≤ e (σ x)
    · have h2 : ¬ e (σ x) ≤ e x := by
        intro hle; exact hne x (le_antisymm hle h)
      simp only [if_pos h, if_neg h2]
    · have h2 : e (σ x) ≤ e x := (le_total (e (σ x)) (e x)).resolve_right h
      simp only [if_neg h, if_pos h2]
  have hidem : ∀ x, r (r x) = r x := by
    intro x
    rcases hr x with h | h
    · rw [h]; exact h
    · rw [h, hfix]; exact h
  exact ⟨r, hidem, hr, hfix⟩

end Work.SSGRoute
