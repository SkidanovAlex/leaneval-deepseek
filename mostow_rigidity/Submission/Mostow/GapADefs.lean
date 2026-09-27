import Submission.Mostow.GeodDefs

/-!
# Lead-written vocabulary for the GAP-A chains (definitions only; DO NOT EDIT)
-/

open LeanEval.Geometry.MostowRigidity MeasureTheory

namespace Submission.Mostow

noncomputable section

/-- GAP-A (EscapeShort) for `Γ`: far from `Γ•K` some infinite-order element is `ε`-short. -/
def GapAProp {n : ℕ} (Γ : Subgroup (PO n 1)) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ K : Set (E n), IsCompact K ∧ ∀ u : E n, (∀ γ : Γ, (γ : PO n 1) • u ∉ K) →
    ∃ g : Γ, orderOf g = 0 ∧ hdist u ((g : PO n 1) • u) < ε

/-- chord length of a rotation angle: `2 sin(|x|/2)` (`‖x‖ ∈ [0, π]` is the arc distance to `0`) -/
def chord (x : AddCircle (2 * Real.pi)) : ℝ := 2 * Real.sin (‖x‖ / 2)

end

end Submission.Mostow
