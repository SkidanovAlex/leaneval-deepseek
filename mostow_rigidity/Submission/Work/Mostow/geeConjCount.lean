import Mathlib
import Submission.Work.Mostow.conjCount

/-!
# `geeConjCount`

The number of conjugates `γ⁻¹ * b * γ` of an element `b` of a discrete subgroup `Γ ≤ PO n 1`
(with `b` fixing a point of `ℍⁿ`, i.e. `b` of finite order) that are `η₁`-near the identity at a
point `w` is bounded by a constant `C` depending only on `n`.

This is the statement of `Work.Mostow.conjCount`, restated with the subgroup and the element
introduced in the order `(Γ) (b)` and with the discreteness hypothesis placed after them, so that
callers can supply the structural hypotheses in the order they occur in `gapA`.
-/

namespace Work.Mostow

theorem geeConjCount (n : ℕ) (hn : 2 ≤ n) (hA : Submission.Mostow.POActionProp n) (hI : Submission.Mostow.HypIsometryProp n) :
    ∃ η₁ : ℝ, 0 < η₁ ∧ ∃ C : ℕ, ∀ (Γ : Subgroup (LeanEval.Geometry.MostowRigidity.PO n 1)) (b : LeanEval.Geometry.MostowRigidity.PO n 1),
      _root_.IsDiscrete (Γ : Set (LeanEval.Geometry.MostowRigidity.PO n 1)) → b ∈ Γ → (∃ p : Submission.Mostow.E n, b • p = p) → ∀ w : Submission.Mostow.E n, Submission.Mostow.NearIdAt b w η₁ →
        {c : LeanEval.Geometry.MostowRigidity.PO n 1 | Submission.Mostow.NearIdAt c w η₁ ∧ ∃ γ ∈ Γ, c = γ⁻¹ * b * γ}.Finite ∧
        {c : LeanEval.Geometry.MostowRigidity.PO n 1 | Submission.Mostow.NearIdAt c w η₁ ∧ ∃ γ ∈ Γ, c = γ⁻¹ * b * γ}.ncard ≤ C := by
  obtain ⟨η₁, hη₁pos, C, hC⟩ := conjCount n hn hA hI
  exact ⟨η₁, hη₁pos, C, fun Γ b hdisc hb hbfix w hw => hC Γ hdisc b hb hbfix w hw⟩

end Work.Mostow
