import Mathlib
import Submission.Work.Drive.OrderBase
import Submission.Work.Drive.muOrd_injective_unordered

namespace Work.Drive

/-- **The fixed-offset chord loop is an embedded circle in the interior of the configuration strip.**

For a smooth embedded closed plane curve `γ` and `w ∈ S¹`, `w ≠ 1`, the map
`x ↦ muOrd γ (x, x * w)` is the "constant offset `w`" chord loop of the configuration Möbius strip
`M = μ(Sym² S¹)`: it parameterises the chords of `γ` whose endpoints are separated by the fixed
rotation `w`.  Its image lies in `M` and stays away from the boundary `∂M` of the strip (which is the
diagonal `x = y`, i.e. `x ↦ muOrd γ (x,x)`), because the chords are non-degenerate (`w ≠ 1`).  It is
injective — i.e. it is a genuine embedded circle in `M`, not a double cover — exactly when `w² ≠ 1`,
i.e. `w ≠ ±1`; for `w = -1` the antipodal loop is 2 : 1 onto its image.

This packages the "essential loop `C₀` of the configuration strip" used as `γ_P` in the chain-level
description of Hugelmeyer's order (Stage 2 of `Submission/Work/Drive/CHAIN_ROUTE_NOTES.md`): the
fixed-offset loop goes once around the Möbius band, and `chord_loop_winding` shows that its direction
coordinate has non-zero degree (`±2`), the usable substitute in that route for the phrase
"homologically essential loop of the capped plane `P`". -/
theorem core_loop (γ : Circle → ℝ × ℝ)
    (hγ : Manifold.IsSmoothEmbedding (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
      (modelWithCornersSelf ℝ (ℝ × ℝ)) ((⊤ : ℕ∞) : WithTop ℕ∞) γ)
    {w : Circle} (hw : w ≠ 1) (hw_neg : w ≠ -1) :
    Function.Injective (fun x : Circle => Submission.Configuration.muOrd γ (x, x * w)) ∧
      (∀ x : Circle, (Submission.Configuration.muOrd γ (x, x * w)).2.2 ≠ 0) := by
  have hinj : Function.Injective γ := hγ.isEmbedding.injective
  constructor
  · -- Injectivity: two chords of `γ` with the same configuration have the same (unordered) endpoints.
    intro x y hxy
    -- `muOrd_injective_unordered` identifies the unordered pairs `{x, x*w}` and `{y, y*w}`.
    rcases Work.Drive.muOrd_injective_unordered hγ hxy with ⟨hx, _⟩ | ⟨hx, hy⟩
    · exact hx
    · -- The alternative is `x = y * w` and `x * w = y`, which forces `w * w = 1`, i.e. `w = ±1`.
      have hww : w * w = 1 := by
        have h1 : y * (w * w) = y := by
          calc y * (w * w) = (y * w) * w := by rw [mul_assoc]
            _ = x * w := by rw [← hx]
            _ = y := hy
        exact mul_left_cancel (a := y) (by rw [h1, mul_one])
      have hwwC : (w : ℂ) * (w : ℂ) = 1 := by
        have := congrArg (fun z : Circle => (z : ℂ)) hww
        simpa using this
      rcases mul_self_eq_one_iff.mp hwwC with h | h
      · exact absurd (Subtype.ext (by simpa using h)) hw
      · exact absurd (Subtype.ext (by simpa using h)) hw_neg
  · -- Non-degeneracy: `x ≠ x * w` because `w ≠ 1`, so the chord has non-zero Euclidean length.
    intro x
    have hne : γ x - γ (x * w) ≠ 0 := by
      intro h0
      have hγeq : γ x = γ (x * w) := sub_eq_zero.mp h0
      have hxw : x = x * w := hinj hγeq
      exact hw (mul_left_cancel (a := x) (b := w) (c := 1) (by rw [mul_one]; exact hxw.symm))
    have hpos := Submission.Geometry.eucNorm_pos hne
    simpa [Submission.Configuration.muOrd] using ne_of_gt hpos

end Work.Drive
