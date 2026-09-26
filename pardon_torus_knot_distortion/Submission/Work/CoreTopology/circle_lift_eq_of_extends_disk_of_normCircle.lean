import Mathlib
import Submission.Work.CoreTopology.TorusDichotomyDefs

namespace Work.CoreTopology

/-- **A loop in the circle which extends to a nonvanishing continuous complex function on the
disc has vanishing winding number.**  Let `W : 𝔻 → ℂ` be continuous and nowhere vanishing on the
closed unit disc.  If `Λ : ℝ → ℝ` is continuous and the normalised boundary loop
`t ↦ normCircle (W (circlePoint t))` equals `Circle.exp ∘ Λ`, then `Λ (2π) = Λ 0`.  (Geometrically:
`W = (2 + cos φ) · exp (i θ)` on the torus, so its normalisation is a loop of the circle extending
over the disc.) -/
theorem circle_lift_eq_of_extends_disk_of_normCircle (W : Metric.closedBall (0 : ℂ) 1 → ℂ)
    (hW : Continuous W) (hW0 : ∀ z : Metric.closedBall (0 : ℂ) 1, W z ≠ 0)
    (Λ : ℝ → ℝ) (hΛ : Continuous Λ)
    (hlift : ∀ t : ℝ,
      normCircle (W (circlePoint t)) (hW0 (circlePoint t)) = Circle.exp (Λ t)) :
    Λ (2 * Real.pi) = Λ 0 := by
  -- The normalised boundary loop, as a circle-valued loop.
  let g : ℝ → Circle := fun t => normCircle (W (circlePoint t)) (hW0 (circlePoint t))
  have hg : Continuous g :=
    continuous_normCircle (fun t : ℝ => W (circlePoint t))
      (hW.comp continuous_circlePoint) (fun t => hW0 (circlePoint t))
  -- It is a loop: `circlePoint` is `2π`-periodic.
  have hper : ∀ t : ℝ, g (t + 2 * Real.pi) = g t := by
    intro t
    apply Subtype.ext
    simp only [g, normCircle_coe]
    rw [circlePoint_add_two_pi]
  -- It extends over the closed disc by normalising `W` pointwise.
  let G : C(Metric.closedBall (0 : ℂ) 1, Circle) :=
    ⟨fun z => normCircle (W z) (hW0 z), continuous_normCircle W hW hW0⟩
  have hG : ∀ θ : ℝ, G (circlePoint θ) = g θ := fun θ => rfl
  exact circle_lift_eq_of_extends_disk g hg hper G hG Λ hΛ (fun t => (hlift t).symm)

end Work.CoreTopology
