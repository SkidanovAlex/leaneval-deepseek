import Mathlib
import Submission.Work.Drive.Generic.HeightDefs

namespace Work.Drive.Generic

/-- At a point where the differential of `Φ` is injective, the two partial derivatives `∂₁Φ` and
`∂₂Φ` are linearly independent, hence the Gauss map `normal Φ = ∂₁Φ ⨯ ∂₂Φ` does not vanish. -/
theorem normal_ne_zero {Φ : ℝ × ℝ → Work.Drive.Generic.E3} (hΦ : ContDiff ℝ 3 Φ)
    (himm : ∀ p, Function.Injective (fderiv ℝ Φ p)) (p : ℝ × ℝ) :
    Work.Drive.Generic.normal Φ p ≠ 0 := by
  rw [normal, crossE_ne_zero_iff]
  intro c d hcd
  have hcd' : c • fderiv ℝ Φ p (1, 0) + d • fderiv ℝ Φ p (0, 1) = 0 := by
    simpa only [d1, d2] using hcd
  have hL : fderiv ℝ Φ p (c, d) = 0 := by
    have hdecomp : (c, d) = c • ((1 : ℝ), (0 : ℝ)) + d • ((0 : ℝ), (1 : ℝ)) := by
      ext <;> simp
    rw [hdecomp, map_add, map_smul, map_smul, hcd']
  have hp : (c, d) = (0 : ℝ × ℝ) := himm p (by rw [hL, map_zero])
  exact ⟨by simpa using congrArg Prod.fst hp, by simpa using congrArg Prod.snd hp⟩

end Work.Drive.Generic
