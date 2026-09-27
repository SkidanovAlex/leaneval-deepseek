import Mathlib
import Submission.Work.Whitney.BumpModel.Defs

namespace Work.Whitney.BumpModel

open scoped Manifold ContDiff
open Set Filter Topology

open Work.Whitney

/-- The second block of the structure map vanishes exactly where the cut-off `χ` does: the second
block is `û(x) • (e₀ + x₀ • (x - x₀ • e₀))` with `û = χ/(1 + ∑ xᵢ²)`, and the vector
`e₀ + x₀ • (x - x₀ • e₀)` has zeroth coordinate `1`, hence is never zero. -/
theorem structMap_snd_ne_zero (n : ℕ) [NeZero n] {χ : (Fin n → ℝ) → ℝ} (x : Fin n → ℝ) :
    (structMap n χ x).2 ≠ 0 ↔ χ x ≠ 0 := by
  -- the zeroth coordinate of the second block is exactly `û x`
  have hcoord : (structMap n χ x).2 0 = uhat n χ x := by
    have h := congrFun (congrArg Prod.snd (structMap_apply n (χ := χ) x)) 0
    simpa using h
  constructor
  · intro h hχ
    exact h (by rw [structMap_snd]; simp [uhat, hχ])
  · intro hχ hzero
    have h0 : uhat n χ x = 0 := by rw [← hcoord, hzero]; rfl
    have hb : bumpU n x ≠ 0 := ne_of_gt (bumpU_pos n x)
    have hχ0 : χ x = 0 := by
      rw [uhat, div_eq_zero_iff] at h0
      rcases h0 with h | h
      · exact h
      · exact absurd h hb
    exact hχ hχ0

end Work.Whitney.BumpModel
