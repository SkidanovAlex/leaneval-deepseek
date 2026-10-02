import Mathlib
import Submission.Work.Bottcher.All
import Submission.Work.ParamRays.Bottcher
import Submission.Work.SeedDyn.Main

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Landing.Rays

/-- **The level point of a dynamical ray at a mandelbar parameter.**

For `c` in the mandelbar the escaping set carries a Böttcher coordinate, and the Böttcher
coordinate is a homeomorphism onto the exterior disc.  Consequently, for every `τ > 1` and every
angle `θ`, there is exactly one escaping point `z` whose Böttcher coordinate equals `τ e^{2πiθ}`,
i.e. the unique point of the dynamical ray `R_c(θ)` at level `τ`.  By uniqueness of the Böttcher
coordinate the value `φ z` is the same for *every* `φ` with `IsDynBottcher c φ`. -/
theorem levelPoint_of_mem_mandelbar (c : ℂ) (hc : c ∈ LeanEval.ComplexAnalysis.Mandelbar)
    {τ : ℝ} (hτ : 1 < τ) (θ : ℝ) :
    ∃! z : ℂ, Work.ParamRays.Escaping c z ∧
      ∀ φ : ℂ → ℂ, Work.ParamRays.IsDynBottcher c φ → φ z = (τ : ℂ) * Work.ParamRays.rayDir θ := by
  obtain ⟨hφ, hinj, hsurj⟩ := Work.SeedDyn.isDynBottcherHomeo hc
  -- the target value `τ * rayDir θ` lies outside the closed unit disc
  have hw : 1 < ‖(τ : ℂ) * Work.ParamRays.rayDir θ‖ := by
    rw [norm_mul, Work.ParamRays.norm_rayDir, mul_one, Complex.norm_of_nonneg (by linarith : (0 : ℝ) ≤ τ)]
    exact hτ
  -- surjectivity of the Böttcher coordinate produces the point
  obtain ⟨z, hzesc, hzφ⟩ := hsurj _ hw
  refine ⟨z, ⟨hzesc, ?_⟩, ?_⟩
  · -- the value is independent of the Böttcher coordinate, by uniqueness
    intro ψ hψ
    rw [Work.ParamRays.isDynBottcher_unique hψ hφ hzesc, hzφ]
  · -- uniqueness of the point, by injectivity of the Böttcher coordinate on the escaping set
    rintro z' ⟨hz'esc, hz'⟩
    exact hinj z' z hz'esc hzesc (by rw [hz' _ hφ, hzφ])

end Work.Landing.Rays
