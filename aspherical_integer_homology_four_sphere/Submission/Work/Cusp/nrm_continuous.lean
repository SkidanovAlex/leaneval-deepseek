import Mathlib
import Submission.Work.Cusp.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Cusp

/-- The layer parameter `nrm p = max |p 0| |p 1|` is continuous on `E2 = ℝ²`.
`E2 = EuclideanSpace ℝ (Fin 2)` is `WithLp 2 (Fin 2 → ℝ)`, whose topology is induced by
`WithLp.ofLp`, so `p ↦ p 0` is the composite of the continuous projection
`WithLp.ofLp : E2 → (Fin 2 → ℝ)` with the continuous coordinate map `f ↦ f 0`. -/
theorem nrm_continuous : Continuous nrm := by
  unfold nrm
  have h0 : Continuous (fun p : E2 => p.ofLp 0) :=
    (continuous_apply 0).comp (PiLp.continuous_ofLp 2 (fun _ : Fin 2 => ℝ))
  have h1 : Continuous (fun p : E2 => p.ofLp 1) :=
    (continuous_apply 1).comp (PiLp.continuous_ofLp 2 (fun _ : Fin 2 => ℝ))
  exact h0.abs.max h1.abs

end Work.Cusp
