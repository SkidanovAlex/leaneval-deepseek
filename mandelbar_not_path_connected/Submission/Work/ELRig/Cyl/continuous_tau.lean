import Mathlib
import Submission.Work.ELRig.CylLift
import Submission.Work.ELRig.analyticOnNhd_dynBottcher

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.ELRig.Cyl

theorem continuous_tau {c : ℂ} (d : Work.EL.RootParabolic c)
    (fl : Work.EL.ParabolicFlower (Work.EL.F c) ((LeanEval.ComplexAnalysis.Tantibar c)^[5]) d.z₁)
    (L : Work.ELRig.RayCylLift d fl) : Continuous L.τ ∧
      (∀ s : ℝ, L.τ s = Real.exp (Work.EL.pot d.hN (fl.Ψ (L.γ₁ s)))) := by
  -- The level `τ s` is the exponential of the potential of the `Ψ`-image of the lift point:
  -- `Ψ (γ₁ s)` is the ray point of level `τ s`, whose potential is `log (τ s)`.
  have hform : ∀ s : ℝ, L.τ s = Real.exp (Work.EL.pot d.hN (fl.Ψ (L.γ₁ s))) := by
    intro s
    rw [L.hΨ₁ s, Work.EL.pot_rayPt d.hN (L.hτ1 s)]
    exact (Real.exp_log (by linarith [L.hτ1 s])).symm
  refine ⟨?_, hform⟩
  -- Continuity: the right-hand side is the composite of the continuous `exp`, the continuous
  -- potential `pot` (a field of the Böttcher data), the entire `Ψ`, and `γ₁`.
  have hc : Continuous fun s : ℝ => Real.exp (Work.EL.pot d.hN (fl.Ψ (L.γ₁ s))) :=
    Real.continuous_exp.comp
      (d.hN.continuous_potential.comp (fl.Ψ_diff.continuous.comp L.cont₁))
  rw [funext hform]
  exact hc

end Work.ELRig.Cyl
