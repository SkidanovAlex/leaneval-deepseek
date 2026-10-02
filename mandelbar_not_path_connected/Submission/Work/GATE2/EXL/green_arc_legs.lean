import Mathlib
import Submission.Work.ELRig.CylLift
import Submission.Work.GATE2.EXL.exitLoop_exists

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

namespace Work.GATE2.EXL

open LeanEval.ComplexAnalysis (Tantibar)

theorem green_arc_legs {c : ℂ} {d : Work.EL.RootParabolic c}
    (fl : Work.EL.ParabolicFlower (Work.EL.F c) ((LeanEval.ComplexAnalysis.Tantibar c)^[5]) d.z₁)
    {θ₀ p : ℝ} (A : C(unitInterval, ℂ))
    (hangle : ∀ r : unitInterval,
      fl.Ψ (A r) = Work.EL.rayPt d.hN (θ₀ + (r : ℝ) * (Work.EL.alpha1 - θ₀)) (Real.exp p))
    (hp : 0 < p) :
    (∀ r : unitInterval, Work.Bottcher.green c (fl.Ψ (A r)) = p) ∧
    (∀ r : unitInterval, Work.Bottcher.green c (fl.Ψ (A r - 1)) = p / 1024) := by
  have h1 : ∀ r : unitInterval, Work.Bottcher.green c (fl.Ψ (A r)) = p := by
    intro r
    have hK : fl.Ψ (A r) ∉ Work.EL.K c := by
      rw [hangle r]
      exact Work.EL.rayPt_notMem_K d.hN (Real.one_lt_exp_iff.mpr hp)
    rw [green_eq_pot d.hN d.bottcher hK, hangle r,
      Work.EL.pot_rayPt d.hN (Real.one_lt_exp_iff.mpr hp), Real.log_exp]
  refine ⟨h1, fun r => ?_⟩
  have hshift : fl.Ψ (A r) = Work.EL.F c (fl.Ψ (A r - 1)) := by
    have h := fl.Ψ_shift (A r - 1)
    rw [sub_add_cancel] at h
    exact h
  have hg := green_F c (fl.Ψ (A r - 1))
  rw [← hshift] at hg
  rw [h1 r] at hg
  linarith

end Work.GATE2.EXL
