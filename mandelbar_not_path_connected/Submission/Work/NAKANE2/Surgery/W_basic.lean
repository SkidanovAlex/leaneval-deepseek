import Mathlib
import Submission.Work.NAKANE2.Defs
import Submission.Work.ParamRaysCrit.GreenLevel

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.NAKANE2.Surgery

open LeanEval.ComplexAnalysis (Tantibar)

/-- **Basic properties of the forward-invariant conformal region `W`.**

`W c₀ = {z | (3/4) G_{c₀}(c₀) < G_{c₀}(z)}` is the superlevel set of the dynamical Green
function `G_{c₀} = Work.ParamRays.greenFun c₀` above the threshold `(3/4) G_{c₀}(c₀)`, which is
positive by the band condition of the surgery datum.

* It is **open** and **preconnected**: `W c₀ = {z | r < G_{c₀} z}` with `r = (3/4) G_{c₀}(c₀) > 0`,
  and superlevel sets of the Green function above a positive level are open
  (`Work.ParamRays.isOpen_lt_greenFun`) and preconnected
  (`Work.ParamRays.isPreconnected_greenFun_gt`).
* It is **forward invariant** under `T_{c₀}`: the functional equation
  `G_{c₀}(T_{c₀} z) = 2 G_{c₀} z` (`Work.ParamRays.greenFun_orbit` at `n = 1`) doubles the
  potential, so `G_{c₀}(T_{c₀} z) = 2 G_{c₀} z > (3/2) G_{c₀}(c₀) > (3/4) G_{c₀}(c₀)`. -/
theorem W_basic {c₀ : ℂ} (D : Work.NAKANE2.SurgeryData c₀) :
    IsOpen (Work.NAKANE2.W c₀) ∧ IsPreconnected (Work.NAKANE2.W c₀) ∧
      (∀ z ∈ Work.NAKANE2.W c₀, LeanEval.ComplexAnalysis.Tantibar c₀ z ∈ Work.NAKANE2.W c₀) := by
  have hr : 0 < 3 / 4 * Gcrit c₀ := by
    have := D.Gcrit_pos
    linarith
  have hW : W c₀ = {z : ℂ | 3 / 4 * Gcrit c₀ < Work.ParamRays.greenFun c₀ z} := rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [hW]; exact Work.ParamRays.isOpen_lt_greenFun c₀ hr
  · rw [hW]; exact Work.ParamRays.isPreconnected_greenFun_gt c₀ hr
  · intro z hz
    rw [mem_W] at hz ⊢
    have h1 : G c₀ (LeanEval.ComplexAnalysis.Tantibar c₀ z) = 2 * G c₀ z := by
      have h := Work.ParamRays.greenFun_orbit c₀ z 1
      rw [Work.ParamRays.orbit_succ c₀ z 0, Work.ParamRays.orbit_zero, pow_one] at h
      exact h
    rw [h1]
    have hpos := D.Gcrit_pos
    linarith

end Work.NAKANE2.Surgery
