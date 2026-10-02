import Mathlib
import Submission.Work.LandLeaves.Defs
import Submission.Work.Landing.Rays
import Submission.Work.Landing.Rays.isBounded_dynRay_sublevel

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.LandLeaves

/-- The accumulation set of a dynamic ray is the intersection, over all `ρ > 1`, of the closures of
the ray points whose Böttcher modulus is at most `ρ`. -/
theorem rayAccum_eq_iInter_closure (c : ℂ) (φ : ℂ → ℂ) (θ : ℝ) :
    Work.Landing.rayAccum c φ θ
      = ⋂ ρ : ℝ, ⋂ (_ : ρ ∈ Set.Ioi (1 : ℝ)),
          closure {z : ℂ | z ∈ Work.Landing.dynRay c φ θ ∧ ‖φ z‖ ≤ ρ} := by
  ext x
  simp [Work.Landing.rayAccum, Set.mem_Ioi]

/-- **The accumulation set of a dynamic ray is compact.**  It is the intersection of the closed
sets `closure {z ∈ R_c(θ) : ‖φ z‖ ≤ ρ}` over `ρ > 1`, hence closed; and it is contained in the
single one of them at `ρ = 2`, which is bounded by `isBounded_dynRay_sublevel` (the asymptotic
clause of the Böttcher coordinate `φ z ≈ z` bounds ray points with bounded Böttcher modulus).  In
the proper space `ℂ`, closed and bounded is compact. -/
theorem isCompact_rayAccum {c : ℂ} {φ : ℂ → ℂ} (h : Work.ParamRays.IsDynBottcher c φ) (θ : ℝ) :
    IsCompact (Work.Landing.rayAccum c φ θ) := by
  rw [Metric.isCompact_iff_isClosed_bounded]
  constructor
  · rw [rayAccum_eq_iInter_closure]
    exact isClosed_iInter fun ρ => isClosed_iInter fun _ => isClosed_closure
  · exact (Work.Landing.Rays.isBounded_dynRay_sublevel h θ 2).closure.subset
      (fun x hx => hx 2 (by norm_num))

end Work.LandLeaves
