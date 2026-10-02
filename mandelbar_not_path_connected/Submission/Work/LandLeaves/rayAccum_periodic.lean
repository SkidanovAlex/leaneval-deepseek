/-
Copyright: subproject `Submission/Work/LandLeaves/` of `mandelbar_not_path_connected`.

# The accumulation set of a periodic ray is invariant

The second structural ingredient of the direct ("no local connectivity", Milnor 18.10) proof of
the landing theorem: the accumulation set of the ray at a *periodic* angle is carried onto itself
by the corresponding iterate of `T_c`.

`Work.Landing.rayAccum_iterate` gives the transfer
`rayAccum c φ ((angDouble)^[n] θ) = (T_c)^[n] '' rayAccum c φ θ`; for a periodic angle
(`PeriodicAngle θ k`) this reads `(T_c)^[k] '' rayAccum c φ θ = rayAccum c φ θ`, so the
accumulation set is a nonempty compact (Work.LandLeaves.rayAccum_nonempty,
Work.LandLeaves.isCompact_rayAccum) invariant set on which `(T_c)^[k]` acts — the object to which
the expansion argument of Milnor 18.10 applies.
-/
import Submission.Work.LandLeaves.Defs
import Submission.Work.LandLeaves.rayAccum_nonempty
import Submission.Work.LandLeaves.isCompact_rayAccum
import Submission.Work.Landing.Land.Landing

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.LandLeaves

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

/-- **Invariance of the accumulation set of a periodic ray**: for a Böttcher coordinate `φ` and a
periodic angle `θ` of period `k`, the iterate `(T_c)^[k]` maps `rayAccum c φ θ` onto itself. -/
theorem rayAccum_iterate_image {c : ℂ} {φ : ℂ → ℂ} (h : Work.ParamRays.IsDynBottcher c φ)
    {θ : ℝ} {k : ℕ} (hper : Work.Landing.PeriodicAngle θ k) :
    (Tantibar c)^[k] '' Work.Landing.rayAccum c φ θ = Work.Landing.rayAccum c φ θ := by
  rw [← Work.Landing.rayAccum_iterate h θ k, hper]

/-- The accumulation set of a periodic ray is mapped *into* itself by the return map. -/
theorem image_rayAccum_subset {c : ℂ} {φ : ℂ → ℂ} (h : Work.ParamRays.IsDynBottcher c φ)
    {θ : ℝ} {k : ℕ} (hper : Work.Landing.PeriodicAngle θ k) :
    (Tantibar c)^[k] '' Work.Landing.rayAccum c φ θ ⊆ Work.Landing.rayAccum c φ θ :=
  (rayAccum_iterate_image h hper).le

end Work.LandLeaves
