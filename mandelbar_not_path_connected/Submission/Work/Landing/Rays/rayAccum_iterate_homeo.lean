import Mathlib
import Submission.Work.Landing.Rays
import Submission.Work.Landing.Rays.rayAccum_image_homeo

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Landing.Rays

/-- Iterating the ray transfer: the accumulation set of the ray at angle `(angDouble)^[n] θ` is
the image under `(T_c)^[n]` of the accumulation set of the ray at angle `θ`. -/
theorem rayAccum_iterate_homeo {c : ℂ} {φ : ℂ → ℂ} (h : Work.Landing.IsDynBottcherHomeo c φ)
    (θ : ℝ) (n : ℕ) :
    Work.Landing.rayAccum c φ ((Work.Landing.angDouble)^[n] θ) =
      (LeanEval.ComplexAnalysis.Tantibar c)^[n] '' Work.Landing.rayAccum c φ θ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply',
      ← rayAccum_image_homeo h ((Work.Landing.angDouble)^[n] θ), ih]
    rw [Function.iterate_succ', Set.image_image]
    rfl

end Work.Landing.Rays
