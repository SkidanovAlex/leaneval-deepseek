import Mathlib
import Submission.Work.Profiles.Basic
import Submission.Work.Profiles.Eta

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Profiles

open scoped ContDiff

theorem deriv2_nonneg_of_convexOn_smooth {f : ℝ → ℝ} (hc : ConvexOn ℝ Set.univ f)
    (hs : ContDiff ℝ ∞ f) (x : ℝ) : 0 ≤ deriv^[2] f x := by
  -- `f` is convex and smooth on `ℝ`, hence its derivative `deriv f` is monotone.
  have hd : Differentiable ℝ f := hs.differentiable (by simp)
  have hmono : Monotone (deriv f) := fun a b hab =>
    hc.monotoneOn_deriv (fun y _ => hd y) (Set.mem_univ a) (Set.mem_univ b) hab
  -- The second derivative of `f` is the derivative of the monotone function `deriv f`.
  have h2 : deriv^[2] f x = deriv (deriv f) x := by
    simp [Function.iterate_succ, Function.comp_apply]
  rw [h2]
  exact hmono.deriv_nonneg

end Work.Profiles
