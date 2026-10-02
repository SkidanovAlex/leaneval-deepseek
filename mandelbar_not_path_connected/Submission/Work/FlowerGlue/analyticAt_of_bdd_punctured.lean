import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Bounded functions on a punctured disk extend analytically

If `f : ℂ → ℂ` is complex differentiable on the punctured disk `ball 0 R \ {0}`
(`R > 0`) and is bounded there (its norm is bounded above on that set), then `f`
has a removable singularity at `0`: there is a function `F` analytic at `0`
which agrees with `f` on a punctured neighbourhood of `0`.

This is the "bounded" case of Riemann's removable singularity theorem, phrased
in terms of the crude hypothesis `BddAbove (norm ∘ f '' (ball 0 R \ {0}))`
(the companion of `Complex.differentiableOn_update_limUnder_of_bddAbove`) and in
the "eventually equal near the point" form needed by the FlowerGlue layer.
-/

open scoped Topology
open Filter

namespace Work.FlowerGlue

/-- **Riemann's removable singularity theorem, bounded form.** A function which
is complex differentiable and bounded on a punctured disk extends to an analytic
function at the centre. -/
theorem analyticAt_of_bdd_punctured {f : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hd : DifferentiableOn ℂ f (Metric.ball 0 R \ {0}))
    (hb : BddAbove (norm ∘ f '' (Metric.ball 0 R \ {0}))) :
    ∃ F : ℂ → ℂ, AnalyticAt ℂ F 0 ∧ F =ᶠ[nhdsWithin (0 : ℂ) {0}ᶜ] f := by
  -- The candidate extension: fill in the (existing) limit of `f` at `0`.
  refine ⟨Function.update f 0 ((nhdsWithin (0 : ℂ) {0}ᶜ).limUnder f), ?_, ?_⟩
  · -- `ball 0 R` is a neighbourhood of `0`, so the removable singularity theorem
    -- makes the extension differentiable on it, hence analytic at `0`.
    exact (Complex.differentiableOn_update_limUnder_of_bddAbove
      (Metric.ball_mem_nhds 0 hR) hd hb).analyticAt (Metric.ball_mem_nhds 0 hR)
  · -- The extension differs from `f` only at `0`.
    rw [Filter.eventuallyEq_iff_exists_mem]
    exact ⟨{0}ᶜ, self_mem_nhdsWithin, fun z hz => Function.update_of_ne hz _ _⟩

end Work.FlowerGlue
