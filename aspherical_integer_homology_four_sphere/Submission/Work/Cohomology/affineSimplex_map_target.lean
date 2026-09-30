import Mathlib
import Submission.Work.Cohomology.Affine

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Naturality of the affine simplex in the target simplex

For a map of vertex sets `f : Fin (n+1) → Fin (m+1)` (thought of as a simplicial map
`Δⁿ → Δᵐ` on vertices), pushing an affine combination forward along `f` commutes with
forming affine combinations: the push-forward `stdSimplex.map f` is the linear extension
of `f` on `Δⁿ`, so

`stdSimplex.map f (affineSimplex w t) = affineSimplex (fun j => stdSimplex.map f (w j)) t`.

This is the target-side counterpart of the source-side functoriality
`affineSimplex_stdSimplex_map` in `Submission/Work/Cohomology/linSimplex_boundary.lean`.
-/

set_option backward.isDefEq.respectTransparency false

open scoped BigOperators

namespace Work.Cohomology

noncomputable section

theorem affineSimplex_map_target {n m k : ℕ} (f : Fin (n + 1) → Fin (m + 1))
    (w : Fin (k + 1) → stdSimplex ℝ (Fin (n + 1))) (t : stdSimplex ℝ (Fin (k + 1))) :
    stdSimplex.map f (affineSimplex w t) =
      affineSimplex (fun j => stdSimplex.map f (w j)) t := by
  ext y
  simp only [affineSimplex_apply, stdSimplex.map_coe, FunOnFinite.linearMap_apply_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.mul_sum]

end

end Work.Cohomology
