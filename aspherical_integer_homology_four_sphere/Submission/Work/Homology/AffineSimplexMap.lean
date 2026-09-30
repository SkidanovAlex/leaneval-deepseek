import Mathlib
import Submission.Work.Homology.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Affine maps out of the standard simplex

The singular simplex `Δ^m → Δ^N` determined by a family of points
`p : Fin (m+1) → Δ^N` is the affine map `s ↦ iConvexComb s p`.  Here we show
that this map is continuous, which is what makes it a singular simplex in the
topological sense.

The proof uses that, for a finite index type `M`, the topology on
`Convexity.StdSimplex ℝ M` is the one induced by the embedding
`t ↦ t.weights : StdSimplex ℝ M → (M → ℝ)`, and computes the coordinates of
`iConvexComb s p` explicitly.
-/

namespace Work.Homology

open Convexity

/-- Coordinates of an indexed convex combination of points of a standard simplex:
the `j`-th weight of `iConvexComb s p` is the weighted average of the `j`-th
weights of the `p i`. -/
theorem weights_iConvexComb_apply {m N : ℕ}
    (p : Fin (m + 1) → Convexity.StdSimplex ℝ (Fin (N + 1)))
    (s : Convexity.StdSimplex ℝ (Fin (m + 1))) (j : Fin (N + 1)) :
    (Convexity.iConvexComb s p).weights j = ∑ i, s.weights i * (p i).weights j := by
  simp only [Convexity.iConvexComb, Convexity.ConvexSpace.sConvexComb,
    Convexity.StdSimplex.weights_join, Convexity.StdSimplex.weights_map, Finsupp.sum_apply]
  rw [Finsupp.sum_mapDomain_index]
  · rw [Finsupp.sum_fintype]
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finsupp.smul_apply, smul_eq_mul]
    · intro i; simp
  · intro b; simp
  · intro b m₁ m₂; simp [add_mul]

/-- A family of points `p : Fin (m+1) → Δ^N` of the standard simplex defines a
continuous affine map `s ↦ iConvexComb s p : Δ^m → Δ^N`. -/
theorem AffineSimplexMap {m N : ℕ} (p : Fin (m + 1) → Convexity.StdSimplex ℝ (Fin (N + 1))) :
    Continuous (fun s : Convexity.StdSimplex ℝ (Fin (m + 1)) => Convexity.iConvexComb s p) := by
  rw [(Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin (N + 1))).continuous_iff]
  rw [continuous_pi_iff]
  intro j
  have key : (fun s : Convexity.StdSimplex ℝ (Fin (m + 1)) => (Convexity.iConvexComb s p).weights j)
      = fun s => ∑ i, s.weights i * (p i).weights j :=
    funext fun s => weights_iConvexComb_apply p s j
  change Continuous
    (fun s : Convexity.StdSimplex ℝ (Fin (m + 1)) => (Convexity.iConvexComb s p).weights j)
  rw [key]
  fun_prop

end Work.Homology
