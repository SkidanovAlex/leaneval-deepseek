import Mathlib
import Submission.Work.Cohomology.Singular
import Submission.Work.Cohomology.euclidean_top_homology_vanishing
import Submission.Work.Cohomology.euclidean_open_homology_gt_vanishing

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The homology of an open subset of `ℝ^N` vanishes in degrees `≥ N`

For an open subset `W ⊆ ℝ^N` (`N ≥ 1`) and every `m ≥ N`, the singular homology `H_m(W; ℤ)`
vanishes.

This is the "dimension bound" for open subsets of Euclidean space: an open subset of `ℝ^N` is a
topological `N`-manifold, so Hatcher's Lemma 3.27(b) gives `H_m(W) = 0` for `m > N`, while the
top degree `m = N` is the non-compactness phenomenon (Hatcher, *Algebraic Topology*,
Proposition 3.29: a connected non-compact `n`-manifold has `H_i = 0` for `i ≥ n`).

The two cases are proved in the companion modules:

* `Work.Cohomology.euclidean_open_homology_gt_vanishing` (`Submission/Work/Cohomology/euclidean_open_homology_gt_vanishing.lean`):
  `H_m(W) = 0` for `m > N`.  A class is represented by a cycle of compact support `K`; choosing an
  open `U` and a compact `A` with `K ⊆ U ⊆ A ⊆ W` (thickenings of `K`), the long exact sequence of
  the triple `(W∖A) ⊆ (W∖(A∖U)) ⊆ W` together with Lemma 3.27(b) — the relative vanishing
  `H_j(W, W∖C) = 0` for compact `C ⊆ W`, `j > N` (`relChains_vanishing_compact_specific`) —
  forces `H_m(U) = 0`, and the class lies in the image of `H_m(U) → H_m(W)`.

* `Work.Cohomology.euclidean_top_homology_vanishing` (`Submission/Work/Cohomology/euclidean_top_homology_vanishing.lean`):
  `H_N(W) = 0`.  Complements of compact sets have vanishing `H_j` in degrees `j ≥ N` (the pair
  sequence of `(ℝ^N, ℝ^N∖A)` plus Lemma 3.27(b)), Mayer–Vietoris for the disjoint open cover
  `ℝ^N∖A = W ⊔ (ℝ^N∖closure W)` of a bounded `W` gives `H_N(W) = 0` there, and an arbitrary open
  `W` is an increasing union of bounded open sets, so every class of `H_N(W)` comes from a finite
  stage.

## Main result

* `euclidean_open_homology_vanishing` — `H_m(W; ℤ) = 0` for every open `W ⊆ ℝ^N` and every `m ≥ N`.
-/

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

namespace Work.Cohomology

noncomputable section

/-- **The singular homology of an open subset of `ℝ^N` vanishes in degrees `≥ N`.**

With `ℤ` coefficients, for `W ⊆ ℝ^N` open (`N ≥ 1`) and every `m ≥ N`, the `m`-th singular
homology of `W` is the zero object of `ModuleCat ℤ`. -/
theorem euclidean_open_homology_vanishing {N : ℕ} (hN : 1 ≤ N)
    (W : Set (EuclideanSpace ℝ (Fin N))) (hW : IsOpen W) :
    ∀ m, N ≤ m → CategoryTheory.Limits.IsZero
      ((Work.Cohomology.singularChains ℤ (TopCat.of ↥W)).homology m) := by
  intro m hm
  rcases eq_or_lt_of_le hm with h | h
  · rw [← h]
    exact euclidean_top_homology_vanishing hN W hW
  · exact euclidean_open_homology_gt_vanishing hN W hW m h

end

end Work.Cohomology
