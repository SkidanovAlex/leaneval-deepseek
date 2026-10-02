import Mathlib
import Submission.Work.Cohomology.pd_good
import Submission.Work.Cohomology.homology_vanishing_relative_compact

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# `H_j(I, I∖K) = 0` for `j > N`, `I ⊆ ℝᴺ` open and `K ⊆ I` compact

The relative (singular, `ℤ`-) homology of the pair `(I, I∖K)` vanishes above the dimension `N`,
for `I` an open subset of `ℝᴺ` and `K ⊆ I` compact.  This is Hatcher's Lemma 3.27
(`H_i(M, M∖A) = 0` for `i > n`, `A` compact in an `n`-manifold `M`) specialised to `M = I`.

`I` is an `N`-dimensional topological manifold (open in `ℝᴺ`), and the whole of `ℝᴺ` carries the
self-chart `chartAt ℝᴺ 0 = OpenPartialHomeomorph.refl ℝᴺ`, for which the chart piece
`W = e ⁻¹' I ∩ e.source` is exactly `I`.  Hence the statement is the case `M = ℝᴺ`, `Q = I`,
`C = K` of the general chart-piece vanishing `homology_vanishing_relative_compact`
(`Submission/Work/Cohomology/homology_vanishing_relative_compact.lean`), whose proof is Hatcher's:
Mayer–Vietoris for the complements of two compact sets, the convex compact base case
(`Duality.ball_local_homology`), finite unions of compact convex sets, and the enlargement of an
arbitrary compact `K` to a union of balls obtained from a relative cycle
(`relative_cycle_lift`, `exists_compact_support_image`, `homologyMap_enlarge_of_lift`).
-/

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

namespace Work.Cohomology

noncomputable section

theorem relChains_vanishing_compact_specific {N : ℕ} (hN : 1 ≤ N)
    (I : Set ↥(TopCat.of (EuclideanSpace ℝ (Fin N)))) (hI : IsOpen I)
    (K : Set ↥(TopCat.of (EuclideanSpace ℝ (Fin N)))) (hKI : K ⊆ I) (hKc : IsCompact K)
    (j : ℕ) (hj : N < j) :
    CategoryTheory.Limits.IsZero
      ((Work.Cohomology.relChains (TopCat.of ↥I) (Work.Cohomology.pdRelSub I K)).homology j) := by
  -- The self-chart of `ℝᴺ` is the identity, so the chart piece of `I` is `I` itself.
  have happ : ∀ x : EuclideanSpace ℝ (Fin N),
      (chartAt (EuclideanSpace ℝ (Fin N)) (0 : EuclideanSpace ℝ (Fin N))) x = x := fun x => rfl
  have hsrc : (chartAt (EuclideanSpace ℝ (Fin N)) (0 : EuclideanSpace ℝ (Fin N))).source
      = Set.univ := rfl
  have hW : ((chartAt (EuclideanSpace ℝ (Fin N)) (0 : EuclideanSpace ℝ (Fin N))) ⁻¹' I)
      ∩ (chartAt (EuclideanSpace ℝ (Fin N)) (0 : EuclideanSpace ℝ (Fin N))).source = I := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_preimage, hsrc, Set.mem_univ, and_true, happ]
  have hQt : I ⊆ (chartAt (EuclideanSpace ℝ (Fin N)) (0 : EuclideanSpace ℝ (Fin N))).target :=
    fun x _ => trivial
  -- Hatcher's Lemma 3.27 for the pair `(ℝᴺ, ℝᴺ∖K)` (as the chart piece over `I`).
  have hsub := homology_vanishing_relative_compact hN (M := TopCat.of (EuclideanSpace ℝ (Fin N)))
    (0 : EuclideanSpace ℝ (Fin N)) I hI hQt K (by intro x hx; rw [hW]; exact hKI hx) hKc j hj
  rw [hW] at hsub
  exact ModuleCat.isZero_iff_subsingleton.mpr hsub

end

end Work.Cohomology
