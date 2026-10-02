import Mathlib
import Submission.Work.Cohomology.Duality.ball_local_homology
import Submission.Work.Cohomology.relCohomologyDual
import Submission.Work.Cohomology.uctDual

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Local cohomology of `ℝⁿ` at a compact convex set

The cohomological counterpart of `Work.Cohomology.Duality.ball_local_homology`: for a nonempty
compact convex `K ⊆ ℝⁿ` (`n ≥ 1`),

`Hᵏ(ℝⁿ, ℝⁿ ∖ K; ℤ) = 0` for `k ≠ n`,  `Hⁿ(ℝⁿ, ℝⁿ ∖ K; ℤ) ≅ ℤ`.

Since the relative homology of the pair is concentrated in degree `n`
(`Work.Cohomology.Duality.ball_local_homology`), it is free, so the universal coefficient theorem in
the evaluation form (`Work.Cohomology.relCohomologyDual`) identifies `Hᵏ(X,A)` with
`Hom(H_k(X,A), ℤ)`, which is `0` for `k ≠ n` and `ℤ` for `k = n`.
-/

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

namespace Work.Cohomology.Duality

noncomputable section

variable {n : ℕ}

/-- The relative homology of `(ℝⁿ, ℝⁿ ∖ K)` is degreewise free, for `K` nonempty compact convex. -/
theorem free_relChains_compl (n : ℕ) (hn : 1 ≤ n) (K : Set (EuclideanSpace ℝ (Fin n)))
    (hKc : IsCompact K) (hconv : Convex ℝ K) (hne : K.Nonempty) :
    ∀ k, Module.Free ℤ ↥((Work.Cohomology.relChains
      (TopCat.of (EuclideanSpace ℝ (Fin n))) {y : EuclideanSpace ℝ (Fin n) | y ∉ K}).homology k) := by
  obtain ⟨hzero, htop⟩ := ball_local_homology n hn K hKc hconv hne
  intro k
  by_cases hk : k = n
  · rw [hk]
    obtain ⟨e⟩ := htop
    haveI : Module.Free ℤ (↥(ModuleCat.of ℤ ℤ)) := inferInstance
    exact Module.Free.of_equiv e.toLinearEquiv.symm
  · haveI : Subsingleton ↥((Work.Cohomology.relChains
        (TopCat.of (EuclideanSpace ℝ (Fin n))) {y : EuclideanSpace ℝ (Fin n) | y ∉ K}).homology k) :=
      ModuleCat.subsingleton_of_isZero (hzero k hk)
    exact Module.Free.of_subsingleton ℤ _

end

end Work.Cohomology.Duality
