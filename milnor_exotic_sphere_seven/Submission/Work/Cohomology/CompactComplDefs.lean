import Mathlib
import Submission.Work.Cohomology.SingularTopFreeDefs
import Submission.Work.Cohomology.Pullback

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Auxiliary definitions for the "homology of the complement of a compact set" development

For a decreasing sequence `T : ℕ → Set ℝ^N` of closed sets, the complements `(T n)ᶜ` form an
increasing sequence of open sets.  This file packages

* `Work.Cohomology.stageIncl T hmono n` — the inclusion `(T n)ᶜ ↪ (T (n+1))ᶜ`;
* `Work.Cohomology.stageMap T hmono n` — the induced map `H_{N-1}((T n)ᶜ) → H_{N-1}((T (n+1))ᶜ)`.
-/

open CategoryTheory AlgebraicTopology

namespace Work.Cohomology

noncomputable section

variable {N : ℕ}

/-- The inclusion `(T n)ᶜ ⟶ (T (n+1))ᶜ` induced by `T (n+1) ⊆ T n`. -/
def stageIncl (T : ℕ → Set (EuclideanSpace ℝ (Fin N))) (hmono : ∀ n, T (n+1) ⊆ T n) (n : ℕ) :
    TopCat.of (Set.compl (T n)) ⟶ TopCat.of (Set.compl (T (n+1))) :=
  inclSet (X := TopCat.of (EuclideanSpace ℝ (Fin N))) (A := Set.compl (T n))
    (B := Set.compl (T (n+1))) (Set.compl_subset_compl.mpr (hmono n))

/-- The map `H_{N-1}((T n)ᶜ) → H_{N-1}((T (n+1))ᶜ)` induced by `stageIncl`. -/
def stageMap (T : ℕ → Set (EuclideanSpace ℝ (Fin N))) (hmono : ∀ n, T (n+1) ⊆ T n) (n : ℕ) :
    ↥((singularChains ℤ (TopCat.of (Set.compl (T n)))).homology (N-1)) →ₗ[ℤ]
      ↥((singularChains ℤ (TopCat.of (Set.compl (T (n+1))))).homology (N-1)) :=
  (HomologicalComplex.homologyMap (chainMap ℤ
    (TopCat.of (Set.compl (T n))) (TopCat.of (Set.compl (T (n+1))))
    (stageIncl T hmono n)) (N-1)).hom

end

end Work.Cohomology
