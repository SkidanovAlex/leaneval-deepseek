import Mathlib
import Submission.Work.Cohomology.diskPairHomologyZero

set_option linter.style.haveILetI false

namespace Work.Compact.Noncompact.Convex

open CategoryTheory CategoryTheory.Limits Metric

/-- **The relative homology of the pair (ball, ball ∖ C) vanishes above the dimension, given the
vanishing of the homology of the complement.**

For `n ≥ 1`, `R > 0`, `c : ℝⁿ`, `C ⊆ ℝⁿ` and `k > n`: if the space
`{y : ↥(Metric.ball c R) // (y : ℝⁿ) ∉ C}` has vanishing singular homology in all degrees `j ≥ n`,
then the `k`-th relative singular homology of the pair `(ball c R, ball c R ∖ C)` vanishes.

Route: the long exact sequence of the pair (`Work.Cohomology.hPairShort`, `hPairδ`,
`hPair_exact₁`, `hPair_exact₃` and the isomorphism criterion `Work.Cohomology.hPairδ_isIso'` from
`Submission/Work/Cohomology/diskPairHomologyZero.lean`) for `X := TopCat.of ↥(Metric.ball c R)`
and `A := {y : ↥(Metric.ball c R) | (y : ℝⁿ) ∉ C}`.  Since `k > n ≥ 1`, we have `k ≥ 2` and
`k - 1 ≥ 1`, so `H_k(X) = 0` and `H_{k-1}(X) = 0` by `Work.Cohomology.homologyContractible` (the
ball is convex and nonempty: `convex_ball`, `Metric.mem_ball_self`, `Convex.contractibleSpace`).
Hence the connecting map `hPairδ X A (k - 1) : H_{(k-1)+1}(X, A) ⟶ H_{k-1}(X ∖ C)` is an
isomorphism; transport it along `Nat.sub_add_cancel` to degree `k` and use the hypothesis with
`j := k - 1 ≥ n` (`IsZero.of_iso`, `CategoryTheory.asIso`). -/
theorem isZero_relChains_ball_compl_convex_of {n k : ℕ} (hn : 1 ≤ n)
    (c : EuclideanSpace ℝ (Fin n)) {R : ℝ} (hR : 0 < R) {C : Set (EuclideanSpace ℝ (Fin n))}
    (hY : ∀ j : ℕ, n ≤ j → CategoryTheory.Limits.IsZero
      ((Work.Cohomology.singularChains ℤ
        (TopCat.of {y : ↥(Metric.ball c R) // (y : EuclideanSpace ℝ (Fin n)) ∉ C})).homology j))
    (hk : n < k) :
    CategoryTheory.Limits.IsZero
      ((Work.Cohomology.relChains (TopCat.of ↥(Metric.ball c R))
        {y : ↥(Metric.ball c R) | (y : EuclideanSpace ℝ (Fin n)) ∉ C}).homology k) := by
  haveI hcontr : ContractibleSpace ↥(Metric.ball c R) :=
    Convex.contractibleSpace (convex_ball c R) ⟨c, Metric.mem_ball_self hR⟩
  have h1 : CategoryTheory.Limits.IsZero
      ((Work.Cohomology.singularChains ℤ (TopCat.of ↥(Metric.ball c R))).homology ((k - 1) + 1)) :=
    Work.Cohomology.homologyContractible ((k - 1) + 1) (by omega)
  have h2 : CategoryTheory.Limits.IsZero
      ((Work.Cohomology.singularChains ℤ (TopCat.of ↥(Metric.ball c R))).homology (k - 1)) :=
    Work.Cohomology.homologyContractible (k - 1) (by omega)
  have hiso : IsIso (Work.Cohomology.hPairδ (TopCat.of ↥(Metric.ball c R))
      {y : ↥(Metric.ball c R) | (y : EuclideanSpace ℝ (Fin n)) ∉ C} (k - 1)) :=
    Work.Cohomology.hPairδ_isIso' _ _ (k - 1) h1 h2
  have hY' : CategoryTheory.Limits.IsZero
      ((Work.Cohomology.singularChains ℤ
        (TopCat.of {y : ↥(Metric.ball c R) | (y : EuclideanSpace ℝ (Fin n)) ∉ C})).homology
        (k - 1)) :=
    hY (k - 1) (by omega)
  rw [show k = (k - 1) + 1 from by omega]
  exact CategoryTheory.Limits.IsZero.of_iso hY'
    (asIso (Work.Cohomology.hPairδ (TopCat.of ↥(Metric.ball c R))
      {y : ↥(Metric.ball c R) | (y : EuclideanSpace ℝ (Fin n)) ∉ C} (k - 1)))

end Work.Compact.Noncompact.Convex
