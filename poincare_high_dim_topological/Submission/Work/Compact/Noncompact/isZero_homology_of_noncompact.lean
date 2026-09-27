import Mathlib
import Submission.Work.Cohomology.localHomology
import Submission.Work.Cohomology.sphereHomologyTop
import Submission.Work.Cohomology.excision
import Submission.Work.Cohomology.MVSequence
import Submission.Work.Cohomology.HomologyPairSequence
import Submission.Work.Compact.Noncompact.Basic
import Submission.Work.Compact.Noncompact.exists_localMap_eq_zero
import Submission.Work.Compact.Noncompact.forall_localMap_eq_zero_of_exists
import Submission.Work.Compact.Noncompact.eq_zero_of_forall_localMap_eq_zero

/-!
# The top homology of a connected noncompact manifold vanishes

(Hatcher, *Algebraic Topology*, Proposition 3.29: if `M` is a connected noncompact `n`-manifold
then `H_i(M;ℤ) = 0` for `i ≥ n`.)

The proof assembles three ingredients about the *localization map*
`localMap n x : H_n(M;ℤ) ⟶ H_n(M, M∖{x};ℤ)`:

* `Work.Compact.Noncompact.exists_localMap_eq_zero` — every class is represented by a cycle with
  compact image, and a noncompact `M` has a point outside that image, where the class is locally
  trivial;
* `Work.Compact.Noncompact.forall_localMap_eq_zero_of_exists` — the vanishing locus of the
  localization map is clopen, hence all of `M` (`M` is connected);
* `Work.Compact.Noncompact.eq_zero_of_forall_localMap_eq_zero` — a class which is locally trivial
  at every point of a connected `n`-manifold (`n ≥ 1`) is zero (Hatcher's Lemma 3.27(a) and the
  `i = n` case of Proposition 3.29).
-/

set_option maxHeartbeats 800000

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

namespace Work.Compact.Noncompact

theorem isZero_homology_of_noncompact (n : ℕ) (hn : 1 ≤ n) {M : Type} [TopologicalSpace M]
    [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [ConnectedSpace M]
    [NoncompactSpace M] :
    CategoryTheory.Limits.IsZero
      ((Work.Cohomology.singularChains ℤ (TopCat.of M)).homology n) := by
  rw [ModuleCat.isZero_iff_subsingleton]
  have hzero : ∀ α : (Work.Cohomology.singularChains ℤ (TopCat.of M)).homology n, α = 0 :=
    fun α =>
      eq_zero_of_forall_localMap_eq_zero hn α
        (forall_localMap_eq_zero_of_exists hn α (exists_localMap_eq_zero α))
  exact ⟨fun a b => by rw [hzero a, hzero b]⟩

end Work.Compact.Noncompact
