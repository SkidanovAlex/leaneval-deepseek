import Mathlib
import Submission.Work.Kunneth.Chapter
import Submission.Work.Cohomology.HomologyPairSequence
import Submission.Work.Serre.relEZ_main

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The relative Eilenberg–Zilber homology isomorphism

For a space `W` and a pair `(P,Q)`, the Koszul tensor product of the singular chains of `W` with
the relative chains of `(P,Q)` has the same homology as the relative chain complex of the product
pair `(W × P, W × Q)`.  The proof (the classical five-lemma argument, together with the
Eilenberg–Zilber theorem and the flatness of the singular chains) is in
`Submission/Work/Serre/relEZ_main.lean` as `Work.Serre.relEZ_homology_iso_core`.
-/

namespace Work.Serre

theorem relEZ_homology_iso (W P : Type) [TopologicalSpace W] [TopologicalSpace P] (Q : Set P) :
    ∀ n : ℕ, Nonempty
      (((Work.Kunneth.tpC (Work.Cohomology.singularChains ℤ (TopCat.of W))
          (Work.Cohomology.relChains (TopCat.of P) Q)).homology n)
        ≅ ((Work.Cohomology.relChains (TopCat.of (W × P)) {x : W × P | x.2 ∈ Q}).homology n)) := by
  exact relEZ_homology_iso_core W P Q

end Work.Serre
