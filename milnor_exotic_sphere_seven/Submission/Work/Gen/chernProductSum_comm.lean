import Mathlib
import Submission.Work.Whitney.ChernProduct
import Submission.Work.Whitney.chernProductSum_eq_fin
import Submission.Work.Whitney.ChernRelDefs
import Submission.Work.LerayHirsch.Series
import Submission.Work.Whitney.convSeries_comm

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.Gen

/-- **The right-hand side of the Whitney formula is symmetric in its two arguments.**  In even
degrees the graded cup product is commutative with sign `(-1)^{(2i)(2j)} = 1`, so swapping the two
factors of `chernProductSum` does not change the class:

`chernProductSum Z₁ Z₂ k = chernProductSum Z₂ Z₁ k`.

Proof route: `Work.Whitney.chernProductSum_eq_fin` writes both sides as `Fin (k+1)`-indexed sums, in
which the summand at index `a` is (up to the degree casts) `cupH' ℤ (ssB B) (2*a) (2*(k-a)) (c_a Z₁)
(c_{k-a} Z₂)` and, after reindexing `a ↦ k - a`, the summand `cupH' ℤ (ssB B) (2*(k-a)) (2*a) (c_{k-a}
Z₂) (c_a Z₁)`; these agree by `Work.Whitney.ChernRel.cupChern_comm` (i.e. `gradedComm` with the sign
`(-1)^{4a(k-a)} = 1`), plus `Finset.sum_bij`/`Fin.sum_univ` reindexing and the degree-cast
bookkeeping (`Work.Whitney.cohTransport_trans`).  The two factors may live over different covers
`ι`, `ι'` (nothing in `cupChern_comm` involves covers).  A possibly shorter route: rewrite both sides
with `Work.LerayHirsch.chernProductSum_eq_convSeries` and use the commutativity of `convSeries`
(`Submission/Work/Whitney/convSeries_comm.lean`). -/
theorem chernProductSum_comm {B : Type} [TopologicalSpace B] {ι ι' : Type} [Fintype ι] [Fintype ι']
    {m₁ m₂ : ℕ} (Z₁ : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m₁)) ι)
    (Z₂ : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m₂)) ι') (k : ℕ) :
    Work.Whitney.chernProductSum Z₁ Z₂ k = Work.Whitney.chernProductSum Z₂ Z₁ k := by
  rw [Work.LerayHirsch.chernProductSum_eq_convSeries Z₁ Z₂ k,
    Work.LerayHirsch.chernProductSum_eq_convSeries Z₂ Z₁ k,
    Work.Whitney.convSeries_comm]

end Work.Gen
