import Mathlib
import Submission.Work.ConCohomology.Extension

namespace Work.ConCohomology

/-- Conjugation in the extension is a (left) action of `G` on `N`: conjugation by a product is the
composite of the two conjugations. -/
lemma GroupExt.conj_mul {G Q N : Type*} [Group G] [Group Q] [Group N] (E : GroupExt G Q N)
    (g h : G) (n : N) : E.conj (g * h) n = E.conj g (E.conj h n) := by
  apply E.injective_i
  rw [E.i_conj, E.i_conj, E.i_conj]
  group

lemma conjCochain_mul {G Q N : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [Group Q] [TopologicalSpace Q] [Group N] [TopologicalSpace N]
    [IsTopologicalGroup N] {M : Type*} [AddCommGroup M] [DistribMulAction G M]
    (E : GroupExt G Q N) (hcont : ∀ g : G, Continuous (E.conj g)) (g h : G)
    (φ : Cochain1 N M) :
    conjCochain E hcont (g * h) φ = conjCochain E hcont g (conjCochain E hcont h φ) := by
  ext n
  simp only [conjCochain_apply]
  rw [← mul_smul, mul_inv_rev, GroupExt.conj_mul]

end Work.ConCohomology
