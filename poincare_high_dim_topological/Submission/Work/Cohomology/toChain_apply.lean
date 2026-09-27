import Mathlib
import Submission.Work.Cohomology.Subdivision
import Submission.Work.Cohomology.SdIter

namespace Work.Cohomology

/-- **`toChain` on an arbitrary affine chain.**  Since `toChain` is, by definition, the
`Finsupp.linearCombination ℤ` of the generator map `w ↦ gen (Delta N) k (linSimplex w)`, it
expands as the finite sum over the support of `c`, each affine simplex weighted by its
coefficient. -/
theorem toChain_apply (N k : ℕ) (c : LinChain N k) :
    toChain N k c
      = ∑ v ∈ c.support, c v • gen (Delta N) k (linSimplex v) := by
  have hmap : toChain N k
      = Finsupp.linearCombination ℤ (fun v => gen (Delta N) k (linSimplex v)) := rfl
  have h2 : (Finsupp.linearCombination ℤ (fun v => gen (Delta N) k (linSimplex v))) c
      = ∑ v ∈ c.support, c v • gen (Delta N) k (linSimplex v) := by
    rw [Finsupp.linearCombination_apply, Finsupp.sum]
    exact Finset.sum_congr rfl fun v _ =>
      Int.cast_smul_eq_zsmul ℤ (c v) (gen (Delta N) k (linSimplex v))
  exact (DFunLike.congr_fun hmap c).trans h2

end Work.Cohomology
