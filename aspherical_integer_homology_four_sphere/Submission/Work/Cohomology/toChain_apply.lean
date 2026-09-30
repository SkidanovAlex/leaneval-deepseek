import Mathlib
import Submission.Work.Cohomology.Subdivision
import Submission.Work.Cohomology.SdIter

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


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
