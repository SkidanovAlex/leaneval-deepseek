import Mathlib
import Submission.Work.SymQuot.Product
import Submission.Work.GCBasics.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


namespace Work.SymQuot.Product

/-- `permIso X σ` is the identity automorphism when `σ` is the identity permutation;
the statement `permIso X 1 = Iso.refl (prod X n)` is the unit law of the symmetric-group
action on the `n`-fold product of `X`. -/
theorem permIso_one {K : Type*} [Field K] (X : Work.GCBasics.Sch K) {n : ℕ} :
    Work.SymQuot.permIso X 1 = CategoryTheory.Iso.refl (Work.SymQuot.prod X n) := by
  rw [Work.SymQuot.permIso]
  unfold Work.SymQuot.prod
  apply CategoryTheory.Iso.ext
  simp only [CategoryTheory.Limits.Pi.whiskerEquiv_hom]
  ext b
  simp [Equiv.Perm.one_def]

end Work.SymQuot.Product
