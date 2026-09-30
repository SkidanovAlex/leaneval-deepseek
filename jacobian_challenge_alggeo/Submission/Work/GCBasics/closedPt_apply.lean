import Mathlib
import Submission.Work.GCBasics.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


namespace Work.GCBasics

open CategoryTheory in
theorem closedPt_apply {K : Type _} [Field K] (R : Type _) [CommRing R] [IsLocalRing R]
    [Algebra K R] :
    (Work.GCBasics.closedPt (K := K) R).left (IsLocalRing.closedPoint (IsLocalRing.ResidueField R)) =
      IsLocalRing.closedPoint R := by
  -- Unfold the definition of `closedPt`: it is `Spec` of the residue map `R →+* κ(R)`.
  simp only [Work.GCBasics.closedPt, Work.GCBasics.specOfMap, Over.homMk_left]
  -- `Spec_closedPoint`: a local ring homomorphism induces a map of spectra sending the
  -- closed point to the closed point.
  refine @AlgebraicGeometry.Spec_closedPoint (CommRingCat.of R)
    (CommRingCat.of (IsLocalRing.ResidueField R)) _ _ (CommRingCat.ofHom (IsLocalRing.residue R)) ?_
  exact inferInstanceAs (IsLocalHom (IsLocalRing.residue R))

end Work.GCBasics
