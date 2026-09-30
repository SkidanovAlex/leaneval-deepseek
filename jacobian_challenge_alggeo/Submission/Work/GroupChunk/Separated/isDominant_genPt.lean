import Mathlib
import Submission.Work.GCBasics.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


namespace Work.GroupChunk.Separated

universe u
open CategoryTheory in
theorem isDominant_genPt {K : Type u} [Field K] (R : Type u) [CommRing R] [IsDomain R]
    [Algebra K R] :
    AlgebraicGeometry.IsDominant (Work.GCBasics.genPt (K := K) R).left := by
  rw [show (Work.GCBasics.genPt (K := K) R).left =
      AlgebraicGeometry.Spec.map
        (CommRingCat.ofHom (algebraMap R (FractionRing R))) from rfl]
  rw [AlgebraicGeometry.isDominant_iff]
  show DenseRange (PrimeSpectrum.comap (algebraMap R (FractionRing R)))
  rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical]
  simp

end Work.GroupChunk.Separated
