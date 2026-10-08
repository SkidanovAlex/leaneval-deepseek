/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# AREA AUTL2 : `N(PSL(2,q)) = PΓL(2,q)`

Assembly of step A3 of the AUTL2 design: the normalizer in `Sym(ℙ¹(F_q))` of the image of
`PSL(2,q)` is `PΓL(2,q)`.

* the inclusion `≤` is `Work.AUTL2.Normalizer.le_pgammaL` (the classical argument);
* the inclusion `≥` is `Work.AUTL2.Galois.decomposition` (a field automorphism conjugates a
  Möbius map to a Möbius map).
-/
import Mathlib
import Submission.Work.AUTL2.Defs
import Submission.Work.AUTL2.Galois.decomposition
import Submission.Work.AUTL2.Normalizer.le_pgammaL

open scoped MatrixGroups LinearAlgebra.Projectivization
open OnePoint

namespace Work.AUTL2

/-- **Step A3**: the normalizer of the image of `PSL(2,q)` (`q = p^k` odd, `q ≥ 5`) in
`Sym(ℙ¹(F_q))` is `PΓL(2,q)`. -/
theorem normalizer_pslImage_eq (p k : ℕ) [Fact p.Prime] [Fintype (GaloisField p k)]
    (hp : Odd p) (hq : 5 ≤ p ^ k) [DecidableEq (GaloisField p k)] :
    Subgroup.normalizer (pslImage (GaloisField p k) :
        Set (Equiv.Perm (P1 (GaloisField p k)))) = pgammaL (GaloisField p k) := by
  refine le_antisymm ?_ ?_
  · intro π hπ
    exact Normalizer.le_pgammaL p k hp hq π hπ
  · exact (Galois.decomposition (GaloisField p k)).2.2.2.2

end Work.AUTL2
