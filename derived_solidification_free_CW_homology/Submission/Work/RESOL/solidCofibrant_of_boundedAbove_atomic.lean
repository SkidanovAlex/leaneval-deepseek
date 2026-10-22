/-
AREA RESOL — B5 of `REFS/02`: a bounded-above complex of atoms is solid-cofibrant.

The proof is a retraction argument.  Let `U m := trunc (L m) K = σ^{≥ -m}K` be the tower of
brutal truncations of `K`, `A K := ∐_m U m`, `s K` the shift of the telescope, and
`T K := cone (𝟙 (A K) - s K)` the telescope of the tower (`RESOL/B5TowerDefs.lean`).

* `RESOL/B5Tower.lean` builds the fold map `σ K : A K ⟶ K`, the map `φ K : T K ⟶ K` induced by
  `σ K` and a null homotopy of `(1 - s) ≫ σ K`, and the coherent section `ψ K : K ⟶ T K`
  (degreewise `(d_K ≫ ∑ u_j, u_{M n})`), and proves the retraction identity `ψ K ≫ φ K = 𝟙 K`.
* `RESOL/B5TowerSolid.lean` proves that every truncation `U m` is solid-cofibrant (downward
  induction from the truncations above the bound of `K`, where they vanish, using
  `solidCofibrant_trunc`), that the telescope `T K` is solid-cofibrant (the closure properties
  `hC.sigma` and `hC.cone`, via `RESOL/solidCofibrant_telescope.lean`), and concludes
  `SolidCofibrant K` from the retraction (`RESOL/Retract.lean`).

The only analytic input is `AtomProp` (the free objects `ℤ[S]` are cofibrant), used through
`solidCofibrant_single_atomic`.
-/
import Mathlib
import Submission.Work.RESOL.Retract
import Submission.Work.RESOL.B5TowerSolid

open CategoryTheory

namespace Work.RESOL

theorem solidCofibrant_of_boundedAbove_atomic (hA : Submission.Blueprint.AtomProp)
    (hC : Work.RESOL.CofibrantClosure) (K : Work.RESOL.Cpx)
    (hbd : Work.RESOL.IsBoundedAbove K) (hat : Work.RESOL.HasAtomicTerms K) :
    Submission.Blueprint.SolidCofibrant K :=
  solidCofibrant_of_boundedAbove_atomic_aux hA hC K hbd hat

end Work.RESOL
