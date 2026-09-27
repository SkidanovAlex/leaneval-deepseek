import Mathlib
import Submission.Work.Mostow.geomFiniteDefs
import Submission.Work.Mostow.geomFiniteGapA
import Submission.Work.Mostow.dirichletGapASelf
import Submission.Work.Mostow.margulisCusp
import Submission.Work.Mostow.margulisLox
import Submission.Work.Mostow.pairStab
import Submission.Work.Mostow.classifyProp

/-! # Area C1 — `geomFinite : GeomFiniteProp n`   (CRUX B)

A finite-volume lattice `Γ ≤ PO(n,1)` is geometrically finite.  The proof is assembled in
`Work.Mostow.geomFiniteGapA` (`geomFinite_of_gapA`) from

* `geomFiniteParabolicClass`  (G2): a parabolic element fixes a unique boundary point;
* `geomFiniteStabHorosphere`  (G3): the stabiliser of a parabolic fixed point preserves the
  horospheres (the Busemann cocycle vanishes on it);
* `cuspHoroballsPairwise` + `horoballComplementBounded_aux` : the cusp horoballs are equivariant
  and pairwise disjoint, and their complement is `Γ`-cocompact, the latter using the lead's HL
  `HL_of_escapeShort` (whose GAP-A input is `Work.Mostow.gapA_all`);
* `geomFiniteCuspCocompact`   (G7): cusp stabilisers act cocompactly on the horospheres.

The remaining inputs `margulisCusp`, `margulisLox`, `pairStab`, `classifyProp` are the (proved)
classification chapters, and `gapA_allSelf` is GAP-A for every `n ≥ 3`.
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory

theorem geomFinite (n : ℕ) (hn : 3 ≤ n) (hA : POActionProp n) (hI : HypIsometryProp n)
    (hBb : ∀ m, BieberbachProp m) : GeomFiniteProp n :=
  geomFinite_of_gapA n hn hA hI hBb
    (margulisCusp n (by omega) hA hI)
    (margulisLox n (by omega) hA hI (pairStab_pairStab n (by omega) hA hI))
    (pairStab_pairStab n (by omega) hA hI)
    (classifyProp n (by omega) hA hI)
    (fun Γ hΓ => gapA_allSelf n hn Γ hΓ)

end Work.Mostow

#print axioms Work.Mostow.geomFinite
