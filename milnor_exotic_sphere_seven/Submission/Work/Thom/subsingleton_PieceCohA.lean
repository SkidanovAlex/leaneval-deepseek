import Mathlib
import Submission.Work.Thom.Glue
import Submission.Work.Thom.subsingleton_PieceCoh_of_euclidean
import Submission.Work.Thom.subsingleton_relComplex_euclidean_punctured
import Submission.Work.Thom.Relocate.SubsingletonRelComplexCube
import Submission.Work.Thom.subsingleton_PieceCoh_of_lt_rank

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-!
# The vanishing of the relative cohomology of a bundle piece in low degrees

**Why this module exists.**  The general Thom isomorphism theorem of this chapter
(`Work.Thom.thomClass_of_cover_gen`, `Submission/Work/Thom/thomClass_of_cover_gen.lean`) takes as
one of its inputs the vanishing `Subsingleton (Work.Thom.PieceCoh Z (U ∩ V) (n - 1))` of the
relative cohomology of the overlap *below the rank*.  The existing producer is
`Work.Thom.subsingleton_PieceCoh_of_lt_rank` (`Submission/Work/Thom/subsingleton_PieceCoh_of_lt_rank.lean`),
but it imports `Work.Thom.subsingleton_relComplex_cube`, which drags in the `prod_sphere_aux` island
of the workspace (`Submission/Work/Cohomology/isIso_smallIsoHom.lean`) — an island that cannot be
combined with `Submission/Work/TangentClasses/`, `Submission/Work/SignatureBordism/` or
`Submission/Work/Thom/Interface.lean`.  The present module re-proves the *same* statement through
the clean copies of the three ingredients:

* `Work.Thom.subsingleton_PieceCoh_of_euclidean` (already in the island);
* `Work.Thom.subsingleton_relComplex_euclidean_punctured` (already in the island);
* `Work.Thom.Relocate.SubsingletonRelComplexCube.subsingleton_relComplex_cube` — the vanishing for
  the cube pair `(W × [-1,1]ⁿ, W × ∂[-1,1]ⁿ)`, a verbatim copy of
  `Work.Thom.subsingleton_relComplex_cube` in which the only unclean import has been replaced by
  `Work.Thom.Relocate.HonestFMV`.

* `Work.Thom.subsingleton_PieceCoh_of_lt_rankA` — `H^m(Z|_W, Z|_W∖0) = 0` for `m < n` whenever
  `W` is contained in a chart `Z.baseSet i` of a real bundle of rank `n`.
-/

open Work.TangentClasses

namespace Work.Thom

noncomputable section

variable {B : Type} [TopologicalSpace B] {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {ι : Type}

/-- **Vanishing of the relative cohomology of a bundle piece below the rank.**  A re-proof (in the
`localCohomology`/`proj_pair_injective`/`ovlRestrictionSurjective` island of the workspace) of
`Work.Thom.subsingleton_PieceCoh_of_lt_rank`. -/
theorem subsingleton_PieceCoh_of_lt_rankA {B : Type} [TopologicalSpace B] (n : ℕ) (ι : Type)
    [Inhabited ι] (Z : Work.TangentClasses.RealBundle B (EuclideanSpace ℝ (Fin n)) ι) (i : ι)
    {W : Set B} (hW : W ⊆ Z.baseSet i) {m : ℕ} (hm : m < n) :
    Subsingleton (Work.Thom.PieceCoh Z W m) :=
  subsingleton_PieceCoh_of_euclidean
    (fun n W _ m hm => subsingleton_relComplex_euclidean_punctured
      (fun n W _ m hm => subsingleton_relComplex_cube n W m hm) n W m hm)
    n ι Z i hW hm

end

end Work.Thom
