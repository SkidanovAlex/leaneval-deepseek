import Mathlib
import Submission.Work.Thom.Glue
import Submission.Work.Thom.subsingleton_PieceCoh_of_euclidean
import Submission.Work.Thom.subsingleton_relComplex_euclidean_punctured
import Submission.Work.Thom.Relocate.SubsingletonRelComplexCube

set_option synthInstance.maxHeartbeats 400000

/-!
# The relative cohomology of a bundle piece vanishes below the rank

For a real vector bundle `Z` of rank `n` over `B` and a set `W ⊆ B` contained in a single chart
`i` of the bundle, the relative cohomology of the piece of the Thom pair over `W`,
`Work.Thom.PieceCoh Z W m = H^m(X|_W, X|_W ∖ 0)`, vanishes for `m < n`.

The proof assembles three reductions:

* `Work.Thom.subsingleton_PieceCoh_of_euclidean` — on a chart the bundle is trivial, so the piece
  is a product with `ℝⁿ` and the claim is the Euclidean model
  `H^m(W × ℝⁿ, W × (ℝⁿ∖0)) = 0` for `m < n`;
* `Work.Thom.subsingleton_relComplex_euclidean_punctured` — the Euclidean model follows from the
  cube model `H^m(W × [-1,1]ⁿ, W × ∂[-1,1]ⁿ) = 0`, which is homotopy equivalent to it;
* `Work.Thom.subsingleton_relComplex_cube` — the cube model, by induction on `n` with the
  Mayer–Vietoris sequence of the cover of the cube by its two open halves.
-/

namespace Work.Thom

theorem subsingleton_PieceCoh_of_lt_rank {B : Type} [TopologicalSpace B] (n : ℕ) (ι : Type)
    [Inhabited ι] (Z : Work.TangentClasses.RealBundle B (EuclideanSpace ℝ (Fin n)) ι) (i : ι)
    {W : Set B} (hW : W ⊆ Z.baseSet i) {m : ℕ} (hm : m < n) :
    Subsingleton (Work.Thom.PieceCoh Z W m) :=
  subsingleton_PieceCoh_of_euclidean
    (fun n W _ m hm => subsingleton_relComplex_euclidean_punctured
      (fun n W _ m hm => subsingleton_relComplex_cube n W m hm) n W m hm)
    n ι Z i hW hm

end Work.Thom
