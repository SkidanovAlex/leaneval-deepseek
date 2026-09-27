import Mathlib
import Submission.Work.KT.Defs
import Submission.Work.KT.Fund.Geom

/-!
# `Work.KT.Fund.Clutch` — the orthogonal projections used in the clutching construction

Given an invertible matrix `u` over `C(X × S¹, ℂ)`, the clutched bundle over `X × S²` is obtained
by gluing two trivial bundles over the two hemispheres along `u`.  Concretely, with `F` a lift of
`u` to the upper disc and `G` a lift of `u⁻¹` to the lower disc, the bundle is the image of

* `graphProj F` — the orthogonal projection onto the *graph* of `F`,
  `im [[1],[F]] ⊆ R^{2n}`, over the upper hemisphere, and
* `recipProj G` — the orthogonal projection onto the *reciprocal graph* of `G`,
  `im [[G],[1]] ⊆ R^{2n}`, over the lower hemisphere.

On the equator, `G| = (F|)⁻¹`, so `im [[1],[u]] = im [[u⁻¹],[1]]` and the two orthogonal
projections agree as matrices: this is `Work.KT.Fund.clutch_agree`.  Orthogonality is essential:
it makes the projection a function of the *image* alone, so the two descriptions agree exactly on
the overlap; the non-orthogonal graph projections would glue to a global graph, i.e. to a trivial
bundle.
-/

namespace Work.KT
namespace Fund

open Matrix

noncomputable section

/-- The block matrix `[[1],[F]]`, as a `2n × n` matrix (rows indexed by `Fin n ⊕ Fin n`). -/
def graphB {n : ℕ} (R : Type) [Ring R] (F : Matrix (Fin n) (Fin n) R) :
    Matrix (Fin n ⊕ Fin n) (Fin n) R :=
  fun i j => match i with
    | Sum.inl a => if a = j then 1 else 0
    | Sum.inr a => F a j

/-- The block matrix `[[G],[1]]`, as a `2n × n` matrix (rows indexed by `Fin n ⊕ Fin n`). -/
def recipB {n : ℕ} (R : Type) [Ring R] (G : Matrix (Fin n) (Fin n) R) :
    Matrix (Fin n ⊕ Fin n) (Fin n) R :=
  fun i j => match i with
    | Sum.inl a => G a j
    | Sum.inr a => if a = j then 1 else 0

/-- The orthogonal projection onto the image of a `2n × n` matrix `B` (with respect to the
standard Hermitian form): `B (Bᴴ B)⁻¹ Bᴴ`. -/
def orthProj {n : ℕ} (R : Type) [CommRing R] [Star R]
    (B : Matrix (Fin n ⊕ Fin n) (Fin n) R) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R :=
  B * Ring.inverse (Matrix.conjTranspose B * B) * Matrix.conjTranspose B

/-- The orthogonal projection onto the graph of `F`. -/
def graphProj {n : ℕ} (R : Type) [CommRing R] [Star R]
    (F : Matrix (Fin n) (Fin n) R) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R :=
  orthProj R (graphB R F)

/-- The orthogonal projection onto the reciprocal graph of `G`. -/
def recipProj {n : ℕ} (R : Type) [CommRing R] [Star R]
    (G : Matrix (Fin n) (Fin n) R) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R :=
  orthProj R (recipB R G)

end

end Fund
end Work.KT
