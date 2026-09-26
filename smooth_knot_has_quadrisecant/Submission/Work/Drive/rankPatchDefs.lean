import Mathlib
import Submission.Work.Drive.Prelude

/-!
# The badness maps of a collinear triple, as functions of the *data*

`Work.Drive.torusGeneralPositionTransverse_noInflection_dense` proves that the bad locus of a
collinear triple is a union of four patches
(`Work.Drive.not_trisecantGeneralPositionTransverse_iff_patches`):

    bad ⟺ (y_a = 0) ∨ (y_b = 0) ∨ (y_m = 0) ∨ (y_a ∥ y_b ∧ y_b ∥ y_m ∧ y_a ∥ y_m)

where `y_x = cross3 (v x) (r a - r b)` is the tangent–chord vector.  All four patches depend on
the curve *only* through the six data

    Data := (r a, r b, r m, v(a), v(b), v(m)) ∈ Space⁶,

so the patch conditions are explicit maps `Space⁶ → Space^k` (defined here), and their
differentials can be computed by hand.  The rank lemmas (four of them, one per patch) are the
crux of the covering argument: at a point of a patch, the patch conditions have a differential
of rank at least four in the data directions (so that perturbations of the coefficient vector
of the trigonometric-sum family, which realise arbitrary data variations by
`exists_trigDegLe_jets_surjective`, surject onto a four-dimensional space of conditions).
-/

namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant

noncomputable section

/-- The six data of a collinear triple: positions and velocities at `a`, `b`, `m`. -/
abbrev TripleData := Space × Space × Space × Space × Space × Space

/-- The positions `(P,Q,M) = (r a, r b, r m)` of the data. -/
def dataP (X : TripleData) : Space := X.1
def dataQ (X : TripleData) : Space := X.2.1
def dataM (X : TripleData) : Space := X.2.2.1
/-- The velocities `(A,B,C) = (v a, v b, v m)` of the data. -/
def dataA (X : TripleData) : Space := X.2.2.2.1
def dataB (X : TripleData) : Space := X.2.2.2.2.1
def dataC (X : TripleData) : Space := X.2.2.2.2.2

/-- The collinearity map `(P − Q) × (P − M)` of the data. -/
def dataColl (X : TripleData) : Space :=
  cross3 (dataP X - dataQ X) (dataP X - dataM X)

/-- The tangent–chord vector at the first point: `A × (P − Q)`. -/
def dataYa (X : TripleData) : Space := cross3 (dataA X) (dataP X - dataQ X)

/-- The tangent–chord vector at the second point: `B × (P − Q)`. -/
def dataYb (X : TripleData) : Space := cross3 (dataB X) (dataP X - dataQ X)

/-- The tangent–chord vector at the middle point: `C × (P − Q)`. -/
def dataYm (X : TripleData) : Space := cross3 (dataC X) (dataP X - dataQ X)

/-- Patch `P_a`: the chord is tangent at the first point. -/
def patchA (X : TripleData) : Space × Space := (dataColl X, dataYa X)

/-- Patch `P_b`: the chord is tangent at the second point. -/
def patchB (X : TripleData) : Space × Space := (dataColl X, dataYb X)

/-- Patch `P_m`: the chord is tangent at the middle point. -/
def patchM (X : TripleData) : Space × Space := (dataColl X, dataYm X)

/-- Patch `P_abm`: the three tangents are pairwise parallel modulo the chord (the
"all three tangents agree" degeneration). -/
def patchAll (X : TripleData) : Space × Space × Space :=
  (dataColl X, cross3 (dataYa X) (dataYb X), cross3 (dataYb X) (dataYm X))

end

end Work.Drive
