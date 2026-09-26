import Mathlib
import Submission.Work.Drive.genericFullDefs
import Submission.Work.Drive.exists_close_transverse_noInflection
import Submission.Work.Drive.noFiveCollinear_bad_interior_empty
import Submission.Work.Drive.interior_projection_zeroSet_of_rank_except
import Submission.Work.Drive.qwDefs
import Submission.Work.Drive.exists_close_generic_fullK
import Submission.Work.Drive.exists_close_generic_fullK_c2

namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant in
/-- **The extended genericity density (with quadrisecant isolation).**

Every smooth knot has arbitrarily `C¹`-close smooth approximants that are simultaneously in
transverse general position, without inflection points, without five collinear points, in
tangent-chord general position, and *quadrisecant-isolated* (`Work.Drive.QuadrisecantIsolated`,
Kuperberg's Lemma 2.4 V: at every collinear quadruple of one period window with the two middles
strictly inside, the four partials of the four-point collinearity map are linearly independent).

This is `Work.Drive.GenericFullDense` with one more parametric-transversality clause.  It is the
density statement consumed by the corrected `O'` construction: `NoFiveCollinear` and
`QuadrisecantIsolated` are the two extra hypotheses that the restated bricks (d′), (e) and the
corrected crux need, and `GenericFullDense` alone does not supply `QuadrisecantIsolated`
(`TorusGeneralPositionTransverse` does not imply it: a knot on a doubly ruled quadric violates it).

Route: the proof is the existing assembly of `Work.Drive.genericFullDense`
(`Submission/Work/Drive/genericFullDense.lean`) with one extra bad set added to the Baire
intersection, exactly as `Work.Drive.noFiveCollinear_bad_interior_empty`
(`Submission/Work/Drive/noFiveCollinear_bad_interior_empty.lean`) and
`Work.Drive.tangentChord_bad_interior_empty`
(`Submission/Work/Drive/tangentChord_bad_interior_empty.lean`) do for their clauses.  For a compact box
in the four parameters `(a, z, w, b)` of one period window, the new bad set is

    {c | ∃ a z w b in the box, the middle conditions hold and
           ¬ LinearIndependent ℝ (quadPartial (perturbedKnot r c) a z w b)},

i.e. the parameters for which the six-by-four matrix of partials has rank at most three; it is the
common zero set of the fifteen four-by-four minors of that matrix, projected to the coefficient space
(which is the twenty-seven-dimensional trigonometric coefficient space of the existing genericity
library, not the nine-dimensional frequency space).

IMPORTANT, the off-by-one to plan for: the tool must be applied to the *augmented* map
`(collinearity, minors)`, not to the collinearity map alone.  For
`Ψ = (cross3 (r z - r a) (r w - r a), cross3 (r z - r a) (r b - r a))` the range of the derivative is
`d^⊥ × d^⊥` of dimension exactly four, equal to the dimension of the four parameters, so the strict
inequality `finrank W < finrank (fderiv Ψ p).range` that
`Work.Drive.interior_projection_zeroSet_of_rank_except` needs *fails* for `Ψ` (and indeed the
projection of `{Ψ = 0}` is everything: every knot has a quadrisecant).  With the minors adjoined the
differential picks up the determinant direction (rank five greater than four), and the `except`
variant of the tool handles the points where the minor gradients vanish (the rank-at-most-two locus).
The four evaluation functionals at four distinct parameters are independent on the coefficient space,
so the values and velocities at the four points can be moved freely enough to make a chosen minor
non-zero.  Finitely many boxes cover the parameter region and the assembly (`dense_iInter_of_isOpen`,
`interior_eq_empty_iff_dense_compl`, `smallCorrectionKnot`) then gives a coefficient outside all the
bad sets, i.e. an approximant with all six clauses. -/
theorem genericFullDenseK : GenericFullDenseK := by
  intro r hr ε hε
  exact exists_close_generic_fullK_c2 hr ε hε

end Work.Drive
