/-
Area `A7REC`, file `Char/c1bLib.lean`: a **shim** re-exporting the parts of the shared library that
the `c1b` leaves (`Work.A7REC.Char.c1bD8`, `c1bZSig`, `c1bIntegral`, `c1bSumInt`, `c1bDegree`)
need.

It exists so that the delegated leaves can be stated against `OddOrder.RepresentationTheory`
(`IrreducibleCharacter`, `ClassFunction`) and `OddOrder.Algebra`
(`exists_int_of_isIntegral_of_forall_complexRingEquiv_fixed`, ...) through a single
`depends_on` entry that lives inside `Submission/Work/`.
-/
import Submission.OddOrder.Algebra.GaloisRationalInteger
import Submission.OddOrder.GroupTheory.RepresentationTheory.ColumnOrthogonality
