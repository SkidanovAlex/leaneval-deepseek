import Mathlib
import Submission.Work.MotAS.ASData
import Submission.Work.MotAS.ASMinv
import Submission.Work.MotAS.asM_mul_asMinv
import Submission.Work.MotAS.asMinv_mul_asM

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The Lagrange (Vandermonde) matrix of the AS coordinates, forked to `Work.MotC5N3`

This is the `Work.MotC5N3` fork of the matrix part of the AS-EQ node
(`Submission/Work/MotAS/ASMinv.lean`, `…/asM_mul_asMinv.lean`, `…/asMinv_mul_asM.lean`).

`asM w i j = (w + i)^j` is the Vandermonde matrix on the five nodes `w, w+1, …, w+4`, and
`asMinv w j i = δ_{j,0} - (w+i)^{4-j}` is the Lagrange interpolation matrix (the explicit inverse
of `asM w` in characteristic `5`, over any commutative ring).  These are *base-field independent*
matrix identities: they mention no base field at all, so the fork is the declaration level of the
re-packaging — the same matrices and the same two identities, available under `Work.MotC5N3`.

The Artin–Schreier Galois coordinates of `Submission/Work/MotC5N3/Defs.lean` are
`asTwY = (asM (asRoot g))⁻¹ · κ`, and the Lagrange-matrix inversion is exactly what turns them into
the polynomial expressions used in `Work.MotC5N3.twistFieldAS_eq`.
-/

set_option autoImplicit false

namespace Work.MotC5N3

/-- Fork of `Work.MotAS.asM`: the Vandermonde matrix `(w + i)^j` on the five AS nodes. -/
abbrev asM {R : Type*} [CommRing R] (w : R) : Matrix (Fin 5) (Fin 5) R := Work.MotAS.asM w

/-- Fork of `Work.MotAS.asV`: the "power sum" matrix `(w+i)^{4-j}`. -/
abbrev asV {R : Type*} [CommRing R] (w : R) : Matrix (Fin 5) (Fin 5) R := Work.MotAS.asV w

/-- Fork of `Work.MotAS.asMinv`: the explicit Lagrange interpolation matrix
`asMinv w j i = δ_{j,0} - (w+i)^{4-j}`, i.e. the inverse of `asM w` in characteristic `5`. -/
abbrev asMinv {R : Type*} [CommRing R] (w : R) : Matrix (Fin 5) (Fin 5) R := Work.MotAS.asMinv w

/-- **`asM w * asMinv w = 1`** in any commutative ring of characteristic `5`. -/
theorem asM_mul_asMinv {R : Type*} [CommRing R] (h5 : (5 : R) = 0) (w : R) :
    asM w * asMinv w = (1 : Matrix (Fin 5) (Fin 5) R) :=
  Work.MotAS.asM_mul_asMinv h5 w

/-- **`asMinv w * asM w = 1`** in any commutative ring of characteristic `5`. -/
theorem asMinv_mul_asM {R : Type*} [CommRing R] (h5 : (5 : R) = 0) (w : R) :
    asMinv w * asM w = (1 : Matrix (Fin 5) (Fin 5) R) :=
  Work.MotAS.asMinv_mul_asM h5 w

end Work.MotC5N3
