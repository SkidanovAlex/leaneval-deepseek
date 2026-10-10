import Submission.Work.MotAS.ASData

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The explicit inverse Vandermonde matrix `asMinv`

Part of the subproject `Submission/Work/MotAS` (`Work.MotAS`), node **AS-EQ**
(`Work.MotAS.twistFieldAS_eq`).

`asM w i j = (w+i)^j` is the Galois-coordinate Vandermonde matrix.  The matrix inverse of a
Vandermonde matrix is given by Lagrange interpolation: writing `Q_i(Z) = ∏_{i' ≠ i} (Z - w - i')`,
whose coefficients are (in characteristic `5`, using `(w+i)^5 - (w+i) = w^5 - w`) the power sums
`1, α_i, α_i^2, α_i^3, α_i^4 - 1` with `α_i = w + i`, we get

`(asM w)⁻¹ j i = δ_{j,0} - α_i^{4-j}`.

So the inverse `asMinv w` is `(if j = 0 then 1 else 0) - (w+i)^{4-j}`, a *polynomial* matrix in `w`;
this is what makes the Lagrange coordinates `y = asMinv w · κ` computable (in particular `y_0`).

The two entries of the claim are the content of the matrix identities
`asM w * asMinv w = 1` and `asMinv w * asM w = 1` (both in characteristic `5`, over any commutative
ring), which live in `Submission/Work/MotAS/asM_mul_asMinv.lean` and
`Submission/Work/MotAS/asMinv_mul_asM.lean`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Work.MotAS

variable {R : Type*} [CommRing R]

/-- The "power sum" matrix `(w+i)^{4-j}` in the exponents `j = 0,…,4`. -/
def asV (w : R) : Matrix (Fin 5) (Fin 5) R := Matrix.of fun j i => (w + (i : ℕ)) ^ (4 - (j : ℕ))

/-- **The explicit inverse Vandermonde matrix**: the Lagrange coefficient matrix
`asMinv w j i = δ_{j,0} - (w+i)^{4-j}`, i.e. the coefficient of `Z^j` in `-∏_{i' ≠ i}(Z - w - i')`.

In characteristic `5` and for `w` arbitrary one has `asM w * asMinv w = 1` and
`asMinv w * asM w = 1`; see the two delegated lemmas. -/
def asMinv (w : R) : Matrix (Fin 5) (Fin 5) R :=
  Matrix.of fun j i => (if (j : ℕ) = 0 then 1 else 0) - (w + (i : ℕ)) ^ (4 - (j : ℕ))

end Work.MotAS
