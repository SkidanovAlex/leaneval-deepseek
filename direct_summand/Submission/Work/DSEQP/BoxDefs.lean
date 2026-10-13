/-
DSEQP: auxiliary definitions used in the proof that `R[Z]/(Z_i^p - z_i)` is a free `R`-module.

The `R`-algebra `R' = R[Z]/(Z_i^p - z_i) = Work.DSSER.serRing R p z` has `R`-basis given by the
"box" monomials `Z^u = ∏ i, Z i ^ u i` with `u i < p` (the standard monomials for the ideal
`(Z_i^p - z_i)`).  This file introduces

* `boxIdx u`, the exponent vector `Fin d →₀ ℕ` of a box index `u : Fin d → Fin p`,
* `boxMono R p z u = ∏ i, Z i ^ (u i : ℕ)`, the box monomial itself, and
* `std R p z`, the `R`-linear "standard form" map which sends a monomial `X^s` to the box
  monomial of `s mod p`, with the `p`-th powers of the variables evaluated at the `z i`.

The key properties of `std` (`std` vanishes on `serRel p z`, and `std (X^u) = e_u` for box `u`)
are proved in separate files.
-/
import Mathlib
import Submission.Work.DSSER.Basic

universe u

namespace Work.DSEQP

/-- The exponent vector of a box index `u : Fin d → Fin p`, as an element of `Fin d →₀ ℕ`. -/
noncomputable def boxIdx {p d : ℕ} (u : Fin d → Fin p) : Fin d →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun i => (u i : ℕ)

@[simp]
theorem boxIdx_apply {p d : ℕ} (u : Fin d → Fin p) (i : Fin d) :
    boxIdx u i = (u i : ℕ) := rfl

/-- The "box" monomial `Z^u = ∏ i, Z i ^ (u i : ℕ)` in `R[Z]/(Z_i^p - z_i)`, for
`u : Fin d → Fin p` (all exponents strictly smaller than `p`). -/
noncomputable def boxMono (R : Type u) [CommRing R] (p : ℕ) {d : ℕ} (z : Fin d → R) :
    (Fin d → Fin p) → Work.DSSER.serRing R p z :=
  fun u => ∏ i, Work.DSSER.serZ p z i ^ (u i : ℕ)

/-- The `R`-linear "standard form" map on `R[X_1,…,X_d]`: on monomials it is given by
reducing the exponents modulo `p` and replacing each `X_i ^ p` by `z_i`, and then reading off
the coefficient of each box monomial.  Explicitly, for `s : Fin d →₀ ℕ` the image of
`monomial s c` is the function `u ↦ if (∀ i, s i % p = u i) then c * ∏ i, z i ^ (s i / p) else 0`.

In particular `std R p z (monomial s 1) u` is the coefficient of `Z^u` in the normal form
of `X^s`. -/
noncomputable def std (R : Type u) [CommRing R] (p : ℕ) {d : ℕ} (z : Fin d → R) :
    MvPolynomial (Fin d) R →ₗ[R] ((Fin d → Fin p) → R) :=
  (MvPolynomial.basisMonomials (Fin d) R).constr R fun s u =>
    if ∀ i, s i % p = (u i : ℕ) then Work.DSSER.zMono z (fun i => s i / p) else 0

end Work.DSEQP
