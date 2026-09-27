import Mathlib
import Submission.Work.KT.Fund.Kappa

/-!
# `Work.KT.Fund.kl_defs` — the matrices of the linear clutching splitting

This file defines the two matrices into which the linear clutching function
`z • 1 + pullMat b` factors, for `b` a matrix over `C(X, ℂ)` commuting with an idempotent `E`
(the "inside" spectral projection of `b`, as produced by `Work.KT.Fund.spectral_split_out`):

* `klV X n b E = z • E + E b + (1 - E)`  ("inside" factor: `z + Eb` on the range of `E`),
* `klW X n b E = E + z • (1 - E) + (1 - E) b`  ("outside" factor),

together with the Bott unit `klV0 X n E = z • E + (1 - E)` that `klV` is homotopic to, and the
constant (in `z`) matrix `klW0` that `klW` is homotopic to.

These are the matrices of `Work.KT.Fund.kappa_lin`; the lemmas about them are proved in the
sibling modules (`kl_factor`, `kl_v_cls`, `kl_w_cls`).
-/

namespace Work.KT.Fund

open Matrix

noncomputable section

variable (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]

/-- The coordinate unit `z` of the circle, as a function on `X × S¹`. -/
def klz : C(X × Sph ℂ, ℂ) := (zUnit X : C(X × Sph ℂ, ℂ))

/-- `pullMat`, under a shorter name. -/
def klP {n : ℕ} (M : Matrix (Fin n) (Fin n) C(X, ℂ)) :
    Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ) :=
  pullMat X M

lemma klP_apply {n : ℕ} (M : Matrix (Fin n) (Fin n) C(X, ℂ)) (i j : Fin n)
    (y : X × Sph ℂ) : klP X M i j y = M i j y.1 := rfl

lemma klz_apply (y : X × Sph ℂ) : klz X y = (y.2 : ℂ) := rfl

/-- The "inside" factor `v = z E + E b + (1 - E)` of the linear splitting. -/
def klV (n : ℕ) (b E : Matrix (Fin n) (Fin n) C(X, ℂ)) :
    Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ) :=
  klz X • klP X E + klP X (E * b) + (1 - klP X E)

/-- The "outside" factor `w = E + z (1 - E) + (1 - E) b` of the linear splitting. -/
def klW (n : ℕ) (b E : Matrix (Fin n) (Fin n) C(X, ℂ)) :
    Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ) :=
  klP X E + klz X • (1 - klP X E) + klP X ((1 - E) * b)

/-- The Bott unit `z E + (1 - E)`, the `t = 0` end of the homotopy of `klV`. -/
def klV0 (n : ℕ) (E : Matrix (Fin n) (Fin n) C(X, ℂ)) :
    Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ) :=
  klz X • klP X E + (1 - klP X E)

/-- The constant-in-`z` matrix `E + (1 - E) b`, the `t = 0` end of the homotopy of `klW`. -/
def klW0 (n : ℕ) (b E : Matrix (Fin n) (Fin n) C(X, ℂ)) : Matrix (Fin n) (Fin n) C(X, ℂ) :=
  E + (1 - E) * b

end

end Work.KT.Fund
