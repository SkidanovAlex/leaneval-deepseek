import Mathlib
import Submission.Work.MotK.KleinData

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.MotAS.phiS`, `Work.MotAS.phiAS` — the explicit maps of the AS residual

`Work.MotAS.ASZTwistDivPlaneGeom` reduces (see
`Submission/Work/MotAS/STATUS_ASZTwistDivPlaneGeom.md`) to the following two explicit linear maps.

* `p(X) = aX⁴ + bX³ - bX² - aX = X(X-1)(aX²+(a+b)X+a)`, `p(1) = 0`.
* `phiS a b` is the matrix of `p(S)`, `S` the cyclic shift `(Sy)_k = y_{k+1}`:
  `(phiS a b).mulVec y k = Σ_j p[(j-k) mod 5] · y_j`.  It satisfies
  `Σ_k (phiS a b ·ᵥ y)_k = 0`, i.e. `phiS` maps into the hyperplane `H = {Σ z = 0}`, and
  * `phiS a b (V(kleinP a b)) ⊆ V(kleinR a b) ∩ H` (verified pointwise over `𝔽₂₅` at many
    `(a,b)`, and ideal-level at `(a,b) ∈ {(1,1),(2,1),(5,1),(3,2),(6,1),(4,3)}`).
* `phiAS a b` is `D⁻¹ · p(T₁) = D⁻¹ · M_{3v}⁻¹ · p(S) · M_{3v}`, where `T₁` is the binomial matrix
  `(T₁)_{lj} = C(j,l)` and `D = diag(2^j)`; equivalently `M_x⁻¹ S M_x = T₁` for every `x`, so the
  conjugation is independent of `v` and `phiAS` is `K`-rational.  It satisfies
  * `phiAS a b (V(kleinPAS a b (3*g))) ⊆ V(kleinRAS a b g)`, row 4 of `phiAS` being zero, so the
    image lies in `{ẑ₄ = 0}` — i.e. `phiAS` maps the AS-twisted Klein curve of class `3g` onto the
    residual curve of the AS link.

The six nonzero entries of `phiAS` are
`(0,1) ↦ 3a+b`, `(0,3) ↦ 3a+4b`, `(1,2) ↦ 3a+b`, `(1,4) ↦ a+3b`, `(2,3) ↦ a+2b`, `(3,4) ↦ 4a+3b`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Work.MotAS

/-- **The split map** `Φ = p(S)`, `p(X) = aX⁴+bX³-bX²-aX`: `Φ_{k,j} = p[(j-k) mod 5]`. -/
def phiS {R : Type*} [CommRing R] (a b : R) (k j : Fin 5) : R :=
  ![0, -a, -b, b, a] (j - k)

/-- **The AS map** `Phi5 = D⁻¹ · p(T₁)`: the explicit six nonzero entries. -/
def phiAS {R : Type*} [CommRing R] (a b : R) (k j : Fin 5) : R :=
  match (k : ℕ), (j : ℕ) with
  | 0, 1 => 3 * a + b
  | 0, 3 => 3 * a + 4 * b
  | 1, 2 => 3 * a + b
  | 1, 4 => a + 3 * b
  | 2, 3 => a + 2 * b
  | 3, 4 => 4 * a + 3 * b
  | _, _ => 0

end Work.MotAS
