import Mathlib

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The Riesz-projection route to a smooth retraction onto the Grassmannian

Vocabulary for `Work.PTGeometric.grassmannianRetraction`.

`Gr_k(ℝⁿ)` is the set `Gr n k` of orthogonal projections of trace `k`.  We build the retraction
from the *Riesz projection* (contour integral) of the symmetrised part `symm A = (A + A†)/2`
around the contour `|z - 1| = 1/2`, written in a purely real form.

* `cc θ = 1 + cos θ / 2`, `ss θ = sin θ / 2` are the real and imaginary parts of
  `z θ = 1 + e^{iθ}/2` on the contour.
* `contDen x θ = (cc θ • 1 - x)² + (ss θ)² • 1` is `(z - x)(z̄ - x)`, a polynomial in `x`.
* `contNum x θ = (cc θ - 1)•(cc θ • 1 - x) + (ss θ)² • 1` is the real part of `(z - 1)(z̄ - x)`.
  Its imaginary part is `ss θ • (1 - x)`, which is a scalar multiple of an operator and will be
  shown to integrate to zero in the self-adjoint case.
* `Phi x` is `(2π)⁻¹ ∫₀^{2π} (contDen x θ)⁻¹ * contNum x θ dθ`, the real form of the Riesz
  projection of `x`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

open scoped ContDiff
open Set Function MeasureTheory

namespace Work.PTGeometric

noncomputable section

/-- `ℝⁿ` as a Euclidean space. -/
abbrev Amb (n : ℕ) : Type := EuclideanSpace ℝ (Fin n)

/-- The space of (continuous) endomorphisms of `ℝⁿ`. -/
abbrev EndOp (n : ℕ) : Type := Amb n →L[ℝ] Amb n

variable {n : ℕ}

/-- The real part `1 + cos θ / 2` of the point `z θ = 1 + e^{iθ}/2` of the contour
`|z - 1| = 1/2`. -/
def cc (θ : ℝ) : ℝ := 1 + (1 / 2) * Real.cos θ

/-- The imaginary part `sin θ / 2` of the contour point `z θ = 1 + e^{iθ}/2`. -/
def ss (θ : ℝ) : ℝ := (1 / 2) * Real.sin θ

/-- The "contour denominator" `(z - x)(z̄ - x)` of the resolvent integrand, written out as a real
operator.  It is a polynomial in `x` of degree `2`. -/
def contDen (x : EndOp n) (θ : ℝ) : EndOp n :=
  (cc θ • 1 - x) * (cc θ • 1 - x) + (ss θ) ^ 2 • 1

/-- The real part of the contour numerator `(z - 1)(z̄ - x)`, as a real operator. -/
def contNum (x : EndOp n) (θ : ℝ) : EndOp n :=
  (cc θ - 1) • (cc θ • 1 - x) + (ss θ) ^ 2 • 1

/-- The imaginary part of the contour numerator `(z - 1)(z̄ - x)`, as a real operator:
it is `ss θ • (1 - x)`. -/
def contNumIm (x : EndOp n) (θ : ℝ) : EndOp n :=
  ss θ • (1 - x)

/-- The integrand of the (real form of the) Riesz projection. -/
def contIntegrand (x : EndOp n) (θ : ℝ) : EndOp n :=
  Ring.inverse (contDen x θ) * contNum x θ

/-- **The Riesz projection**, in real form: the contour integral of `(z - x)⁻¹ (z - 1)` around the
circle `|z - 1| = 1/2`, of which only the real part is written down.  On self-adjoint `x` whose
spectrum avoids the contour this is the orthogonal projection onto the spectral subspace of `x`
lying inside the contour. -/
def Phi (x : EndOp n) : EndOp n :=
  (2 * Real.pi)⁻¹ • ∫ θ in 0..(2 * Real.pi), contIntegrand x θ

/-- The symmetrised part `(A + A†)/2` of an operator. -/
def symm (A : EndOp n) : EndOp n := (2 : ℝ)⁻¹ • (A + ContinuousLinearMap.adjoint A)

/-- `Gr_k(ℝⁿ)`, the Grassmannian of rank-`k` orthogonal projections, as a set of operators. -/
def Gr (n k : ℕ) : Set (EndOp n) :=
  {P | ContinuousLinearMap.adjoint P = P ∧ P * P = P ∧ LinearMap.trace ℝ (Amb n) P = (k : ℝ)}

/-- The open set on which the retraction is defined: operators whose symmetrised part is within
`1/4` of the Grassmannian. -/
def good (n k : ℕ) : Set (EndOp n) :=
  ⋃ P ∈ Gr n k, {A | ‖symm A - P‖ < 1/4}

/-- The retraction: the Riesz projection of the symmetrised part. -/
def Rmap (A : EndOp n) : EndOp n := Phi (symm A)

end

end Work.PTGeometric
