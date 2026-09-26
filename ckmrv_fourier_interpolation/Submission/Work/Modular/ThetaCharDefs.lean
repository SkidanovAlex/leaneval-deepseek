import Mathlib
import Submission.Work.Modular.Basic
import Submission.Work.Modular.Lattice

/-!
# One-dimensional theta summands and the `E₈` parametrisation

This file collects the shared vocabulary for the decomposition of the `E₈` theta series into
eighth powers of the Jacobi theta functions.

* `thetaChar τ c n = exp (π I τ (n + c)²)`: the one-dimensional theta summand with
  characteristic `c`.  For `c = 0` its sum is `θ₃`, for `c = 1/2` it is `θ₂`.
* `thetaSign n = exp (π I n)`: the sign `(-1)^n`, which produces `θ₄` out of `thetaChar τ 0`
  and which vanishes when combined with characteristic `1/2`.
* `e8ParamMap (m, δ) = m + δ/2`: the parametrisation of `ℤ⁸ × {0,1}` by the vectors of
  `ℝ⁸` whose coordinates are either all integral or all half-integral.
-/

open UpperHalfPlane
open scoped Real MatrixGroups

namespace Work.Modular

/-- One-dimensional theta summand with characteristic `c : ℝ`:
`exp (π I τ (n + c)²)`. -/
noncomputable def thetaChar (τ : ℂ) (c : ℝ) (n : ℤ) : ℂ :=
  Complex.exp (π * Complex.I * τ * ((n : ℂ) + (c : ℂ)) ^ 2)

/-- The sign `(-1)^n`, written as `exp (π I n)` for `n : ℤ`. -/
noncomputable def thetaSign (n : ℤ) : ℂ := Complex.exp (π * Complex.I * (n : ℂ))

/-- The index set parametrising the `E₈` lattice: a vector of `ℤ⁸` together with a coset
parity class `δ ∈ {0,1}`. -/
abbrev E8Idx := (Fin 8 → ℤ) × Fin 2

/-- The characteristic `δ/2 ∈ {0, 1/2}` attached to a parity class `δ : Fin 2`. -/
noncomputable def charOf (δ : Fin 2) : ℝ := ((δ : ℕ) : ℝ) / 2

/-- The parametrisation `(m, δ) ↦ m + δ/2` of `ℤ⁸ × {0,1}` into `ℝ⁸`, whose image on the
even-sum part is exactly the `E₈` lattice. -/
noncomputable def e8ParamMap (p : E8Idx) : EuclideanSpace ℝ (Fin 8) :=
  WithLp.toLp 2 (fun i => (p.1 i : ℝ) + charOf p.2)

@[simp]
theorem e8ParamMap_apply (p : E8Idx) (i : Fin 8) :
    (e8ParamMap p).ofLp i = (p.1 i : ℝ) + charOf p.2 := rfl

end Work.Modular
