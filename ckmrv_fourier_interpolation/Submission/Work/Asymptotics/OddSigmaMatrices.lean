/-
# The explicit six-dimensional odd-weight matrices `oddMS`, `oddMT`

Let `R = ℂ[SL(2,ℤ)]` and `𝓘_odd = (T-I)²R + S(T-I)²R + (1+z)R`, the odd-weight defect ideal
of `Work.Asymptotics.OddIdeal`.  In the basis
`(μ₀, μ₁, μ₂, μ₃, μ₄, μ₅) = (1, T⁻¹, S*T*S, S, S*T⁻¹, T*S)`
of `R/𝓘_odd` (whose classes span the quotient by `Work.Asymptotics.spanning_Mp_idealIOdd`),
the matrices of right multiplication by `S` and by `T` are the integral matrices `oddMS` and
`oddMT` below.  Together with `oddMS * oddMS = -1` and `(oddMS * oddMT)^3 = -1` they define a
six-dimensional representation `SL(2,ℤ) → GL₆(ℂ)` with `-I ↦ -1`, which is the "odd"
companion of the paper's six-dimensional representation `σ` of `PSL(2,ℤ)`.

The representation itself is constructed in a separate statement, using the universal
property of the classical presentation `SL(2,ℤ) = ⟨S,T | S⁴ = 1, S² = (ST)³⟩`; here we only
record the matrices and the elementary matrix identities that the propagation argument
needs.
-/
import Mathlib

open Matrix

noncomputable section

namespace Work.Asymptotics

/-- The matrix of right multiplication by `S` on `R/𝓘_odd` in the basis
`(1, T⁻¹, S*T*S, S, S*T⁻¹, T*S)`. -/
def oddMS : Matrix (Fin 6) (Fin 6) ℂ :=
  !![0, 0, 0, 1, 0, 0;
     0, 0, 0, 2, 0, -1;
     0, 0, 0, -2, 1, 0;
     -1, 0, 0, 0, 0, 0;
     -2, 0, -1, 0, 0, 0;
     -2, 1, 0, 0, 0, 0]

/-- The matrix of right multiplication by `T` on `R/𝓘_odd` in the basis
`(1, T⁻¹, S*T*S, S, S*T⁻¹, T*S)`. -/
def oddMT : Matrix (Fin 6) (Fin 6) ℂ :=
  !![2, -1, 0, 0, 0, 0;
     1, 0, 0, 0, 0, 0;
     0, 0, 0, 2, 0, -1;
     0, 0, 0, 2, -1, 0;
     0, 0, 0, 1, 0, 0;
     2, 0, 1, 0, 0, 0]

/-- The matrices of the six basis elements `(1, T⁻¹, S*T*S, S, S*T⁻¹, T*S)`. -/
def oddMu : Fin 6 → Matrix (Fin 6) (Fin 6) ℂ :=
  ![1, oddMT⁻¹, oddMS * oddMT * oddMS, oddMS, oddMS * oddMT⁻¹, oddMT * oddMS]

end Work.Asymptotics

end
