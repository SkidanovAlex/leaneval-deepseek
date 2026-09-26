import Mathlib
import Submission.Work.Asymptotics.KhatE1Core.KdevA4
import Submission.Work.Asymptotics.KhatE1Core.Kminus4
import Submission.Work.Asymptotics.KhatE1Core.KdevA4_eq

/-!
# The `j`-decomposition of the `E(z)^4`-coefficient `KdevA4num`

`KdevA4num = 3456π·tailC⁻¹·Phi4 + (β₄ + (j(τ)-720)β₂ + γβ₀ + Dev4)` is a polynomial of degree at
most two in `j(τ) = E₄(τ)³/Δ(τ)`, because `E₁₄/Δ = j·(E₆/E₄)`.  This file splits both summands
into their `j⁰, j¹, j²`-parts,

* `Phi4j0, Phi4j1, Phi4j2` for the `K₊`-coefficient `Phi4` (`Phi4_eq_split`), and
* `BRj0, BRj1, BRj2` for the `K₋` bracket `KdevA4BR` (`BR_eq_split`),

and assembles them into `KdevA4j0, KdevA4j1, KdevA4j2` with

  `KdevA4num = KdevA4j2 · j² + KdevA4j1 · j + KdevA4j0`   (`KdevA4num_eq_jdecomp`).

Since `Δ(τ)·j(τ) = E₄(τ)³`, multiplying the `j^m`-coefficient by `Δ(τ)^m` clears the pole, which
is what will make each coefficient amenable to a cusp-expansion estimate: numerically
`KdevA4 = O(q_τ)`, so one expects `A_m = O(q_τ^m (scale τ)^N (1+t)^M)`.

The scalar `tailC⁻¹` is kept *factored* (not folded into the `(6i/π)`-monomials), so that the
`ring` normalisations on the two sides of the identities below have literally the same `i`- and
`π`-monomials (`ring` treats `Complex.I` as an indeterminate and cannot use `i² = -1`).
-/

namespace Work.Asymptotics.KhatE1Core

open UpperHalfPlane

noncomputable section

open Work.Kernels

/-- The `j²`-part of `Phi4`. -/
noncomputable def Phi4j2 (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ) : ℂ :=
    - (1 : ℂ) * (E6Fun τ * (6 * Complex.I / (Real.pi : ℂ)) * (6 * Complex.I / (Real.pi : ℂ)) * (τ : ℂ))
    + (2 : ℂ) * ((z : ℂ) * E6Fun τ * (6 * Complex.I / (Real.pi : ℂ)) * (τ : ℂ))
    - (2 : ℂ) * ((z : ℂ) * E4Fun τ * (6 * Complex.I / (Real.pi : ℂ)) * (τ : ℂ) * E2Fun τ)
    + (1 : ℂ) * ((z : ℂ) * E4Fun τ * (6 * Complex.I / (Real.pi : ℂ)) * (6 * Complex.I / (Real.pi : ℂ)))
    - (1 : ℂ) * ((z : ℂ) * (z : ℂ) * (τ : ℂ) * E2Fun τ * E2Fun τ * (E6Fun τ / E4Fun τ))
    + (1 : ℂ) * ((z : ℂ) * (z : ℂ) * (6 * Complex.I / (Real.pi : ℂ)) * E2Fun τ * (E6Fun τ / E4Fun τ))
    - (1 : ℂ) * ((z : ℂ) * (z : ℂ) * E6Fun τ * (τ : ℂ))
    + (2 : ℂ) * ((z : ℂ) * (z : ℂ) * E4Fun τ * (τ : ℂ) * E2Fun τ)
    - (1 : ℂ) * ((z : ℂ) * (z : ℂ) * E4Fun τ * (6 * Complex.I / (Real.pi : ℂ)))

/-- The `j¹`-part of `Phi4`. -/
noncomputable def Phi4j1 (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ) : ℂ :=
    (984 : ℂ) * (E6Fun τ * (6 * Complex.I / (Real.pi : ℂ)) * (6 * Complex.I / (Real.pi : ℂ)) * (τ : ℂ))
    - (2016 : ℂ) * ((z : ℂ) * E6Fun τ * (6 * Complex.I / (Real.pi : ℂ)) * (τ : ℂ))
    + (3456 : ℂ) * ((z : ℂ) * E4Fun τ * (6 * Complex.I / (Real.pi : ℂ)) * (τ : ℂ) * E2Fun τ)
    - (1728 : ℂ) * ((z : ℂ) * E4Fun τ * (6 * Complex.I / (Real.pi : ℂ)) * (6 * Complex.I / (Real.pi : ℂ)))
    + (744 : ℂ) * ((z : ℂ) * (z : ℂ) * (τ : ℂ) * E2Fun τ * E2Fun τ * (E6Fun τ / E4Fun τ))
    - (744 : ℂ) * ((z : ℂ) * (z : ℂ) * (6 * Complex.I / (Real.pi : ℂ)) * E2Fun τ * (E6Fun τ / E4Fun τ))
    + (1032 : ℂ) * ((z : ℂ) * (z : ℂ) * E6Fun τ * (τ : ℂ))
    - (3504 : ℂ) * ((z : ℂ) * (z : ℂ) * E4Fun τ * (τ : ℂ) * E2Fun τ)
    + (1752 : ℂ) * ((z : ℂ) * (z : ℂ) * E4Fun τ * (6 * Complex.I / (Real.pi : ℂ)))

/-- The `j⁰`-part of `Phi4`. -/
noncomputable def Phi4j0 (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ) : ℂ :=
    - (55440 : ℂ) * (E6Fun τ * (6 * Complex.I / (Real.pi : ℂ)) * (6 * Complex.I / (Real.pi : ℂ)) * (τ : ℂ))
    + (122256 : ℂ) * ((z : ℂ) * E6Fun τ * (6 * Complex.I / (Real.pi : ℂ)) * (τ : ℂ))
    - (787536 : ℂ) * ((z : ℂ) * E4Fun τ * (6 * Complex.I / (Real.pi : ℂ)) * (τ : ℂ) * E2Fun τ)
    + (393768 : ℂ) * ((z : ℂ) * E4Fun τ * (6 * Complex.I / (Real.pi : ℂ)) * (6 * Complex.I / (Real.pi : ℂ)))
    - (67392 : ℂ) * ((z : ℂ) * (z : ℂ) * E6Fun τ * (τ : ℂ))
    + (834624 : ℂ) * ((z : ℂ) * (z : ℂ) * E4Fun τ * (τ : ℂ) * E2Fun τ)
    - (417312 : ℂ) * ((z : ℂ) * (z : ℂ) * E4Fun τ * (6 * Complex.I / (Real.pi : ℂ)))

/-- The `K₋`-bracket of `KdevA4num` (the `K⁻`-half, in the spelling of `Kminus4_eq`). -/
noncomputable def KdevA4BR (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ) : ℂ :=
    ((10948608 * E4Fun τ + 19906560 * psi4 ℓ τ
                + 61056 * (jInvariantFun τ * psi4 ℓ τ)
                - 61056 * (psi2 ℓ τ * E14Fun τ / DeltaFun τ)
              + (jInvariantFun τ - 720)
                * (-41472 * E4Fun τ + 912384 * Work.Asymptotics.Compact.Xc ℓ z * E4Fun τ
                  + 870912 * psi4 ℓ τ
                  + 1152 * (psi2 ℓ τ * E14Fun τ / DeltaFun τ)
                  - 1152 * (jInvariantFun τ * psi4 ℓ τ)))
            + (((jInvariantFun τ - 720) ^ 2 - 179280 - 24 * jInvariantFun τ)
                * (-3456 * Work.Asymptotics.Compact.Xc ℓ z * E4Fun τ + 1728 * psi4 ℓ τ))
            + Work.Asymptotics.KhatE1Core.Dev4 ℓ τ z)

/-- The `j²`-part of the `K₋`-bracket. -/
noncomputable def BRj2 (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ) : ℂ :=
    (1152 : ℂ) * ((psi2 ℓ τ * E6Fun τ / E4Fun τ))
    + (576 : ℂ) * (psi4 ℓ τ)
    - (3456 : ℂ) * (Work.Asymptotics.Compact.Xc ℓ z * E4Fun τ)

/-- The `j¹`-part of the `K₋`-bracket. -/
noncomputable def BRj1 (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ) : ℂ :=
    - (811008 : ℂ) * ((psi2 ℓ τ * E6Fun τ / E4Fun τ))
    - (847872 : ℂ) * (psi4 ℓ τ)
    - (41472 : ℂ) * (E4Fun τ)
    + (5971968 : ℂ) * (Work.Asymptotics.Compact.Xc ℓ z * E4Fun τ)

/-- The `j⁰`-part of the `K₋`-bracket. -/
noncomputable def BRj0 (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ) : ℂ :=
    (85888512 : ℂ) * (psi4 ℓ τ)
    + (40787712 : ℂ) * (E4Fun τ)
    - (1360862208 : ℂ) * (Work.Asymptotics.Compact.Xc ℓ z * E4Fun τ)

/-- **The `j`-split of `Phi4`.** -/
theorem Phi4_eq_split (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ)
    (hΔ : DeltaFun τ ≠ 0) (hE4 : E4Fun τ ≠ 0) :
    Phi4 τ z = Phi4j2 ℓ τ z * jInvariantFun τ ^ 2
      + Phi4j1 ℓ τ z * jInvariantFun τ + Phi4j0 ℓ τ z := by
  rw [Phi4, Phi4j2, Phi4j1, Phi4j0,
    show jInvariantFun τ = E4Fun τ ^ 3 / DeltaFun τ from rfl]
  simp only [E14Fun]
  field_simp
  ring

/-- **The `j`-split of the `K₋`-bracket.** -/
theorem BR_eq_split (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ)
    (hΔ : DeltaFun τ ≠ 0) (hE4 : E4Fun τ ≠ 0) :
    KdevA4BR ℓ τ z = BRj2 ℓ τ z * jInvariantFun τ ^ 2
      + BRj1 ℓ τ z * jInvariantFun τ + BRj0 ℓ τ z := by
  rw [KdevA4BR, BRj2, BRj1, BRj0, Dev4,
    show jInvariantFun τ = E4Fun τ ^ 3 / DeltaFun τ from rfl]
  simp only [E14Fun]
  field_simp
  ring

/-- `KdevA4num` split as `3456π·tailC⁻¹·Phi4` plus the `K₋`-bracket. -/
theorem KdevA4num_eq_Phi4_add_BR (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ) :
    KdevA4num ℓ τ z
      = ((3456 : ℂ) * (Real.pi : ℂ)) * (Work.Asymptotics.Compact.tailC)⁻¹ * Phi4 τ z
        + KdevA4BR ℓ τ z := by
  rw [KdevA4num, KdevA4BR]

/-- The `j²`-coefficient of `KdevA4num`. -/
noncomputable def KdevA4j2 (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ) : ℂ :=
  ((3456 : ℂ) * (Real.pi : ℂ)) * (Work.Asymptotics.Compact.tailC)⁻¹ * Phi4j2 ℓ τ z
    + BRj2 ℓ τ z

/-- The `j¹`-coefficient of `KdevA4num`. -/
noncomputable def KdevA4j1 (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ) : ℂ :=
  ((3456 : ℂ) * (Real.pi : ℂ)) * (Work.Asymptotics.Compact.tailC)⁻¹ * Phi4j1 ℓ τ z
    + BRj1 ℓ τ z

/-- The `j⁰`-coefficient of `KdevA4num`. -/
noncomputable def KdevA4j0 (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ) : ℂ :=
  ((3456 : ℂ) * (Real.pi : ℂ)) * (Work.Asymptotics.Compact.tailC)⁻¹ * Phi4j0 ℓ τ z
    + BRj0 ℓ τ z

/-- **The `j`-decomposition of `KdevA4num`.** -/
theorem KdevA4num_eq_jdecomp (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ)
    (hΔ : DeltaFun τ ≠ 0) (hE4 : E4Fun τ ≠ 0) :
    KdevA4num ℓ τ z
      = KdevA4j2 ℓ τ z * jInvariantFun τ ^ 2
        + KdevA4j1 ℓ τ z * jInvariantFun τ + KdevA4j0 ℓ τ z := by
  rw [KdevA4num_eq_Phi4_add_BR, Phi4_eq_split ℓ τ z hΔ hE4, BR_eq_split ℓ τ z hΔ hE4,
    KdevA4j2, KdevA4j1, KdevA4j0]
  ring

end

end Work.Asymptotics.KhatE1Core
