import Mathlib
import Submission.Work.Asymptotics.KhatE1Defs
import Submission.Work.Asymptotics.KhatE1.E1combo8_bound
import Submission.Work.Residues.ThetaEpt

namespace Work.Asymptotics.KhatE1

open UpperHalfPlane

/-!
## The leading term of the funnel deviation and the leading-term-free remainder

The deviation `Kdev = K̂ - 𝒢̂ = (K̂ - 𝒢̂)` of `KhatE1Defs` has, as a function of `z`, an
expansion in powers of `E(z) = Ept z = e^{πiz}`, whose coefficients are functions of `τ` and
polynomials in `z`.  Its `E(z)⁰`-coefficient vanishes, and its `E(z)¹`-coefficient is the
(`z`-independent) combination `E1combo8 ℓ τ / (288π)`.  Removing that leading term, the
remainder

  `KdevRem ℓ τ z = Kdev ℓ 8 τ z - (E1combo8 ℓ τ / (288π)) · Ept z`

starts at `E(z)²`, so the `z ↦ z+1`-invariant half

  `KdevEven τ z = (Kdev τ z + Kdev τ (z+1))/2 = (KdevRem τ z + KdevRem τ (z+1))/2`

of the deviation is *one power of `E(z)` smaller* than `Kdev` itself.
-/

/-- The `E(z)¹`-coefficient of the funnel deviation `Kdev`. -/
noncomputable def KdevLead (ℓ : Work.Kernels.LogLambdaData) (τ : ℍ) : ℂ :=
  Work.Asymptotics.E1combo8 ℓ τ / (288 * (Real.pi : ℂ))

/-- The deviation with its leading `E(z)¹`-term removed. -/
noncomputable def KdevRem (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ) : ℂ :=
  Work.Asymptotics.Kdev ℓ 8 τ z - KdevLead ℓ τ * Work.Residues.Ept z

/-- `Ept (z+1) = -Ept z`. -/
lemma Ept_vadd_one (z : ℍ) : Work.Residues.Ept ((1 : ℝ) +ᵥ z) = -Work.Residues.Ept z := by
  rw [← UpperHalfPlane.modular_T_smul, Work.Residues.Ept_T]

/-- **The invariant half is the `T`-average of the leading-term-free deviation.**  The leading
`E(z)¹`-term drops out because `E(z+1) = -E(z)`. -/
lemma KdevEven_eq_KdevRem (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ) :
    Work.Asymptotics.KdevEven ℓ 8 τ z
      = (KdevRem ℓ τ z + KdevRem ℓ τ ((1 : ℝ) +ᵥ z)) / 2 := by
  unfold KdevRem KdevLead
  rw [Work.Asymptotics.KdevEven, Ept_vadd_one]
  ring

end Work.Asymptotics.KhatE1
