import Mathlib
import Submission.Work.Asymptotics.KhatE1Core.Sm3Split
import Submission.Work.Asymptotics.KhatE1Core.Bracket24TailCore

/-!
# The `K₊`-side assembly: `KPlus24Group = KPlus24Ref + dKPlus24`

`KPlus24Group ℓ τ z = -(c·z²·(Sm1 + Sm2 + Sm3 + Sm4 + Sm5))`, and this module assembles the five
splits of the preceding slices into the `K₊` counterpart of `KMinus24Split`:

  `KPlus24Group ℓ τ z = KPlus24Ref ℓ τ z + dKPlus24 ℓ τ z`,

where `KPlus24Ref` is an **explicit polynomial in `E = Ept z`** (odd and even powers, degree
`≤ 12` from the products `E4Ref³·S0`, `j(τ)·Φ_ref·q²`, …) whose coefficients involve only the
`τ`-atoms (`E4Fun τ`, `E6Fun τ`, `E2Fun τ`, `jInvariantFun τ`, `psi2`, `psi4`, `r0`, `r1`, `r2`,
`R0`, `Th0`, `Q1`, `Phiref`, `Uref`, `(τ:ℂ)`) and the `z`-atoms `(z:ℂ)`, `S0z z`, and where
`dKPlus24` is an explicit sum of products of the deviations
`dPhi, dE4c, dE6, dE2S, dE14, dI4, dI4z, dDq, dDelta, dUfun, Donly` with reference cofactors.

Together with `KMinus24Split` (`KMinus24Group = (3456π)⁻¹(PolyKM + DevKM)`) this gives the full
scaffolding

  `X = KPlus24Group + KMinus24Group = [polynomial in E] + [deviation sum]`

for the `E(z)`-expansion of `Bracket24ExpansionHold`.
-/

namespace Work.Asymptotics.KhatE1Core

open UpperHalfPlane

noncomputable section

/-- Sum of the five `K₊` references. -/
def KPlusSumRef (τ z : ℍ) : ℂ :=
  Sm1Ref τ z + Sm2Ref τ z + Sm3Ref τ z + Sm4Ref τ z + Sm5Ref τ z

/-- Sum of the five `K₊` deviations. -/
def dKPlusSum (τ z : ℍ) : ℂ :=
  dSm1 τ z + dSm2 τ z + dSm3 τ z + dSm4 τ z + dSm5 τ z

/-- **The sum split**: `Sm1 + … + Sm5 = KPlusSumRef + dKPlusSum`. -/
lemma KPlusSum_eq_ref_add (τ z : ℍ) :
    (Work.Asymptotics.K24F.Sm1 τ z + Work.Asymptotics.K24F.Sm2 τ z
        + Work.Asymptotics.K24F.Sm3 τ z + Work.Asymptotics.K24F.Sm4 τ z
        + Work.Asymptotics.K24F.Sm5 τ z)
      = KPlusSumRef τ z + dKPlusSum τ z := by
  rw [Sm1_eq_ref_add τ z, Sm2_eq_ref_add τ z, Sm3_eq_ref_add τ z,
    Sm4_eq_ref_add τ z, Sm5_eq_ref_add τ z]
  simp only [KPlusSumRef, dKPlusSum]
  ring

/-- The reference part of `KPlus24Group`. -/
def KPlus24Ref (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ) : ℂ :=
  -(Work.Asymptotics.K24F.c * (z : ℂ) ^ 2 * KPlusSumRef τ z)

/-- The deviation part of `KPlus24Group`. -/
def dKPlus24 (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ) : ℂ :=
  -(Work.Asymptotics.K24F.c * (z : ℂ) ^ 2 * dKPlusSum τ z)

/-- **The `K₊`-split**: `KPlus24Group = KPlus24Ref + dKPlus24`, exactly. -/
lemma KPlus24Group_eq_ref_add (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ) :
    KPlus24Group ℓ τ z = KPlus24Ref ℓ τ z + dKPlus24 ℓ τ z := by
  have h := KPlusSum_eq_ref_add τ z
  simp only [KPlus24Group, KPlus24Ref, dKPlus24]
  rw [h]
  ring

end

end Work.Asymptotics.KhatE1Core
