import Mathlib
import Submission.Work.Asymptotics.KhatE1Core.Bracket24XtruncDefs
import Submission.Work.Asymptotics.KhatE1Core.XtruncDev.Atoms
import Submission.Work.Asymptotics.KhatE1Core.Bracket24BCoeffs
import Submission.Work.Asymptotics.KhatE1Core.XWrTreeDefs

namespace Work.Asymptotics.KhatE1Core.XtruncDev

open UpperHalfPlane
open Work.Residues (Ept)

noncomputable section

/-- The fifth-order truncation of `𝓛`: `LT` plus the `-(48/5)e⁵` term. -/
def LT5 (ℓ : Work.Kernels.LogLambdaData) (z : ℍ) : ℂ :=
  LT ℓ z - (48 / 5 : ℂ) * (Ept z) ^ 5

/-- `A₂₄` with the `z`-atoms replaced by their truncations and `𝓛` by `LT5`. -/
def A24TC (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ) : ℂ :=
  -3456 * Work.Kernels.DeltaFun τ * E14T z * LT5 ℓ z
    - (Work.Kernels.psi2 ℓ τ * Work.Kernels.E10Fun τ
        - Work.Kernels.psi4 ℓ τ * Work.Kernels.E8Fun τ) * E10T z * D2T z

/-- The `K₋`-group of the intermediate `Xint`. -/
def KMinusT (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ) : ℂ :=
  invDeltaT z * A24TC ℓ τ z
    + Work.Asymptotics.Compact.C24 ℓ τ * WT z
    + (Work.Kernels.jInvariantFun τ - jzT z) * WT z * Work.Asymptotics.Compact.B24 ℓ τ
    + ShT τ z * Work.Asymptotics.Compact.br0 24 ℓ τ z
    - ShT τ z * Ept z
        * (Work.Asymptotics.E1combo24 ℓ τ + Work.Asymptotics.KhatE1.Am24 ℓ τ)

/-- The intermediate expression: the bracket with the `z`-atoms replaced by their truncations
(and `𝓛` by `LT5`). -/
def Xint (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ) : ℂ :=
  KPlus24GroupT τ z + ((3456 : ℂ) * (Real.pi : ℂ))⁻¹ * KMinusT ℓ τ z

end

end Work.Asymptotics.KhatE1Core.XtruncDev
