import Mathlib
import Submission.Work.Asymptotics.KhatE1.KdevE2Defs
import Submission.Work.Asymptotics.KhatE1Core.Kdev8_matching_bridge
import Submission.Work.Asymptotics.Compact.kminus_tail_core
import Submission.Work.Asymptotics.funnelTailBasic
import Submission.Work.Asymptotics.KhatE1.KdevE2_strip_bound
import Submission.Work.Asymptotics.Funnel24Aux
import Submission.Work.Asymptotics.KMinusFunnelAtoms
import Submission.Work.Asymptotics.DeltaFun_upper_sharp

namespace Work.Asymptotics.KhatE1

open UpperHalfPlane

/-! A local copy of `KhatE1.KdevA3` and `KhatE1.KdevA3_eq` (which live in
`KhatE1/KdevBracket_cleared.lean`, a module that imports `KdevBracketClearedRestBound` and would
therefore create an import cycle).  The declarations keep their original names. -/

noncomputable def KdevA3 (ℓ : Work.Kernels.LogLambdaData) (τ : ℍ) : ℂ :=
  ((3456 : ℂ) * (Real.pi : ℂ))⁻¹ *
    (Work.Asymptotics.Compact.R8_p2 ℓ τ
      + 36864 * Work.Kernels.E4Fun τ
      - 480 * (Work.Kernels.psi2 ℓ τ * Work.Kernels.E14Fun τ / Work.Kernels.DeltaFun τ)
      + Work.Kernels.psi4 ℓ τ * (-55296 + 480 * Work.Kernels.jInvariantFun τ))

/-- **The reduced form of `A₃`.**  Using `E1combo8 = j(ψ₄ - ψ₂E₆/E₄) + 576(2E₄ - ψ₄)`,
`E₁₄ = E₄²E₆` and `Δj = E₄³` the coefficient collapses to a combination of `j(τ)·E1combo8`,
`E₄`, `ψ₄`:
`3456π·A₃ = (24jτ - 21024)·E1combo8 - 2949120·E₄ - 8847360·ψ₄`. -/
theorem KdevA3_eq (ℓ : Work.Kernels.LogLambdaData) (τ : ℍ) (hF : Work.Asymptotics.Funnel τ) :
    ((3456 : ℂ) * (Real.pi : ℂ)) * KdevA3 ℓ τ
      = (24 * Work.Kernels.jInvariantFun τ - 21024) * Work.Asymptotics.E1combo8 ℓ τ
        - 2949120 * Work.Kernels.E4Fun τ - 8847360 * Work.Kernels.psi4 ℓ τ := by
  have hD : Work.Kernels.DeltaFun τ ≠ 0 := Work.Kernels.ClassicalFacts.DeltaFun_ne_zero τ
  have hE4 : Work.Kernels.E4Fun τ ≠ 0 := Work.Asymptotics.funnel_E4_ne_zero τ hF
  have hj : Work.Kernels.jInvariantFun τ
      = (Work.Kernels.E4Fun τ) ^ 3 / Work.Kernels.DeltaFun τ := by
    rw [eq_div_iff hD, mul_comm]
    exact Work.Kernels.ClassicalFacts.DeltaFun_mul_jInvariantFun τ
  rw [KdevA3, Work.Asymptotics.E1combo8, Work.Asymptotics.Compact.R8_p2, Work.Kernels.E14Fun, hj]
  field_simp
  ring

end Work.Asymptotics.KhatE1
