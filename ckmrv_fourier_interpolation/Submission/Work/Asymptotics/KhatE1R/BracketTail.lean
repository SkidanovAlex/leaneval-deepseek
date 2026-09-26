import Mathlib
import Submission.Work.Asymptotics.KhatE1Sharp.WresPolyBound_core
import Submission.Work.Asymptotics.KhatE1R.Kdev8WresTailGlue
import Submission.Work.Asymptotics.KhatE1R.Kdev8WresPolyDevBound
import Submission.Work.Asymptotics.KhatE1R.WresDevBound

namespace Work.Asymptotics.KhatE1RAssembly

theorem KdevBracket_rest_R (ℓ : Work.Kernels.LogLambdaData) :
    ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
      ∀ (τ z : UpperHalfPlane) (t : ℝ), Work.Asymptotics.Funnel τ → τ.im + 1 ≤ t →
        -1 ≤ z.re → z.re ≤ 2 → z.im = t →
        ‖Work.Asymptotics.KhatE1Core.Kdev8Bracket ℓ τ z
            - 2 * Work.Asymptotics.KhatE1.KdevE2 ℓ τ z * (Work.Residues.Ept z) ^ 2‖
          ≤ C * ‖Work.Kernels.qParamFun τ‖ * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M
              * Real.exp (-(2 * Real.pi * t)) :=
  Work.Asymptotics.KhatE1R.Kdev8BracketTail_of_three ℓ
    (Work.Asymptotics.KhatE1Core.WresPolyPol_bound ℓ)
    (Work.Asymptotics.KhatE1R.Kdev8WresPolyDevBound ℓ)
    (Work.Asymptotics.KhatE1RCore.WresDevBound ℓ)

end Work.Asymptotics.KhatE1RAssembly
