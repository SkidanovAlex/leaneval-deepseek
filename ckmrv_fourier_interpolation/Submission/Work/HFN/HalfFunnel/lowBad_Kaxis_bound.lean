import Mathlib
import Submission.Work.Asymptotics.HalfFunnel.lowBadDefs
import Submission.Work.HFN.HalfFunnel.lowBad_Kaxis_bound_aux

/-!
# Boundedness of the CKMRV kernel on the bad-line set, away from the spike

For `τ` in the bad-line region `Work.Asymptotics.HalfFunnel.lowBadSet`
(`τ ∈ 𝒟`, `1/2 ≤ Im τ ≤ 2`, `|Re τ| > 3/4`) the contour point `z = i t` (`0 < t ≤ lowT = 3`)
is separated from the translate pole `z = τ - tsign τ` by the hypothesis
`1/8 ≤ |t - Im τ|`; the remaining approach of the pole to the contour is controlled by the
`S`-branch annihilation `KfunClear ℓ d (S • zpole τ) (zpole τ) = 0`.  The resulting bound

  `‖Kaxis (Kfun ℓ d) τ t‖ ≤ C`

with `C` independent of `τ` and `t` is proved in
`Work.Asymptotics.HalfFunnel.lowBad_Kaxis_bound_aux` (a separate module of the same
development); this module records the statement needed by
`Work.Asymptotics.HalfFunnel.lowBad_kernel_spike` and routes it through that proof.
-/

noncomputable section

namespace Work.HFN.HalfFunnel
open Work.Asymptotics Work.Asymptotics.HalfFunnel  -- ck-hfn-fix: fork moved out of Work.Asymptotics

/-- **Boundedness of the CKMRV kernel on the bad-line set away from the spike window.**

There is a constant `C ≥ 0` such that for every `τ ∈ lowBadSet` and every `0 < t ≤ lowT = 3`
with `1/8 ≤ |t - Im τ|` one has `‖Kaxis (Kfun ℓ d) τ t‖ ≤ C`.  See
`Work.Asymptotics.HalfFunnel.lowBad_Kaxis_bound_aux` for the proof. -/
theorem lowBad_Kaxis_bound (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (τ : UpperHalfPlane) (t : ℝ),
      Work.Asymptotics.HalfFunnel.lowBadSet τ → 0 < t → t ≤ Work.Asymptotics.HalfFunnel.lowT →
      (1 / 8 : ℝ) ≤ |t - τ.im| →
      ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t‖ ≤ C :=
  lowBad_Kaxis_bound_aux ℓ d hd

end Work.HFN.HalfFunnel
