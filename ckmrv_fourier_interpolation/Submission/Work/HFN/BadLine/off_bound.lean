import Mathlib
import Submission.Work.Asymptotics.HalfFunnel.lowBadDefs
import Submission.Work.Asymptotics.HalfFunnel.Kaxis_cusp_of_bounded
import Submission.Work.Asymptotics.KaxisMid.Main
import Submission.Work.Asymptotics.Kaxis_local_coincidence
import Submission.Work.Asymptotics.Kaxis_principal_part_bound
import Submission.Work.Asymptotics.orbit_imagAxis_of_mem_DomainD
import Submission.Work.Asymptotics.eq_one_or_neg_one_or_S_of_smul_imagAxis
import Submission.Work.HFN.HalfFunnel.lowBad_Kaxis_bound

namespace Work.HFN.BadLine
open Work.Asymptotics  -- ck-hfn-fix: fork moved out of Work.Asymptotics

/-- **Boundedness of the CKMRV kernel on the bad-line region, away from the spike window.**

For `τ` in the bad-line region `Work.Asymptotics.HalfFunnel.lowBadSet` (`τ ∈ 𝒟`,
`1/2 ≤ Im τ ≤ 2`, `|Re τ| > 3/4`) and `0 < t ≤ lowT = 3` with `1/8 ≤ |t - Im τ|`, the kernel
`Kaxis (Kfun ℓ d) τ t` is bounded by a constant independent of `τ` and `t`.

The hypothesis keeps the contour point `i t` away from the translate pole `z = τ - tsign τ`
(at height `Im τ`, a genuine pole); the only remaining point of the `SL(2,ℤ)`-orbit of `τ`
approaching the contour as `Re τ → ±1` is the `S`-branch `z = S (τ - tsign τ)` (at height
`1/Im τ`), where the residue vanishes and the cleared kernel vanishes linearly.  This is the
statement proved (with the "far"/"near" split of the bad-line analysis) in
`Work.Asymptotics.HalfFunnel.lowBad_Kaxis_bound`, which is recorded here under the name
requested by the bad-line development. -/
theorem off_bound (ℓ : Work.Kernels.LogLambdaData) (d : Nat) (hd : d = 8 ∨ d = 24) :
    ∃ C : Real, 0 ≤ C ∧ ∀ (τ : UpperHalfPlane) (t : Real),
      Work.Asymptotics.HalfFunnel.lowBadSet τ → 0 < t → t ≤ Work.Asymptotics.HalfFunnel.lowT →
      (1 / 8 : Real) ≤ |t - τ.im| →
      ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t‖ ≤ C :=
  Work.HFN.HalfFunnel.lowBad_Kaxis_bound ℓ d hd

end Work.HFN.BadLine
