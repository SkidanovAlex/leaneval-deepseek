/-
# The far window on `E`, assembled (plain-window route)

`Work.Asymptotics.SKEC.FarWindow_proof`: the far piece `1 ≤ t ≤ Im (S • w) - 1` of the plain
polynomial window on the cusp-`0` tile `E = KEpsilon`, obtained from the assembly lemma
`Work.Asymptotics.EWindow_far_of` and its four inputs

* `Work.Asymptotics.Xi8_low_bound` (clean, colleague's file),
* `Work.Asymptotics.SKEC.SKX24_low_bound` (a private compiling copy of `Xi24_low_bound`, whose
  original module currently fails to elaborate),
* `Work.Asymptotics.EpolyWindowE_ncusp_low_bound` (clean, colleague's file),
* `Work.Asymptotics.divisor_lower_lowIm` (clean).

With it the *plain* polynomial window on the whole range `0 < t ≤ scale w`
(`Work.Asymptotics.SKEC.EpolyWindowE_clean_far`) and hence, together with the sharp tail
`Work.Asymptotics.SKEC.E_tail_clean`, the two-regime control `Work.Asymptotics.ERegimes ℓ d`
(`Work.Asymptotics.SKEC.ERegimes_clean`) are available without the tautologically tainted
`Kfun_middle` / `EpolyWindowE_one` / `ETailE_one` chain.
-/
import Mathlib
import Submission.Work.Asymptotics.KEpsilon
import Submission.Work.Asymptotics.EBase
import Submission.Work.Asymptotics.SKEC.Defs
import Submission.Work.Asymptotics.SKEC.WindowE
import Submission.Work.Asymptotics.SKEC.WindowCleanFar
import Submission.Work.Asymptotics.SKEC.Xi24Clean
import Submission.Work.Asymptotics.EWindow_far
import Submission.Work.Asymptotics.EpolyWindowE_Ncusp
import Submission.Work.Asymptotics.Xi8_low_bound
import Submission.Work.Kernels.All

noncomputable section

open UpperHalfPlane ModularGroup
open scoped MatrixGroups UpperHalfPlane

namespace Work.Asymptotics

open Work.Kernels

/-- **The far window** (`Work.Asymptotics.EWindow_far`): the plain polynomial window on
`1 ≤ t ≤ Im (S • w) - 1`. -/
theorem FarWindow_proof (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) :
    FarWindow ℓ d :=
  EWindow_far_of ℓ Xi8_low_bound SKX24_low_bound
    (fun d hd => EpolyWindowE_ncusp_low_bound ℓ d hd) divisor_lower_lowIm d hd

/-- **The plain polynomial window on `E` up to `scale w`** (`Work.Asymptotics.EPolyWin` with
`N₀ = 1`). -/
theorem EpolyWindowE_clean_far (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) :
    ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
      ∀ (w : UpperHalfPlane) (t : ℝ), w ∈ KEpsilon → 0 < t →
        t ≤ Work.Kernels.scale w →
        ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) w t‖
          ≤ C * (Work.Kernels.scale w) ^ N * (1 + t) ^ M :=
  EpolyWindowE_of_far ℓ d hd (FarWindow_proof ℓ d hd)

end Work.Asymptotics
