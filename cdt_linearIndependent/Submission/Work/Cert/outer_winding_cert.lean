import Mathlib
import Submission.Work.Cert.Spec
import Submission.Work.Cert.wind_cert
import Submission.Work.Cert.outer_winding_core

/-! # Outer winding of `φ_A + 1/72` on the unit circle (Theorem A, Z2)

The certificate (the 46 lead-built winding chunks `WChunks/W000 … W045`, packaged as
`WindCertFacts` in `Submission/Work/Cert/wind_cert.lean`) together with the soundness contracts
`WindLeafSound`, `ArcCover` and `RotConsts` gives both conjuncts: `φ_A + 1/72` does not vanish on
`|z| = 1` and its logarithmic derivative has circle integral `2πI`.

The assembly is `Work.Cert.outer_winding_core` (quadrant winding lemma + grid drift + label turn
sum); this file only applies it to the certificate. -/

namespace Work.Cert

open Submission.CDTPlan in
theorem outer_winding_cert (hW : WindLeafSound) (hC : ArcCover) (hR : RotConsts) :
    (∀ z : ℂ, ‖z‖ = 1 → phiA z + 1 / 72 ≠ 0) ∧
      circleIntegral (fun z => logDeriv (fun w => phiA w + 1 / 72) z) 0 1 =
        2 * (Real.pi : ℂ) * Complex.I :=
  outer_winding_core hW hC hR wind_cert

end Work.Cert
