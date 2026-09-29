import Mathlib
import Submission.CDTPlan.InterfacesA
import Submission.Work.ANum.psiA_deriv
import Submission.Work.Cert.a_conj2_core2
import Submission.Work.Cert.leaf_sound
import Submission.Work.Cert.slitStage_sound3
import Submission.Work.Cert.luneStage_sound
import Submission.Work.Cert.theta_encl
import Submission.Work.Cert.theta_identity
import Submission.Work.Cert.expLo_sound
import Submission.Work.Cert.arc_cover2
import Submission.Work.Cert.rot_consts
import Submission.Work.Cert.rot_consts2
import Submission.Work.Cert.conj2_cert2
import Submission.Work.Cert.outer_winding_cert
import Submission.Work.Cert.wind_leaf_sound
import Submission.Work.ANum3.phiA_analytic_ext
import Submission.Work.ANum3.phiA_inner_unique
import Submission.Work.ANum3.phiA_annulus_zero_free

/-! # Area ANum — certified numerics for Theorem A (`Submission.CDTPlan.ANumerics`)

`ANumerics` is the conjunction of three claims.

1. **conjunct 1** — `‖ψ_A'(0)‖ = 2383521894760738000000000/3774888615849058882987209`
   (exact algebra from the derivatives of the slit and lune maps):
   `Work.ANum.psiA_deriv_norm` (`Submission/Work/ANum/psiA_deriv.lean`).

2. **conjunct 2** — `rearrInt (fun k => (γ(k+1) − γ(k))/14) φ_A ≤ 112/10`, the rearrangement
   integral of the `l = 2` family, from the lead-built integer arc certificate
   (`Submission/Work/Cert/`, "verify, don't compute"): the checker `Cert.Defs`, the arc chunks
   `Cert.Chunks/`, the soundness contracts `Cert.Spec` with their proofs (`Cert.leaf_sound`,
   `Cert.slitStage_sound3`, `Cert.luneStage_sound`, `Cert.theta_encl`, `Cert.theta_identity`,
   `Cert.expLo_sound`, `Cert.arc_cover2`, `Cert.rot_consts`, `Cert.rot_consts2`), the certificate
   `Cert.conj2_cert2`, and the assembly `Cert.a_conj2_core2` (certificate v4, `NARC2 = 1024` arcs
   per circle, value 11.1330 ≤ 11.2).

3. **conjunct 3** — `φ_A(z) ≠ −1/72` for `1/1000 ≤ ‖z‖ ≤ 1`, by the argument principle on the
   annulus (`Work.ANum3.phiA_annulus_zero_free`): the outer winding of `φ_A + 1/72` on `|z| = 1`
   is one (`Cert.outer_winding_cert` applied to the winding certificate `Cert.wind_cert` and the
   soundness contracts), and the only zero inside `|z| < 1/1000` is simple
   (`Work.ANum3.phiA_inner_unique`). -/

namespace Work.ANum

open Submission.CDTPlan

/-- Conjunct 1 of `ANumerics`: the exact value of `‖ψ_A'(0)‖` (the conformal radius of the
Theorem-A contour). -/
theorem a_numerics_deriv :
    ‖deriv psiA 0‖ = 2383521894760738000000000 / 3774888615849058882987209 :=
  psiA_deriv_norm

/-- Conjunct 2 of `ANumerics`: the rearrangement integral bound, from the integer certificate. -/
theorem a_numerics_conj2 :
    rearrInt (fun k => (gammaA k.succ - gammaA k.castSucc) / 14) phiAfam ≤ 112 / 10 :=
  Work.Cert.a_conj2_core2
    (Work.Cert.leaf_sound Work.Cert.rot_consts Work.Cert.expLo_sound
      Work.Cert.slitStage_sound3 Work.Cert.luneStage_sound Work.Cert.theta_encl
      Work.Cert.theta_identity)
    Work.Cert.arc_cover2 Work.Cert.rot_consts2 Work.Cert.conj2_cert2

/-- Conjunct 3 of `ANumerics`: `φ_A(z) ≠ −1/72` on the annulus `1/1000 ≤ ‖z‖ ≤ 1`. -/
theorem a_numerics_conj3 : ∀ z : ℂ, 1 / 1000 ≤ ‖z‖ → ‖z‖ ≤ 1 → phiA z ≠ -1 / 72 :=
  Work.ANum3.phiA_annulus_zero_free Work.ANum3.phiA_analytic_ext
    (Work.Cert.outer_winding_cert
      (Work.Cert.wind_leaf_sound Work.Cert.rot_consts Work.Cert.slitStage_sound3
        Work.Cert.luneStage_sound Work.Cert.theta_encl Work.Cert.theta_identity)
      Work.Cert.arc_cover Work.Cert.rot_consts)
    Work.ANum3.phiA_inner_unique

theorem a_numerics : ANumerics :=
  ⟨a_numerics_deriv, a_numerics_conj2, a_numerics_conj3⟩

end Work.ANum
