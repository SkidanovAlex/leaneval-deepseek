import Mathlib
import Submission.Work.MotT.Defs
import Submission.Work.MotK.LinkCertTGenInf
import Submission.Work.MotK.GenBridge

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotWire

/-- **Audit node `T8` (`Work.MotT.LinkCertTInput`) for an infinite base field of characteristic
`≠ 5`**, i.e. the Crauder–Katz affine link certificate for the T-twist of the Klein curve: for every
good Klein datum `D` over `K` and every nonzero Kummer class `h ∈ K`, the twist fields
`K(C_h)` and `K(C_{h²})` are linked by a `Work.MotV.LinkCert`.

This is the `MotT`-vocabulary form of the K-route deliverable `Work.MotK.LinkCertTGenInf`; the two
twist fields agree definitionally (`Work.MotK.twistFieldTG_eq_twistFieldTK`), so the transfer
`Work.MotK.linkCertTInput_transfer` applies directly. -/
theorem linkCertTInput_of_charNeFive (K : Type) [Field K] [Infinite K] (hk : ringChar K ≠ 5) :
    Work.MotT.LinkCertTInput K :=
  Work.MotK.linkCertTInput_transfer K hk (fun D hD h hh =>
    Work.MotK.LinkCertTGenInf K hk D hD h hh)

end Work.MotWire
