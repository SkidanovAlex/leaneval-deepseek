import Mathlib
import Submission.Work.MotT.Defs
import Submission.Work.MotK.LinkCertGen

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Bridge: the generic T-twist vocabulary of `Work.MotK` and `Work.MotT`

`Submission/Work/MotK/LinkCertGen.lean` (area `MotK`) and `Submission/Work/MotT/Defs.lean`
(area `MotT`, which consumes the K-route's node `T8`) define the *same* generic T-twist data:
`AlgebraicClosure K`, the function field of `D.E` over it, a chosen fifth root of `h`, the twisted
Klein coordinates `y_i = w^{-i}κ_i/κ_0` and the twist field `K(C_h) ⊂ K̄(E)`.

The two definitions are **definitionally equal** — the only cosmetic difference is the name of the
chosen fifth root and of the field abbreviations — as witnessed by the `rfl`-lemmas below.  In
particular `LinkCertTGenInf` (`Submission.Work.MotK.LinkCertTGenInf`, the `MotK` version of the
K-route deliverable `T8`, proved over `twistFieldTG`) *is* the `MotT` statement over
`twistFieldTK`; `linkCertTInput_transfer` below records that transfer.

**Warning (reported to the `MotT` area).**  `Work.MotT.LinkCertTInput K` — the form in which
`MotT` states node `T8` — quantifies over *all* fields `K` with no hypothesis.  The design
(`MOTIVIC_S45_LEAD.md` §2.4, `GUIDE_K5K6.md` §5) needs `[Infinite K]` (to choose the general point
`p` of the twisted quadric, finitely many conditions being avoided) and `ringChar K ≠ 5` (in
characteristic 5 the group `μ₅` is infinitesimal, the T-twist degenerates, and the whole
Crauder–Katz quadrature is replaced by the Artin–Schreier route of `Submission/Work/MotV5`).
-/

set_option autoImplicit false

namespace Work.MotK

variable (K : Type) [Field K]

/-- The two algebraic closures agree definitionally. -/
theorem KbG_eq_KbK : Work.MotK.KbG K = Work.MotT.KbK K := rfl

/-- The two ambient function fields agree definitionally. -/
theorem OmG_eq_OmK (D : Work.MotV.KleinData K) :
    Work.MotK.OmG K D = Work.MotT.OmK D := rfl

/-- The two twisted-coordinate families agree definitionally. -/
theorem twCoordG_eq_twCoordK (D : Work.MotV.KleinData K) (h : K) (i : Fin 5) :
    Work.MotK.twCoordG K D h i = Work.MotT.twCoordK D h i := rfl

/-- **The two twist fields are the same field**, definitionally. -/
theorem twistFieldTG_eq_twistFieldTK (D : Work.MotV.KleinData K) (h : K) :
    Work.MotK.twistFieldTG K D h = Work.MotT.twistFieldTK D h := rfl

/-- **The transfer of the K-route deliverable `T8` to the `MotT` vocabulary**: a proof of the
generic link certificate over `Work.MotK.twistFieldTG` (with the hypotheses the design needs) is a
proof of the `MotT` statement over `Work.MotT.twistFieldTK`. -/
theorem linkCertTInput_transfer (hk : ringChar K ≠ 5)
    (H : ∀ (D : Work.MotV.KleinData K), D.Good → ∀ h : K, h ≠ 0 →
      Nonempty (Work.MotV.LinkCert K (Work.MotK.twistFieldTG K D h)
        (Work.MotK.twistFieldTG K D (h ^ 2)))) :
    ∀ (D : Work.MotV.KleinData K), D.Good → ∀ h : K, h ≠ 0 →
      Nonempty (Work.MotV.LinkCert K (Work.MotT.twistFieldTK D h)
        (Work.MotT.twistFieldTK D (h ^ 2))) :=
  H

end Work.MotK
