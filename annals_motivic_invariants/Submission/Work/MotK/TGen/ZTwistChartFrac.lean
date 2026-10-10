import Mathlib
import Submission.Work.MotK.TGen.ZTwistDivGeomDefs
import Submission.Work.MotK.TGen.ZpgPsiDefs
import Submission.Work.MotK.TGen.ZTwistChartFracMain
import Submission.Work.MotK.TGen.ZTwistChartFracMain

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.MotK.TGen.ZTwistChartFrac`

The chart `y₀ = 1` of the twisted Klein curve `C_{h²} = V(kleinTwP a b h²)` is birational to the
plane model `V(zpgE a b h)` of the residual curve: the fraction fields agree.  This is the
"geometric leaf" of node K6 (the paper's `C' = Jac²(C_h)`, twist `2T = h²`).

The definitions and the graph map `zpgPsi` now live in
`Submission/Work/MotK/TGen/ZpgPsiDefs.lean` (module `Submission.Work.MotK.TGen.ZpgPsiDefs`), and the
proof of the theorem below is assembled in
`Submission/Work/MotK/TGen/ZTwistChartFracMain.lean` (which needs `zpgPsi` and hence cannot be
imported by this file, but this file *can* import it).
-/

namespace Work.MotK.TGen

theorem ZTwistChartFrac (K : Type) [Field K] (a b h : K)
    (ha : a ≠ 0) (hb : b ≠ 0) (hh : h ≠ 0)
    (hirr : Irreducible (Work.MotK.TwCensus.ZElim2 a b h)) :
    Nonempty (FractionRing (MvPolynomial (Fin 4) K ⧸
        Ideal.radical (Work.MotK.TGen.zpgI4 a b h)) ≃ₐ[K]
      FractionRing (MvPolynomial (Fin 2) K ⧸ Ideal.span {Work.MotK.TGen.zpgE a b h})) :=
  ZTwistChartFracMain K a b h ha hb hh hirr

end Work.MotK.TGen
