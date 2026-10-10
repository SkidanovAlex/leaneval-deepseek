import Mathlib
import Submission.Work.MotK.TGen.ZPlaneModel
import Submission.Work.MotK.TwCensus.ZTwist
import Submission.Work.MotK.TwCensus.KummerInvariance
import Submission.Work.MotK.TGen.ZTwistDivGeomDefs
import Submission.Work.MotK.TGen.ZTwistDivGeomCerts
import Submission.Work.MotK.TGen.ZTwistDivGeomA
import Submission.Work.MotK.TGen.ZTwistChartFrac
import Submission.Work.MotK.TGen.ZTwistQidealChart

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotK.TGen

-- CONTEXT.  This is the single remaining *geometric* leaf of node K6 (the paper's `C' = Jac²(C_h)`,
-- twist class `2T = h²`) of the T-twisted Crauder--Katz link.  Its companion `ZTwistDivFrac`
-- (`Submission/Work/MotK/TGen/ZTwistDiv.lean`) is PROVED from it, from `ZPlaneModel` and from
-- `ZChartPresentation`; through them this statement feeds `Work.MotK.TGen.STClass`, hence the census
-- `Work.MotK.TGenCensus` and the deliverable `Work.MotK.LinkCertT`.
--
-- This is the statement `Work.MotK.TGen.ZTwistDivPlane` on disk, copied verbatim (same hypotheses)
-- so that it can be delegated without touching the file that also contains the proved companion;
-- when it lands, `ZTwistDivFrac` is re-pointed to it.
--
-- Its content: the plane model `V(ZElim2 a b h)` of the *residual curve* of the `h`-twisted link is
-- birational (`FractionRing`s agree) to the chart `y₀ = 1` of the twisted Klein curve
-- `C_{h²} = V(kleinTwP a b (h²))` — the exponent `h²` being the `(ℤ/5)ˣ`-level statement of the
-- ledger in `ZTwistDiv.lean`'s module docstring (base isomorphism with `Ψ^{-1}δ^CΨ = (δ^Z)³`), and
-- the C-side being taken with `Work.MotK.TwCensus.Qideal` (the radical of the twisted Pfaffians) and
-- **not** with `ZTwPlane`, which is not a model of `C_{h²}` (see the warning in that docstring).
--
-- Two reviews of this statement both warn that the *exponent* `h²` is the one unverified input (the
-- recorded point-count tables are taken at `h = 1`, and for `p ≡ 1 mod 5` the counts turn out to be
-- independent of the Kummer class, so they neither support nor refute `m = 2`); they also confirm
-- that the statement is the right leaf and is non-vacuous (`a = b = h = 1`, `hdisc = -11 ≠ 0`).
-- Determining `m` from the ledger's base-isomorphism computation is therefore part of this job, and
-- a `declare_false` supported by that computation would be as valuable as a proof: K6 has been the
-- acknowledged bottleneck of this area for several sessions.
--
-- Supporting material already on disk: `ZElim2` and the `TGen/ZElim2*` campaign (elimination
-- certificate, plane model, irreducibility), `ZPlaneModel`, `ZChartPresentation`,
-- `Work.MotK.TwCensus.KummerInvariance`, `Work.MotK.TGen.ZRatFuncBridge`, and the quadric/coordinate
-- facts about the twisted Klein curve (`Work.MotK.TGen.TwCoordGKleinTw`).
theorem ZTwistDivPlaneGeom (K : Type) [Field K] (hk : ringChar K ≠ 5) (a b h : K)
    (ha : a ≠ 0) (hb : b ≠ 0) (hh : h ≠ 0)
    (hdisc : a ^ 10 - 11 * a ^ 5 * b ^ 5 - b ^ 10 ≠ 0)
    (hirr : Irreducible (Work.MotK.TwCensus.ZElim2 a b h)) :
    Nonempty (FractionRing (MvPolynomial (Fin 2) K ⧸
        Ideal.span {Work.MotK.TwCensus.ZElim2 a b h}) ≃ₐ[K]
      FractionRing (MvPolynomial (Fin 5) K ⧸
        (Work.MotK.TwCensus.Qideal a b (h ^ 2) ⊔
          Ideal.span {MvPolynomial.X (0 : Fin 5) - 1}))) := by
  obtain ⟨eA⟩ := ZTwistDivGeomA K a b h ha hb hh
  obtain ⟨eC⟩ := ZTwistChartFrac K a b h ha hb hh hirr
  obtain ⟨eQ⟩ := ZTwistQidealChart K a b h ha hb hh
  exact ⟨(eA.trans eC.symm).trans eQ.symm⟩

end Work.MotK.TGen
