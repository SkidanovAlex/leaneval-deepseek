import Mathlib
import Submission.Work.MotC5N3.Defs
import Submission.Work.MotC5N3.AK
import Submission.Work.MotAS.ASResidual
import Submission.Work.MotK.TGen.ZRatFuncBridge
import Submission.Work.MotC5N3.ASZTwistDivPlaneGeomGen
import Submission.Work.MotC5N3.ASZChartPresentationGen

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotC5N3

-- K6 of the AS (Artin-Schreier) branch, generic in the base field `K`: the function field of the
-- residual curve `Z = V(radical (ZIAS (aK K D) (bK K D) g))` of the AS Crauder-Katz link is the AS
-- twist field of the class `2 * g`.  This is the `RatFunc 𝕜 ↦ K`, `fAS 𝕜 ↦ g` fork of
-- `Work.MotAS.ASZTwistDiv2` (whose proof in MotAS is
-- `ASZTwistDivPlaneGeomV2 ∘ ASZChartPresentation` composed with `Work.MotK.TGen.ZRatFuncBridge`).
--
-- ============================ STATUS ============================
-- The statement is assembled below from its two **independent** leaves:
--
-- * `Work.MotC5N3.ASZChartPresentationGen`
--   (`Submission/Work/MotC5N3/ASZChartPresentationGen.lean`): **PROVED and axiom-clean**
--   (`#print axioms` = `[propext, Classical.choice, Quot.sound]`) — the generic fork of
--   `Work.MotAS.ASZChartPresentation_gen`:
--   `Frac (K[Y₀..Y₄] ⧸ asChartIdeal a b h) ≅ ↥(twistFieldAS D h)` for every class `h : K`;
-- * `Work.MotC5N3.ASZTwistDivPlaneGeomGen`
--   (`Submission/Work/MotC5N3/ASZTwistDivPlaneGeomGen.lean`), a one-line wrapper of the single
--   designated K6 owner's `Work.MotC5N3.ASZTwistDivPlaneGeom` (which is
--   `ASZTwistDivPlaneGeom_of_three ∘ ASZTwistDivPlaneGeom_three`): the *geometric* leaf
--   `Frac (K[x₀,x₁,x₂] ⧸ √(ZIAS a b g)) ≅ Frac (K[Y₀..Y₄] ⧸ asChartIdeal a b (2 • g))` — the
--   paper's `C' = Jac²(C_g)` with twist class `2g`; its class-`3 * g` core
--   `ASZTwistDivPlaneGeom_three` is the last open K6 leaf (the lead's
--   `Submission/Work/MotC5N3/K6_RULING.md` records the Gröbner certificates proving the statement,
--   class `2 • g` included).  Until that leaf is discharged (and the temporary import cycle of
--   `MotC5N3/ASZChartNegIso` with `MotAS/ASZTwistDivPlaneGeomV2` — see
--   `Submission/Work/MotC5N3/STATUS_ASZTwistDiv2.md` — is resolved) this module does not build; once
--   it is discharged, this file is sorry-free with no further edit needed.
--
-- (`[CharP 𝕜 5]`, which the geometric leaf carries, is derived below from `[Algebra 𝕜 K]` and
-- `[CharP K 5]`: the algebra map `𝕜 → K` from a field into a nontrivial ring is injective, so
-- `RingHom.charP` gives the characteristic of `𝕜`.)
theorem ASZTwistDiv2 (K : Type) [Field K] [CharP K 5] {𝕜 : Type} [Field 𝕜] [Algebra 𝕜 K]
    (D : Work.MotV.KleinData 𝕜) (hD : Work.MotV5.KleinData.ASGood D) (g : K)
    (hg : ¬ ∃ u : K, u ^ 5 - u = g) :
    Nonempty (FractionRing (Polynomial (MvPolynomial (Fin 3) K ⧸
        Ideal.radical (Work.MotAS.ZIAS (Work.MotC5N3.aK K D) (Work.MotC5N3.bK K D) g))) ≃ₐ[K]
      RatFunc ↥(Work.MotC5N3.twistFieldAS D (2 • g))) := by
  haveI : CharP 𝕜 5 :=
    RingHom.charP (algebraMap 𝕜 K) (algebraMap 𝕜 K).injective 5
  obtain ⟨e₁⟩ := ASZTwistDivPlaneGeomGen K D hD g hg
  obtain ⟨e₂⟩ := ASZChartPresentationGen K D hD (2 • g)
  exact Work.MotK.TGen.ZRatFuncBridge K
    (MvPolynomial (Fin 3) K ⧸ Ideal.radical (Work.MotAS.ZIAS (aK K D) (bK K D) g))
    ↥(twistFieldAS D (2 • g)) ⟨e₁.trans e₂⟩

end Work.MotC5N3
