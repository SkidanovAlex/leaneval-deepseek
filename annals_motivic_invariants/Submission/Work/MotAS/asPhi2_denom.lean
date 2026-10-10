import Mathlib
import Submission.Work.MotAS.SdualAS2Defs
import Submission.Work.MotAS.TwistField
import Submission.Work.MotV5.ASLocal.asPhi2_denom

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option maxHeartbeats 1000000

namespace Work.MotAS

open WeierstrassCurve WeierstrassCurve.Affine

/-- The zeroth component of the ruling point `asRuleQW a b g c t` is `A + t·B`, where
`A = asRuleQA a b g c 0` and `B = asRuleQB a b g c 0`. -/
theorem asRuleQW_zero_apply {R : Type*} [CommRing R] (a b g : R) (c : Fin 5 → R) (t : R) :
    Work.MotAS.asRuleQW a b g c t 0
      = Work.MotAS.asRuleQA a b g c 0 + t * Work.MotAS.asRuleQB a b g c 0 := by
  simp only [Work.MotAS.asRuleQW]

/-- **The chart-`2` normalising coordinate is nonzero.**  Writing `T = ↥(twistFieldAS D (fAS 𝕜))`
and `c = algebraMap ∘ asY0 D (fAS 𝕜)`, the zeroth component of the ruling point is
`asRuleQW a b g c RatFunc.X 0 = asRuleQA a b g c 0 + RatFunc.X * asRuleQB a b g c 0`.
The two coefficients live in `T`; the second one is nonzero because `asY0` is the projective
normalisation `y / y 0` of the affine coordinates `y = asTwY D (fAS 𝕜)` (whose ruling quadratic
form is nonzero by `Work.MotAS.asKleinQuad_ne_zero`), and `RatFunc.X` is transcendental over `T`. -/
theorem asPhi2_denom (𝕜 : Type) [Field 𝕜] [CharP 𝕜 5] (D : Work.MotV.KleinData 𝕜)
    (hD : Work.MotV5.KleinData.ASGood D) :
    Work.MotAS.asRuleQW (algebraMap 𝕜 (RatFunc ↥(Work.MotAS.twistFieldAS D (Work.MotV.fAS 𝕜))) D.a)
      (algebraMap 𝕜 (RatFunc ↥(Work.MotAS.twistFieldAS D (Work.MotV.fAS 𝕜))) D.b)
      (algebraMap (RatFunc 𝕜) (RatFunc ↥(Work.MotAS.twistFieldAS D (Work.MotV.fAS 𝕜))) (Work.MotV.fAS 𝕜))
      (fun j => algebraMap ↥(Work.MotAS.twistFieldAS D (Work.MotV.fAS 𝕜))
        (RatFunc ↥(Work.MotAS.twistFieldAS D (Work.MotV.fAS 𝕜))) (Work.MotAS.asY0 D (Work.MotV.fAS 𝕜) j))
      (RatFunc.X : RatFunc ↥(Work.MotAS.twistFieldAS D (Work.MotV.fAS 𝕜))) 0 ≠ 0 := by
  have hB : Work.MotAS.asRuleQB
      (algebraMap 𝕜 ↥(Work.MotAS.twistFieldAS D (Work.MotV.fAS 𝕜)) D.a)
      (algebraMap 𝕜 ↥(Work.MotAS.twistFieldAS D (Work.MotV.fAS 𝕜)) D.b)
      (algebraMap (RatFunc 𝕜) ↥(Work.MotAS.twistFieldAS D (Work.MotV.fAS 𝕜)) (Work.MotV.fAS 𝕜))
      (Work.MotAS.asY0 D (Work.MotV.fAS 𝕜)) 0 ≠ 0 :=
    Work.MotV5.ASLocal.asRuleQB_asY0_ne_zero D hD (Work.MotV.fAS 𝕜)
  rw [asRuleQW_zero_apply]
  set_option synthInstance.maxHeartbeats 800000 in
  rw [IsScalarTower.algebraMap_apply 𝕜 ↥(Work.MotAS.twistFieldAS D (Work.MotV.fAS 𝕜))
        (RatFunc ↥(Work.MotAS.twistFieldAS D (Work.MotV.fAS 𝕜))) D.a,
      IsScalarTower.algebraMap_apply 𝕜 ↥(Work.MotAS.twistFieldAS D (Work.MotV.fAS 𝕜))
        (RatFunc ↥(Work.MotAS.twistFieldAS D (Work.MotV.fAS 𝕜))) D.b,
      IsScalarTower.algebraMap_apply (RatFunc 𝕜) ↥(Work.MotAS.twistFieldAS D (Work.MotV.fAS 𝕜))
        (RatFunc ↥(Work.MotAS.twistFieldAS D (Work.MotV.fAS 𝕜))) (Work.MotV.fAS 𝕜)]
  rw [← Work.MotAS.map_asRuleQA
        (algebraMap ↥(Work.MotAS.twistFieldAS D (Work.MotV.fAS 𝕜))
          (RatFunc ↥(Work.MotAS.twistFieldAS D (Work.MotV.fAS 𝕜))))
        (algebraMap 𝕜 ↥(Work.MotAS.twistFieldAS D (Work.MotV.fAS 𝕜)) D.a)
        (algebraMap 𝕜 ↥(Work.MotAS.twistFieldAS D (Work.MotV.fAS 𝕜)) D.b)
        (algebraMap (RatFunc 𝕜) ↥(Work.MotAS.twistFieldAS D (Work.MotV.fAS 𝕜)) (Work.MotV.fAS 𝕜))
        (Work.MotAS.asY0 D (Work.MotV.fAS 𝕜)) 0,
      ← Work.MotAS.map_asRuleQB
        (algebraMap ↥(Work.MotAS.twistFieldAS D (Work.MotV.fAS 𝕜))
          (RatFunc ↥(Work.MotAS.twistFieldAS D (Work.MotV.fAS 𝕜))))
        (algebraMap 𝕜 ↥(Work.MotAS.twistFieldAS D (Work.MotV.fAS 𝕜)) D.a)
        (algebraMap 𝕜 ↥(Work.MotAS.twistFieldAS D (Work.MotV.fAS 𝕜)) D.b)
        (algebraMap (RatFunc 𝕜) ↥(Work.MotAS.twistFieldAS D (Work.MotV.fAS 𝕜)) (Work.MotV.fAS 𝕜))
        (Work.MotAS.asY0 D (Work.MotV.fAS 𝕜)) 0]
  exact Work.MotV5.ASLocal.ratFunc_algebraMap_add_X_mul_ne_zero hB

end Work.MotAS
