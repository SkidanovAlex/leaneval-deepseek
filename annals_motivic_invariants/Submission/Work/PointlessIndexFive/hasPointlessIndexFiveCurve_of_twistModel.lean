import Mathlib
import Submission.Work.PointlessIndexFive.Defs

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option linter.style.haveILetI false

namespace Work.PointlessIndexFive

/-- **The main reduction.**  A curve model realizing a pointless quintic twist is a
`PointlessIndexFiveCurve`.  The geometric fields (`Variety`, `IsProper`, `Smooth`,
`GeometricallyIntegral`, `dim_eq_one`) are transported verbatim; `no_point` is the bridge
`hasPoint_iff` composed with the non-vanishing of the class; `five` is the orbit-divisor statement
`5 • cls = 0`; and `dvd` is the fact that the class has exact additive order `5`. -/
theorem hasPointlessIndexFiveCurve_of_twistModel {𝕜 : Type} [Field 𝕜] [DecidableEq 𝕜]
    (D : QuinticTwist 𝕜) (M : TwistCurveModel D) (h : D.Pointless) :
    HasPointlessIndexFiveCurve 𝕜 := by
  refine ⟨{ C := M.C
            variety := M.variety
            isProper := M.isProper
            isSmooth := M.isSmooth
            isGeomIntegral := M.isGeomIntegral
            dim_eq_one := M.dim_eq_one
            no_point := ?_
            five := ?_
            dvd := ?_ }⟩
  · -- `C(𝕜) = ∅`: `hasPoint_iff` transports rational points to `cls = 0`.
    intro hp
    exact h (ofAdd_eq_one.mp (M.hasPoint_iff.mp hp))
  · -- the orbit divisor: `5 • cls = 0` (`five_smul_cls`).
    refine (M.divisorOfDegree_iff 5).mpr ?_
    show (Multiplicative.ofAdd D.cls) ^ (5 : ℕ) = 1
    rw [← ofAdd_nsmul, ofAdd_eq_one]
    exact Work.TorsorExistence.five_smul_cls D
  · -- the index: the class has exact additive order `5`.
    intro n hn
    have hn' : n • D.cls = 0 := by
      have h1 : (Multiplicative.ofAdd D.cls) ^ n = 1 := (M.divisorOfDegree_iff n).mp hn
      rwa [← ofAdd_nsmul, ofAdd_eq_one] at h1
    haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    have hao : addOrderOf D.cls = 5 :=
      addOrderOf_eq_prime (Work.TorsorExistence.five_smul_cls D) h
    rw [← hao]
    exact addOrderOf_dvd_iff_nsmul_eq_zero.mpr hn'

end Work.PointlessIndexFive
