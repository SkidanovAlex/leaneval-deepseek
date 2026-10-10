import Mathlib
import Submission.Work.MotAS.ChartDefs
import Submission.Work.MotK.RuleData
import Submission.Work.MotAS.TwistField
import Submission.Work.MotAS.twistFieldAS_eq
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.MotAS.ASRulDefs` — the ruling data of the AS target divisor

The target ruling divisor of the Artin–Schreier (characteristic-`5`) Crauder–Katz link is the
quintic `sdualAS a b g = kleinSecDualAS a b g (chart3)` of `Submission.Work.MotAS.ChartDefs`.
Its ruling lines are obtained exactly as in the split (`Work.MotK.RuleData`) and T-twisted
(`Work.MotK.TwRule`) cases:

* `q^AS = kleinPAS0` is the (first) AS Pfaffian quadric;
* `asTan a b g c k = b_{q}(c, e_k) e_0 − b_q(c, e_0) e_k` is the tangent vector of `{q^AS = 0}`
  at `c` (`b_q` = polar form `kleinBilinAS0`);
* `asRuleA = dP^AS_c(asTan(·,1))`, `asRuleB = dP^AS_c(asTan(·,2))` are the two ruling vectors,
  where `dP^AS` is the polarisation `asPolarP` of the AS Pfaffian map `kleinPAS`;
* `asRulePt a b g c l m = l·asRuleA(c) + m·asRuleB(c)` is a point of the ruling line.

The zeroth component of `asRuleA` is `b_q(c,e_0)b_q(c,e_1) − b_q(c,e_1)b_q(c,e_0) = 0` because the
polarisation is of the *same* quadric `kleinPAS0` that defines the tangent vector; hence the ruling
lines lie in the hyperplane `{z₀ = 0}` of the affine chart `chart3 = (0, X₀, X₁, X₂, 1)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000

namespace Work.MotAS

open MvPolynomial

variable {R : Type*} [CommRing R]

/-- The polar form of the AS quadric `kleinPAS0` (the quadric of the AS ruling). -/
def kleinBilinAS0 (a b g : R) (u v : Fin 5 → R) : R :=
  kleinPAS0 a b g (u + v) - kleinPAS0 a b g u - kleinPAS0 a b g v

/-- The tangent vector of the AS quadric `kleinPAS0` at `c` in the `k`-th direction. -/
def asTan (a b g : R) (c : Fin 5 → R) (k : Fin 5) : Fin 5 → R :=
  fun i => kleinBilinAS0 a b g c (Work.MotK.kleinE k) * Work.MotK.kleinE 0 i
    - kleinBilinAS0 a b g c (Work.MotK.kleinE 0) * Work.MotK.kleinE k i

/-- The polarisation of the AS Pfaffian map `kleinPAS` in the direction `u`. -/
def asPolarP (a b g : R) (c u : Fin 5 → R) : Fin 5 → R :=
  fun i => kleinPAS a b g (c + u) i - kleinPAS a b g c i - kleinPAS a b g u i

/-- The first AS ruling vector `A(c) = dP^AS_c(u₁)`. -/
def asRuleA (a b g : R) (c : Fin 5 → R) : Fin 5 → R :=
  asPolarP a b g c (asTan a b g c 1)

/-- The second AS ruling vector `B(c) = dP^AS_c(u₂)`. -/
def asRuleB (a b g : R) (c : Fin 5 → R) : Fin 5 → R :=
  asPolarP a b g c (asTan a b g c 2)

/-- A point of the AS ruling line over the curve point `c`. -/
def asRulePt (a b g : R) (c : Fin 5 → R) (l m : R) : Fin 5 → R :=
  fun i => l * asRuleA a b g c i + m * asRuleB a b g c i

theorem asRulePt_apply (a b g : R) (c : Fin 5 → R) (l m : R) (i : Fin 5) :
    asRulePt a b g c l m i = l * asRuleA a b g c i + m * asRuleB a b g c i := rfl

/-- `kleinPAS` at component `0` is the quadric `kleinPAS0`. -/
theorem kleinPAS_apply_zero (a b g : R) (y : Fin 5 → R) : kleinPAS a b g y 0 = kleinPAS0 a b g y := by
  simp only [kleinPAS, Matrix.cons_val_zero]

/-- Linear-in-the-second-argument form of the polar form of `kleinPAS0`. -/
theorem kleinBilinAS0_lin (a b g : R) (c : Fin 5 → R) (x y : R) (u v : Fin 5 → R) :
    kleinBilinAS0 a b g c (x • u + y • v)
      = x * kleinBilinAS0 a b g c u + y * kleinBilinAS0 a b g c v := by
  simp only [kleinBilinAS0, kleinPAS0, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  first | refl_ring1 | ring

/-- The tangent vector written as a linear combination of two basis vectors. -/
theorem asTan_eq (a b g : R) (c : Fin 5 → R) (k : Fin 5) :
    asTan a b g c k
      = kleinBilinAS0 a b g c (Work.MotK.kleinE k) • Work.MotK.kleinE 0
        + (-(kleinBilinAS0 a b g c (Work.MotK.kleinE 0))) • Work.MotK.kleinE k := by
  funext i
  simp only [asTan, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Work.MotK.kleinE,
    Pi.single_apply]
  first | refl_ring1 | ring

/-- **The AS ruling lines lie in the hyperplane `{z₀ = 0}`.**  The zeroth component of the first
ruling vector is `b_q(c,e₀)b_q(c,e₁) − b_q(c,e₁)b_q(c,e₀) = 0`. -/
theorem asRuleA_zero (a b g : R) (c : Fin 5 → R) : asRuleA a b g c 0 = 0 := by
  have h0 : asRuleA a b g c 0
      = kleinBilinAS0 a b g c (asTan a b g c 1) := by
    simp only [asRuleA, asPolarP, kleinPAS_apply_zero, kleinBilinAS0]
  rw [h0, asTan_eq, kleinBilinAS0_lin]
  first | refl_ring1 | ring

/-- **The AS ruling lines lie in the hyperplane `{z₀ = 0}`** (second ruling vector). -/
theorem asRuleB_zero (a b g : R) (c : Fin 5 → R) : asRuleB a b g c 0 = 0 := by
  have h0 : asRuleB a b g c 0
      = kleinBilinAS0 a b g c (asTan a b g c 2) := by
    simp only [asRuleB, asPolarP, kleinPAS_apply_zero, kleinBilinAS0]
  rw [h0, asTan_eq, kleinBilinAS0_lin]
  first | refl_ring1 | ring

/-- A point of the AS ruling line has vanishing zeroth coordinate. -/
theorem asRulePt_zero (a b g : R) (c : Fin 5 → R) (l m : R) : asRulePt a b g c l m 0 = 0 := by
  rw [asRulePt_apply, asRuleA_zero, asRuleB_zero, mul_zero, mul_zero, add_zero]

end Work.MotAS
