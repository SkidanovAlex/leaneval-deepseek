import Submission.ZagierHoffmanProof.CarlitzModule

set_option autoImplicit false
set_option maxHeartbeats 1000000

open Polynomial
open scoped BigOperators

/-!
# Regression tests for the Carlitz module action

Concrete instances of `Submission.ZagierHoffmanProof.CarlitzModule` over `F₂ = ZMod 2`.
-/

namespace ZagierHoffmanPositiveChar

section Reg

open PowerSeries

attribute [local instance 100] Classical.decEq

/-- `C_1 = id`. -/
example : carlitzAct (ZMod 2) (1 : (ZMod 2)[X]) (carlitzExp (ZMod 2))
    = PowerSeries.rescale (algebraMap (ZMod 2)[X] (RatFunc (ZMod 2)) 1) (carlitzExp (ZMod 2)) :=
  carlitzAct_exp _ _

/-- `C_θ(e_C) = e_C(θ z)`. -/
example : carlitzAct (ZMod 2) (Polynomial.X : (ZMod 2)[X]) (carlitzExp (ZMod 2))
    = PowerSeries.rescale (((Polynomial.X : (ZMod 2)[X]) : RatFunc (ZMod 2))) (carlitzExp (ZMod 2)) :=
  carlitzAct_exp _ _
example : (((Polynomial.X : (ZMod 2)[X]) : RatFunc (ZMod 2))) = carlitzTheta (ZMod 2) := rfl

/-- `e_C` has no constant term. -/
example : (carlitzExp (ZMod 2)).constantCoeff = 0 := constantCoeff_carlitzExp _

/-- `e_C` is supported on the `q`-powers. -/
example : QpowSparse (ZMod 2) (carlitzExp (ZMod 2)) := qpowSparse_carlitzExp _

/-- ★ The Carlitz action is multiplicative: `C_{ab} = C_a ∘ C_b`. -/
example (a b : (ZMod 2)[X]) :
    carlitzAct (ZMod 2) (a * b) (carlitzExp (ZMod 2))
      = carlitzAct (ZMod 2) a (carlitzAct (ZMod 2) b (carlitzExp (ZMod 2))) :=
  carlitzAct_mul _ a b _

/-- ★ The Carlitz action is additive: `C_{a+b} = C_a + C_b`. -/
example (a b : (ZMod 2)[X]) :
    carlitzAct (ZMod 2) (a + b) (carlitzExp (ZMod 2))
      = carlitzAct (ZMod 2) a (carlitzExp (ZMod 2))
        + carlitzAct (ZMod 2) b (carlitzExp (ZMod 2)) :=
  carlitzAct_add _ a b _

/-- `C_θ` as an `F`-linear endomorphism. -/
example (f : PowerSeries (RatFunc (ZMod 2))) :
    carlitzThetaEnd (ZMod 2) f
      = PowerSeries.C (carlitzTheta (ZMod 2)) * f + f ^ Nat.card (ZMod 2) :=
  carlitzThetaEnd_apply _ f

/-- The Freshman's dream for `q ^ i`-th powers in `F₂(θ)`. -/
example (x y : RatFunc (ZMod 2)) (i : ℕ) :
    (x + y) ^ (Nat.card (ZMod 2) ^ i) = x ^ (Nat.card (ZMod 2) ^ i) + y ^ (Nat.card (ZMod 2) ^ i) :=
  add_pow_card_pow _ x y i

end Reg

end ZagierHoffmanPositiveChar
