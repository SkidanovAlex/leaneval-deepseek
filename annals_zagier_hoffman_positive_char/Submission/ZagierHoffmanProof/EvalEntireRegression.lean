import Submission.ZagierHoffmanProof.EvalEntire
import Submission.ZagierHoffmanProof.SuperOmegaRegression
import Submission.Commons.FieldTheory.RatFunc.charP_completionAtInfty

/-!
# Regression checks: evaluating super-entire series

Concrete instantiations over `K = F(t)_∞`, `θ = X`, `F = ZMod 2`.
-/

set_option autoImplicit false
open Polynomial RatFunc
open scoped WithZero Topology

namespace ZagierHoffmanPositiveChar

attribute [local instance 100] Classical.decEq

attribute [local instance] Commons.FieldTheory.RatFunc.charP_completionAtInfty

noncomputable section

example (a : RatFunc.CompletionAtInfty (ZMod 2)) :
    evalSeries (PowerSeries.C a) (thetaOf (ZMod 2)) = a := evalSeries_C a _

example : evalSeries (PowerSeries.X : PowerSeries (RatFunc.CompletionAtInfty (ZMod 2)))
    (thetaOf (ZMod 2)) = thetaOf (ZMod 2) := evalSeries_X _

example (n : ℕ) : evalSeries (n : PowerSeries (RatFunc.CompletionAtInfty (ZMod 2)))
    (thetaOf (ZMod 2)) = (n : RatFunc.CompletionAtInfty (ZMod 2)) :=
  evalSeries_natCast n _

/-- The evaluation of the period function at the boundary point `θ` exists. -/
example : evalSeries (atOmega 2 (thetaOf (ZMod 2))) (thetaOf (ZMod 2))
    = ∑' n : ℕ, PowerSeries.coeff n (atOmega 2 (thetaOf (ZMod 2)))
        * (thetaOf (ZMod 2)) ^ n := rfl

/-- **Evaluation converts the Frobenius twist into a square** (over `F₂`, so the twist is the
2-power twist). -/
example : evalSeries (frobTwist (R := RatFunc.CompletionAtInfty (ZMod 2)) (p := 2) 1
      (atOmega 2 (thetaOf (ZMod 2)))) ((thetaOf (ZMod 2)) ^ 2)
    = (evalSeries (atOmega 2 (thetaOf (ZMod 2))) (thetaOf (ZMod 2))) ^ 2 :=
  evalSeries_frobTwist 2 (superEntire_atOmega 2 (thetaOf (ZMod 2)) 1 (by norm_num)
    (v_thetaOf (ZMod 2)) (by norm_num)) (thetaOf (ZMod 2)) 1

/-- **Evaluation is multiplicative** (concrete instance over `F₂`). -/
example (a b : RatFunc.CompletionAtInfty (ZMod 2)) :
    evalSeries (PowerSeries.C a * PowerSeries.C b) (thetaOf (ZMod 2)) = a * b := by
  rw [evalSeries_mul (SuperEntire.C a) (SuperEntire.C b) (thetaOf (ZMod 2)),
    evalSeries_C, evalSeries_C]

/-- **Evaluation at `θ` is a ring homomorphism** on `ε` (concrete instance). -/
example (f g : ↥(superEntireSubring (RatFunc.CompletionAtInfty (ZMod 2)))) :
    evalSeriesRingHom (thetaOf (ZMod 2)) (f * g) =
      evalSeriesRingHom (thetaOf (ZMod 2)) f * evalSeriesRingHom (thetaOf (ZMod 2)) g :=
  map_mul _ f g

/-- **`(Ω²)(θ) = Ω(θ)²`** — multiplicativity of evaluation applied to the period function. -/
example : evalSeries (atOmega 2 (thetaOf (ZMod 2)) ^ 2) (thetaOf (ZMod 2))
    = (evalSeries (atOmega 2 (thetaOf (ZMod 2))) (thetaOf (ZMod 2))) ^ 2 :=
  evalSeries_pow (superEntire_atOmega 2 (thetaOf (ZMod 2)) 1 (by norm_num)
    (v_thetaOf (ZMod 2)) (by norm_num)) 2 (thetaOf (ZMod 2))

/-- **Evaluation of a polynomial is polynomial evaluation** (concrete instance over `F₂`). -/
example : evalSeries ((Polynomial.X ^ 2 + Polynomial.C 1 : Polynomial (RatFunc.CompletionAtInfty (ZMod 2))) : PowerSeries _)
    (thetaOf (ZMod 2)) = (thetaOf (ZMod 2)) ^ 2 + 1 := by
  rw [evalSeries_polynomial]
  simp

end

end ZagierHoffmanPositiveChar
