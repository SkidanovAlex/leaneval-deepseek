import Mathlib.Algebra.Field.ZMod
import Submission.ZagierHoffmanProof.SuperOmega
import Submission.ZagierHoffmanProof.OmegaRegression

/-!
# Regression checks: `Ω ∈ ε` over `K∞` and over `F((y))`

The sharp coefficient bound `v (coeff m Ω) ≤ exp (-(d q + ⋯ + d q^m))`, super-entireness of `Ω`
over `F = ZMod 2`, `ZMod 3` (with `K = F(t)_∞`, `θ = X`, `d = 1`), and the concrete Kummer-field
instances from `SuperPeriod` (imported separately).
-/

set_option autoImplicit false
open Polynomial RatFunc
open scoped WithZero Topology

namespace ZagierHoffmanPositiveChar

attribute [local instance 100] Classical.decEq

noncomputable section

/-- The sharp bound over `F₂`: `v (coeff 4 Ω) ≤ exp (-(2 + 4 + 8 + 16))`. -/
example : Valued.v (PowerSeries.coeff 4 (atOmega 2 (thetaOf (ZMod 2))))
    ≤ WithZero.exp (-(2 + 4 + 8 + 16 : ℤ)) := by
  have h := v_coeff_atOmega_le_sharp 2 (thetaOf (ZMod 2)) 1 (by norm_num) (v_thetaOf (ZMod 2))
    (by norm_num) 4
  have hexp : sharpExp 1 2 4 = (2 + 4 + 8 + 16 : ℤ) := by
    norm_num [sharpExp, Finset.sum_range_succ]
  simpa [hexp] using h

/-- The sharp bound over `F₃`: `v (coeff 3 Ω) ≤ exp (-(3 + 9 + 27))`. -/
example : Valued.v (PowerSeries.coeff 3 (atOmega 3 (thetaOf (ZMod 3))))
    ≤ WithZero.exp (-(3 + 9 + 27 : ℤ)) := by
  have h := v_coeff_atOmega_le_sharp 3 (thetaOf (ZMod 3)) 1 (by norm_num) (v_thetaOf (ZMod 3))
    (by norm_num) 3
  have hexp : sharpExp 1 3 3 = (3 + 9 + 27 : ℤ) := by
    norm_num [sharpExp, Finset.sum_range_succ]
  simpa [hexp] using h

/-- **`Ω ∈ ε` over `F₂`.** -/
example : SuperEntire (atOmega 2 (thetaOf (ZMod 2))) :=
  superEntire_atOmega 2 (thetaOf (ZMod 2)) 1 (by norm_num) (v_thetaOf (ZMod 2)) (by norm_num)

/-- **`Ω ∈ ε` over `F₃`.** -/
example : SuperEntire (atOmega 3 (thetaOf (ZMod 3))) :=
  superEntire_atOmega 3 (thetaOf (ZMod 3)) 1 (by norm_num) (v_thetaOf (ZMod 3)) (by norm_num)

/-- `ε` is a *proper* subring of the Tate algebra: the geometric series is a Tate series but not
super-entire. -/
example : ¬ SuperEntire (PowerSeries.mk fun _ : ℕ => (1 : RatFunc.CompletionAtInfty (ZMod 2))) :=
  not_superEntire_mk_one

example : SeriesBounded (PowerSeries.mk fun _ : ℕ => (1 : RatFunc.CompletionAtInfty (ZMod 2))) :=
  seriesBounded_mk_one

example : ∃ f : PowerSeries (RatFunc.CompletionAtInfty (ZMod 2)),
    SeriesBounded f ∧ ¬ SuperEntire f := exists_tate_not_superEntire

/-- Super-entireness is inherited by the powers of `Ω`, as needed for the `L`-series. -/
example : SuperEntire (atOmega 2 (thetaOf (ZMod 2)) ^ 3) :=
  (superEntire_atOmega 2 (thetaOf (ZMod 2)) 1 (by norm_num) (v_thetaOf (ZMod 2))
    (by norm_num)).pow 3

end

end ZagierHoffmanPositiveChar
