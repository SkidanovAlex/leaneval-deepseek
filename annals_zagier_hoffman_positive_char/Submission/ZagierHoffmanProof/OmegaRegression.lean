import Mathlib.Algebra.Field.ZMod
import Submission.ZagierHoffmanProof.Omega
import Submission.ZagierHoffmanProof.CompletionInstances
import Submission.ZagierHoffmanProof.Valuation
import Submission.Commons.FieldTheory.RatFunc.charP_completionAtInfty

/-!
# Regression checks: the Anderson–Thakur period function `Ω`

Concrete instantiations of the results of `Omega.lean` over `F = ZMod 2` and `F = ZMod 3`,
with `K = F(t)_∞` (the completion of `F(t)` at the place at infinity) and `θ = X`.
-/

set_option autoImplicit false
open Polynomial RatFunc
open scoped WithZero Topology

namespace ZagierHoffmanPositiveChar

attribute [local instance 100] Classical.decEq

noncomputable section

/-- The element `θ = X` of `K = F(t)_∞`. -/
abbrev thetaOf (F : Type*) [Field F] [DecidableEq (RatFunc F)] :
    RatFunc.CompletionAtInfty F := ((X : F[X]) : RatFunc F)

lemma v_thetaOf (F : Type*) [Field F] [DecidableEq (RatFunc F)] :
    Valued.v (thetaOf F) = WithZero.exp 1 := by
  have h := inftyValued_v_polynomial F (X : F[X]) (Polynomial.X_ne_zero (R := F))
  simpa [thetaOf] using h

/-- `Ω` is entire over `F₂`. -/
example : Entire (atOmega 2 (thetaOf (ZMod 2))) :=
  atOmega_entire 2 (thetaOf (ZMod 2)) (v_thetaOf (ZMod 2)) (by norm_num)

/-- `Ω` is entire over `F₃`. -/
example : Entire (atOmega 3 (thetaOf (ZMod 3))) :=
  atOmega_entire 3 (thetaOf (ZMod 3)) (v_thetaOf (ZMod 3)) (by norm_num)

/-- `Ω` has bounded coefficients (it is an element of the Tate algebra) over `F₂`. -/
example : SeriesBounded (atOmega 2 (thetaOf (ZMod 2))) :=
  atOmega_bounded 2 (thetaOf (ZMod 2)) (v_thetaOf (ZMod 2)) (by norm_num)

/-- `Ω` has bounded coefficients over `F₃`. -/
example : SeriesBounded (atOmega 3 (thetaOf (ZMod 3))) :=
  atOmega_bounded 3 (thetaOf (ZMod 3)) (v_thetaOf (ZMod 3)) (by norm_num)

/-- The constant term of `Ω` is `1`, over `F₂`. -/
example : PowerSeries.constantCoeff (atOmega 2 (thetaOf (ZMod 2))) = 1 :=
  constantCoeff_atOmega 2 (thetaOf (ZMod 2))

/-- The constant term of `Ω` is `1`, over `F₃`. -/
example : PowerSeries.constantCoeff (atOmega 3 (thetaOf (ZMod 3))) = 1 :=
  constantCoeff_atOmega 3 (thetaOf (ZMod 3))

/-- The coefficient bound `v (coeff m Ω) ≤ exp (-m)` over `F₂`. -/
example : Valued.v (PowerSeries.coeff 3 (atOmega 2 (thetaOf (ZMod 2))))
    ≤ WithZero.exp (-(3 : ℤ)) :=
  v_coeff_atOmega_le 2 (thetaOf (ZMod 2)) (v_thetaOf (ZMod 2)) (by norm_num) 3

/-- The coefficient bound `v (coeff m Ω) ≤ exp (-m)` over `F₃`. -/
example : Valued.v (PowerSeries.coeff 5 (atOmega 3 (thetaOf (ZMod 3))))
    ≤ WithZero.exp (-(5 : ℤ)) :=
  v_coeff_atOmega_le 3 (thetaOf (ZMod 3)) (v_thetaOf (ZMod 3)) (by norm_num) 5

-- The completion `F(t)_∞` has the same characteristic as `F`, so the `q`-power Frobenius
-- twist is available there.
attribute [local instance] Commons.FieldTheory.RatFunc.charP_completionAtInfty

/-- `Ω` over `F₂` satisfies its functional equation. -/
example : (1 - PowerSeries.C (omX 2 (thetaOf (ZMod 2)) 1) * PowerSeries.X)
      * frobTwist (R := RatFunc.CompletionAtInfty (ZMod 2)) (p := 2) 1
        (atOmega 2 (thetaOf (ZMod 2)))
    = atOmega 2 (thetaOf (ZMod 2)) :=
  atOmega_twist 2 (thetaOf (ZMod 2)) (v_thetaOf (ZMod 2)) (by norm_num)

/-- `Ω` over `F₃` satisfies its functional equation. -/
example : (1 - PowerSeries.C (omX 3 (thetaOf (ZMod 3)) 1) * PowerSeries.X)
      * frobTwist (R := RatFunc.CompletionAtInfty (ZMod 3)) (p := 3) 1
        (atOmega 3 (thetaOf (ZMod 3)))
    = atOmega 3 (thetaOf (ZMod 3)) :=
  atOmega_twist 3 (thetaOf (ZMod 3)) (v_thetaOf (ZMod 3)) (by norm_num)

/-- The general functional equation `Ω = (∏_{i=1}^{N}(1 - t/θ^{q^i})) · Ω^{(N)}` over `F₂`. -/
example (N : ℕ) : atOmega 2 (thetaOf (ZMod 2))
    = omPartial 2 (thetaOf (ZMod 2)) N
      * frobTwist (R := RatFunc.CompletionAtInfty (ZMod 2)) (p := 2) N
        (atOmega 2 (thetaOf (ZMod 2))) :=
  atOmega_eq_omPartial_mul_frobTwist 2 (thetaOf (ZMod 2)) (v_thetaOf (ZMod 2)) (by norm_num) N

/-- The Frobenius recursion for the coefficients of `Ω`, over `F₂`. -/
example : PowerSeries.coeff 4 (atOmega 2 (thetaOf (ZMod 2)))
    = (PowerSeries.coeff 4 (atOmega 2 (thetaOf (ZMod 2)))) ^ 2
      - (PowerSeries.coeff 3 (atOmega 2 (thetaOf (ZMod 2)))) ^ 2
        * omX 2 (thetaOf (ZMod 2)) 1 :=
  coeff_atOmega_frobenius 2 (thetaOf (ZMod 2)) (v_thetaOf (ZMod 2)) (by norm_num) 4

/-- `Ω` is a unit of the power series ring, over `F₂`. -/
example : IsUnit (atOmega 2 (thetaOf (ZMod 2))) :=
  isUnit_atOmega 2 (thetaOf (ZMod 2))

/-- The coefficient of `t` in `Ω` is the negative of the sum of the `θ^{-q^i}`, over `F₂`. -/
example : PowerSeries.coeff 1 (atOmega 2 (thetaOf (ZMod 2)))
    = -∑' N : ℕ, omX 2 (thetaOf (ZMod 2)) (N + 1) :=
  coeff_one_atOmega 2 (thetaOf (ZMod 2)) (v_thetaOf (ZMod 2)) (by norm_num)

/-- The partial products converge to `Ω`, coefficientwise, over `F₂`. -/
example : Filter.Tendsto
    (fun N => PowerSeries.coeff 2 (omPartial 2 (thetaOf (ZMod 2)) N)) Filter.atTop
      (𝓝 (omCoeff 2 (thetaOf (ZMod 2)) 2)) :=
  tendsto_coeff_omPartial 2 (thetaOf (ZMod 2)) (v_thetaOf (ZMod 2)) (by norm_num) 2

/-- The uniform coefficient bound for the partial products, over `F₃`. -/
example (N m : ℕ) :
    Valued.v (PowerSeries.coeff m (omPartial 3 (thetaOf (ZMod 3)) N))
      ≤ WithZero.exp (-(m : ℤ)) :=
  v_coeff_omPartial_le 3 (thetaOf (ZMod 3)) (v_thetaOf (ZMod 3)) (by norm_num) N m

/-- The valuation of `x_i = θ^{-q^i}` over `F₂`. -/
example (i : ℕ) : Valued.v (omX 2 (thetaOf (ZMod 2)) i) = WithZero.exp (-((2 ^ i : ℕ) : ℤ)) :=
  v_omX 2 (thetaOf (ZMod 2)) (v_thetaOf (ZMod 2)) i

/-- `Ω ∈ T^×`: `Ω` is a unit of the Tate algebra over `F₂`. -/
example : IsUnit (atOmegaTate 2 (thetaOf (ZMod 2)) (v_thetaOf (ZMod 2)) (by norm_num)) :=
  isUnit_atOmegaTate 2 (thetaOf (ZMod 2)) (v_thetaOf (ZMod 2)) (by norm_num)

/-- `Ω` is a unit of the Tate algebra over `F₃`. -/
example : IsUnit (atOmegaTate 3 (thetaOf (ZMod 3)) (v_thetaOf (ZMod 3)) (by norm_num)) :=
  isUnit_atOmegaTate 3 (thetaOf (ZMod 3)) (v_thetaOf (ZMod 3)) (by norm_num)

/-- The coefficients of the inverse of `Ω` are bounded, over `F₂`. -/
example : SeriesBounded (PowerSeries.mk (omInvCoeff 2 (thetaOf (ZMod 2)))) :=
  omInvCoeff_bounded 2 (thetaOf (ZMod 2)) (v_thetaOf (ZMod 2)) (by norm_num)

/-- `Ω * Ω⁻¹ = 1`, over `F₂`. -/
example : atOmega 2 (thetaOf (ZMod 2)) * PowerSeries.mk (omInvCoeff 2 (thetaOf (ZMod 2))) = 1 :=
  atOmega_mul_omInvCoeff 2 (thetaOf (ZMod 2))

/-- The coefficient recursion of the inverse of `Ω`, over `F₂`. -/
example (m : ℕ) : omInvCoeff 2 (thetaOf (ZMod 2)) (m + 1)
    = -∑ k ∈ Finset.range (m + 1),
        PowerSeries.coeff (k + 1) (atOmega 2 (thetaOf (ZMod 2)))
          * omInvCoeff 2 (thetaOf (ZMod 2)) (m - k) :=
  omInvCoeff_succ 2 (thetaOf (ZMod 2)) m

/-- The sharp coefficient bound for the powers of `Ω`, over `F₂`. -/
example (s n : ℕ) (hn : 1 ≤ n) :
    Valued.v (PowerSeries.coeff n (atOmega 2 (thetaOf (ZMod 2)) ^ s))
      ≤ WithZero.exp (-1) :=
  v_coeff_pow_atOmega_le 2 (thetaOf (ZMod 2)) (v_thetaOf (ZMod 2)) (by norm_num) s n hn

/-- The constant term of a power of `Ω` is `1`, over `F₃`. -/
example (s : ℕ) : PowerSeries.coeff 0 (atOmega 3 (thetaOf (ZMod 3)) ^ s) = 1 :=
  coeff_zero_pow_atOmega 3 (thetaOf (ZMod 3)) s

/-- The coefficient bound for `Q * Ω^s` for a bounded `Q`, over `F₂`. -/
example (s n : ℕ) (hn : 1 ≤ n) :
    Valued.v (PowerSeries.coeff n
        (((PowerSeries.X : PowerSeries (RatFunc.CompletionAtInfty (ZMod 2))) ^ 3)
          * atOmega 2 (thetaOf (ZMod 2)) ^ s)) ≤ WithZero.exp 0 :=
  v_coeff_mul_pow_atOmega_le 2 (thetaOf (ZMod 2)) (v_thetaOf (ZMod 2)) (by norm_num)
    ((PowerSeries.X : PowerSeries (RatFunc.CompletionAtInfty (ZMod 2))) ^ 3) 0 (fun n => by
      rw [PowerSeries.coeff_X_pow]
      by_cases h : n = 3
      · rw [if_pos h, map_one, WithZero.exp_zero]
      · rw [if_neg h, map_zero]
        exact bot_le) s n hn

/-- The Frobenius twist of `Q * Ω^s` is bounded (the shape of the `L`-series terms), over `F₂`. -/
example (s i : ℕ) : SeriesBounded (frobTwist (R := RatFunc.CompletionAtInfty (ZMod 2)) (p := 2) i
    ((PowerSeries.X : PowerSeries (RatFunc.CompletionAtInfty (ZMod 2))) ^ 3
      * atOmega 2 (thetaOf (ZMod 2)) ^ s)) :=
  frobTwist_mul_pow_atOmega_bounded 2 (thetaOf (ZMod 2)) (v_thetaOf (ZMod 2)) (by norm_num)
    ((PowerSeries.X : PowerSeries (RatFunc.CompletionAtInfty (ZMod 2))) ^ 3) ⟨0, fun n => by
      rw [PowerSeries.coeff_X_pow]
      by_cases h : n = 3
      · rw [if_pos h, map_one, WithZero.exp_zero]
      · rw [if_neg h, map_zero]
        exact bot_le⟩ s i

end

end ZagierHoffmanPositiveChar
