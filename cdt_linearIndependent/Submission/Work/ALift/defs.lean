import Mathlib
import Submission.CDTPlan.InterfacesA2
import Submission.CDT.EichlerInput

/-!
# Area ALift — continuation of `H` along a lift of `φ_A`: definitions

Under the absurd relation `ARel a b c` the series `H = a H_A + b H_B + c H_C` overconverges to
radius `1` (`Submission.CDT.functionsH_overconverges`), and it satisfies Zagier's order-2 operator
with polynomial coefficients and inhomogeneity `b + c/(1-x)`:

`P·H'' + Q·H' + R·H = b + c/(1-x)`,  `P = x(1-x)(1-9x)`, `Q = 1 - 20x + 27x²`, `R = -3 + 9x`

(`Submission.CDT.HA_odeLHS`).  Since `H` extends to `|x| < 1` it can be evaluated at any point
`q` with `‖q‖ < 1`; the analytic functions `U₀, U₁, U₂` below are the evaluation of `H` and its two
formal derivatives.

Pulling the first-order system `(u,u')' = M(x)(u,u') + v(x)` back along a lift `Φ` of `φ_A`
(`Φ z + Φ(-z) = Φ z · Φ(-z) = phiA (z²)`) gives the system `sysA, sysb` used by
`OdeContinuation`; `Y0v` is the initial solution `(U₀(Φ z), U₁(Φ z))` on a small disc.
-/

open PowerSeries Metric
open Submission.CDTPlan
open scoped BigOperators

namespace Work.ALift

noncomputable section

/-- The complex coefficients of `H = a·H_A + b·H_B + c·H_C`. -/
def hcoef (a b c : ℤ) (k : ℕ) : ℂ := ((PowerSeries.coeff k (HZ a b c) : ℚ) : ℂ)

/-- `U₀(q) = Σ_k h_k q^k`, the analytic function defined by `H` near `0`. -/
def HU0 (a b c : ℤ) (q : ℂ) : ℂ := ∑' k : ℕ, hcoef a b c k * q ^ k

/-- `U₁`: the evaluation of the derivative series of `H`. -/
def HU1 (a b c : ℤ) (q : ℂ) : ℂ :=
  ∑' k : ℕ, ((k : ℂ) + 1) * hcoef a b c (k + 1) * q ^ k

/-- `U₂`: the evaluation of the second derivative series of `H`. -/
def HU2 (a b c : ℤ) (q : ℂ) : ℂ :=
  ∑' k : ℕ, ((k : ℂ) + 1) * ((k : ℂ) + 2) * hcoef a b c (k + 2) * q ^ k

/-- `P(x) = x(1-x)(1-9x)`, the leading coefficient of Zagier's operator. -/
def Pd (x : ℂ) : ℂ := x * (1 - x) * (1 - 9 * x)

/-- `Q(x) = 1 - 20x + 27x²`, the derivative coefficient of Zagier's operator. -/
def Qd (x : ℂ) : ℂ := 1 - 20 * x + 27 * x ^ 2

/-- `R(x) = -3 + 9x`, the zeroth-order coefficient of Zagier's operator. -/
def Rd (x : ℂ) : ℂ := -3 + 9 * x

/-- The inhomogeneity `b + c/(1-x)` of the Zagier operator for `H = aH_A + bH_B + cH_C`. -/
def rhsA (b c : ℤ) (x : ℂ) : ℂ := (b : ℂ) + (c : ℂ) / (1 - x)

/-- The inner radius `r₀ = 1/31`: the annulus `r₀ < ‖z‖ < 1` contains no preimage of the
singular points `0, 1/9, 1` of the operator other than the excluded `z = 0`. -/
def rA0 : ℝ := 1 / 31

/-- The radius `r₁ = 1/25` of the disc on which the initial solution `Y0v` is defined. -/
def rA1 : ℝ := 1 / 25

/-- The matrix of the first-order system `(u,u')' = M(x)·(u,u') + v(x)` for the Zagier operator,
pulled back along `Φ`: `sysA Φ z = (deriv Φ z) • M(Φ z)`. -/
def sysA (Φ : ℂ → ℂ) (z : ℂ) : Fin 2 → Fin 2 → ℂ := fun i j =>
  deriv Φ z *
    (if i = 0 then (if j = 0 then 0 else 1)
      else (if j = 0 then -Rd (Φ z) / Pd (Φ z) else -Qd (Φ z) / Pd (Φ z)))

/-- The inhomogeneity of the pulled-back system: `sysb Φ z = (deriv Φ z) • v(Φ z)`. -/
def sysb (b c : ℤ) (Φ : ℂ → ℂ) (z : ℂ) : Fin 2 → ℂ := fun i =>
  deriv Φ z * (if i = 0 then 0 else rhsA b c (Φ z) / Pd (Φ z))

/-- `Y₀ = (U₀, U₁) ∘ Φ`, the initial solution of the pulled-back system on the disc `‖z‖ < r₁`. -/
def Y0v (a b c : ℤ) (Φ : ℂ → ℂ) (z : ℂ) : Fin 2 → ℂ := fun i =>
  if i = 0 then HU0 a b c (Φ z) else HU1 a b c (Φ z)

/-! ## The two radii -/

lemma rA0_eq : rA0 = 1 / 31 := rfl
lemma rA1_eq : rA1 = 1 / 25 := rfl
lemma rA0_pos : 0 < rA0 := by norm_num [rA0]
lemma rA0_lt_rA1 : rA0 < rA1 := by norm_num [rA0, rA1]
lemma rA1_pos : 0 < rA1 := by norm_num [rA1]
lemma rA1_le_one : rA1 ≤ 1 := by norm_num [rA1]

/-! ## The entries of the pulled-back system -/

lemma sysA_00 (Φ : ℂ → ℂ) (z : ℂ) : sysA Φ z 0 0 = 0 := by
  unfold sysA
  rw [if_pos rfl, if_pos rfl, mul_zero]

lemma sysA_01 (Φ : ℂ → ℂ) (z : ℂ) : sysA Φ z 0 1 = deriv Φ z := by
  unfold sysA
  rw [if_pos rfl, if_neg (by decide : ¬ ((1 : Fin 2) = 0)), mul_one]

lemma sysA_10 (Φ : ℂ → ℂ) (z : ℂ) :
    sysA Φ z 1 0 = deriv Φ z * (-Rd (Φ z) / Pd (Φ z)) := by
  unfold sysA
  rw [if_neg (by decide : ¬ ((1 : Fin 2) = 0)), if_pos rfl]

lemma sysA_11 (Φ : ℂ → ℂ) (z : ℂ) :
    sysA Φ z 1 1 = deriv Φ z * (-Qd (Φ z) / Pd (Φ z)) := by
  unfold sysA
  rw [if_neg (by decide : ¬ ((1 : Fin 2) = 0)),
    if_neg (by decide : ¬ ((1 : Fin 2) = 0))]

lemma sysb_0 (b c : ℤ) (Φ : ℂ → ℂ) (z : ℂ) : sysb b c Φ z 0 = 0 := by
  unfold sysb
  rw [if_pos rfl, mul_zero]

lemma sysb_1 (b c : ℤ) (Φ : ℂ → ℂ) (z : ℂ) :
    sysb b c Φ z 1 = deriv Φ z * (rhsA b c (Φ z) / Pd (Φ z)) := by
  unfold sysb
  rw [if_neg (by decide : ¬ ((1 : Fin 2) = 0))]

lemma Y0v_0 (a b c : ℤ) (Φ : ℂ → ℂ) (z : ℂ) : Y0v a b c Φ z 0 = HU0 a b c (Φ z) := by
  unfold Y0v
  rw [if_pos rfl]

lemma Y0v_1 (a b c : ℤ) (Φ : ℂ → ℂ) (z : ℂ) : Y0v a b c Φ z 1 = HU1 a b c (Φ z) := by
  unfold Y0v
  rw [if_neg (by decide : ¬ ((1 : Fin 2) = 0))]

end

end Work.ALift
