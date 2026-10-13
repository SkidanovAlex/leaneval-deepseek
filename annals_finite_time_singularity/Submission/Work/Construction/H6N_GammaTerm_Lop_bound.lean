/-
# The `D_θ`-iterate bound for `ψ = c2m·Γ`, to order `6`

This file proves

`Work.Construction.H6N_GammaTerm_Lop_bound`: there is a universal `D > 0` with

`|D_θ^i ψ(θ)| ≤ D·Γ(θ)·(sin²(2θ) + α)`  for `0 < α ≤ 1`, `1 ≤ i ≤ 6`, `θ ∈ (0,π/2)`,

where `ψ = c2m·Γ` is the angular factor of the `Γ`-term (`D_θ = Lop = sin(2θ)∂_θ`).
It extends the companion module `H4N_GammaTerm_Lop_bound.lean` (orders `1 ≤ i ≤ 4`) to the
orders `5` and `6` needed for the `ℋ⁶`-bound on the `Γ`-term.

The mechanism is the one of the companion module.  On the open quadrant, writing
`x = cos²θ`, the operator acts on functions of the form `θ ↦ a(cos²θ)` as

* `Lop (Γ · a(cos²·)) = Γ · ( -4x(1-x)·a'(x) + (α/3)(6x-4)·a(x) )`  (`glop_step`),

so that with `A₀ = c2m = 3x-2` and the recurrence
`Aᵢ₊₁ = -4x(1-x)Aᵢ' + (α/3)(6x-4)Aᵢ` one has `D_θ^i ψ = Γ(θ)·Aᵢ(cos²θ, α)`.

This file

* defines `A₅`, `A₆` by the recurrence (so that the two new iterate identities are
  definitional, see `Lop_iter_psiA5`, `Lop_iter_psiA6`);
* records the explicit polynomial `D₄ = ∂ₓA₄` (`deriv_Aang_four`) and the explicit
  expansion of `A₅` in powers of `x` with coefficients polynomial in `α/3`
  (`Aang5_eq_mono`);
* bounds `|A₅| ≤ 24325808(α + 4x(1-x))`, `|∂ₓA₅| ≤ 196578816` and
  `|A₆| ≤ 245230432(α + 4x(1-x))` on `[0,1]` by summing the absolute values of the
  coefficients of the explicit polynomials (the factors `(α/3)^k`, `x^j` are `≤ 1` there);
* concludes with `D = 10^9`.

The coefficients of the explicit polynomials were computed from
`Aᵢ₊₁ = -4x(1-x)Aᵢ' + (α/3)(6x-4)Aᵢ`; the tables `ac4`, `dq4`, `cc5` below list them
(the graded pieces of `A₄`, `∂ₓA₄` and `A₅` in powers of `α/3`).
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.IntervalCases
import Submission.Work.Construction.GammaTermAux
import Submission.Work.Construction.GLop_Aux
import Submission.Work.Construction.H4N_GammaTerm_Lop_bound
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open Filter

namespace Work.Construction

set_option autoImplicit false

set_option maxHeartbeats 1000000

/-! ## Two general tools -/

/-- The derivative of a monomial sum, in shifted form. -/
theorem deriv_mono_succ (k : ℕ) (a : ℕ → ℝ) (x : ℝ) :
    deriv (fun y : ℝ => ∑ j ∈ Finset.range (k+1), a j * y ^ j) x
      = ∑ j ∈ Finset.range k, ((j : ℝ) + 1) * a (j+1) * x ^ j := by
  have hfun : (fun y : ℝ => ∑ j ∈ Finset.range (k+1), a j * y ^ j)
      = fun y : ℝ => a 0 + ∑ j ∈ Finset.range k, a (j+1) * y ^ (j+1) := by
    funext y
    rw [Finset.sum_range_succ']
    ring
  rw [hfun, deriv_const_add (a 0)]
  rw [show (fun y : ℝ => ∑ j ∈ Finset.range k, a (j+1) * y ^ (j+1))
      = (∑ j ∈ Finset.range k, fun y : ℝ => a (j+1) * y ^ (j+1)) from by
    funext y; rw [Finset.sum_apply]]
  rw [deriv_sum (fun j hj => by fun_prop)]
  apply Finset.sum_congr rfl
  intro j hj
  rw [((hasDerivAt_pow (j+1) x).const_mul (a (j+1))).deriv, Nat.add_sub_cancel]
  push_cast
  ring

/-- A monomial sum in the variable `r ∈ [0,1]` is bounded by the sum of the absolute
values of its coefficients. -/
theorem abs_sum_mul_pow_le (n : ℕ) (r : ℝ) (b : ℕ → ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    |∑ k ∈ Finset.range n, b k * r ^ k| ≤ ∑ k ∈ Finset.range n, |b k| := by
  calc |∑ k ∈ Finset.range n, b k * r ^ k| ≤ ∑ k ∈ Finset.range n, |b k * r ^ k| :=
        Finset.abs_sum_le_sum_abs _ _
    _ = ∑ k ∈ Finset.range n, |b k| * r ^ k := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [abs_mul, abs_of_nonneg (pow_nonneg hr0 k)]
    _ ≤ ∑ k ∈ Finset.range n, |b k| := by
        apply Finset.sum_le_sum
        intro k hk
        exact mul_le_of_le_one_right (abs_nonneg (b k)) (pow_le_one₀ hr0 hr1)

/-! ## The coefficient tables -/

/-- The `x`-coefficients of the powers of `α/3` in `A₄`:
`A₄ = ∑ k (α/3)^k ∑ j ac4 k j x^j`. -/
def ac4 : ℕ → ℕ → ℝ
  | 0, 0 => 0 | 0, 1 => 768 | 0, 2 => -11520 | 0, 3 => 38400 | 0, 4 => -46080 | 0, 5 => 18432
  | 1, 0 => 0 | 1, 1 => 3840 | 1, 2 => -44160 | 1, 3 => 132480 | 1, 4 => -149760 | 1, 5 => 57600
  | 2, 0 => 0 | 2, 1 => 7680 | 2, 2 => -63360 | 2, 3 => 162240 | 2, 4 => -167040 | 2, 5 => 60480
  | 3, 0 => 0 | 3, 1 => 7680 | 3, 2 => -42240 | 3, 3 => 86400 | 3, 4 => -77760 | 3, 5 => 25920
  | 4, 0 => -512 | 4, 1 => 3840 | 4, 2 => -11520 | 4, 3 => 17280 | 4, 4 => -12960 | 4, 5 => 3888
  | _, _ => 0

/-- The `x`-coefficients of the powers of `α/3` in `D₄ = ∂ₓA₄`:
`D₄ = ∑ k (α/3)^k ∑ j dq4 k j x^j`. -/
def dq4 : ℕ → ℕ → ℝ
  | 0, 0 => 768 | 0, 1 => -23040 | 0, 2 => 115200 | 0, 3 => -184320 | 0, 4 => 92160
  | 1, 0 => 3840 | 1, 1 => -88320 | 1, 2 => 397440 | 1, 3 => -599040 | 1, 4 => 288000
  | 2, 0 => 7680 | 2, 1 => -126720 | 2, 2 => 486720 | 2, 3 => -668160 | 2, 4 => 302400
  | 3, 0 => 7680 | 3, 1 => -84480 | 3, 2 => 259200 | 3, 3 => -311040 | 3, 4 => 129600
  | 4, 0 => 3840 | 4, 1 => -23040 | 4, 2 => 51840 | 4, 3 => -51840 | 4, 4 => 19440
  | _, _ => 0

/-- The `x`-coefficients of the powers of `α/3` in `A₅`:
`A₅ = ∑ k (α/3)^k ∑ j cc5 k j x^j`. -/
def cc5 : ℕ → ℕ → ℝ
  | 0, 0 => 0 | 0, 1 => -3072 | 0, 2 => 95232 | 0, 3 => -552960 | 0, 4 => 1198080
  | 0, 5 => -1105920 | 0, 6 => 368640
  | 1, 0 => 0 | 1, 1 => -18432 | 1, 2 => 419328 | 1, 3 => -2165760 | 1, 4 => 4400640
  | 1, 5 => -3898368 | 1, 6 => 1262592
  | 2, 0 => 0 | 2, 1 => -46080 | 2, 2 => 737280 | 2, 3 => -3248640 | 2, 4 => 6013440
  | 2, 5 => -5011200 | 2, 6 => 1555200
  | 3, 0 => 0 | 3, 1 => -61440 | 3, 2 => 668160 | 3, 3 => -2403840 | 3, 4 => 3922560
  | 3, 5 => -3006720 | 3, 6 => 881280
  | 4, 0 => 0 | 4, 1 => -46080 | 4, 2 => 322560 | 4, 3 => -898560 | 4, 4 => 1244160
  | 4, 5 => -855360 | 4, 6 => 233280
  | 5, 0 => 2048 | 5, 1 => -18432 | 5, 2 => 69120 | 5, 3 => -138240 | 5, 4 => 155520
  | 5, 5 => -93312 | 5, 6 => 23328
  | _, _ => 0

/-- The mono coefficients of `A₄`: `A₄ = ∑ j a4 j α · x^j`. -/
def a4 (j : ℕ) (α : ℝ) : ℝ := ∑ k ∈ Finset.range 5, ac4 k j * (α/3)^k

/-- The explicit polynomial `D₄ = ∂ₓA₄`. -/
def D4p (x α : ℝ) : ℝ := ∑ k ∈ Finset.range 5, (∑ j ∈ Finset.range 5, dq4 k j * x^j) * (α/3)^k

/-- The mono coefficients of `A₅`: `A₅ = ∑ j c5 j α · x^j`. -/
def c5 (j : ℕ) (α : ℝ) : ℝ := ∑ k ∈ Finset.range 6, cc5 k j * (α/3)^k

/-- The fifth angular polynomial: the result of one more application of the operator
`-4x(1-x)∂ₓ + (α/3)(6x-4)` to `A₄`. -/
def Aang5 (x α : ℝ) : ℝ :=
  -4 * x * (1 - x) * deriv (fun y : ℝ => Aang 4 y α) x + (α/3) * (6 * x - 4) * Aang 4 x α

/-- The sixth angular polynomial. -/
def Aang6 (x α : ℝ) : ℝ :=
  -4 * x * (1 - x) * deriv (fun y : ℝ => Aang5 y α) x + (α/3) * (6 * x - 4) * Aang5 x α

/-! ## The explicit derivative of `A₄` -/

theorem deriv_Aang_four (x α : ℝ) : deriv (fun y : ℝ => Aang 4 y α) x = D4p x α := by
  have h : (fun y : ℝ => Aang 4 y α) = fun y : ℝ =>
      a4 0 α + a4 1 α * y + a4 2 α * y^2 + a4 3 α * y^3 + a4 4 α * y^4 + a4 5 α * y^5 := by
    funext y
    simp only [Aang_four]
    unfold a4
    norm_num [ac4, Finset.sum_range_succ]
    ring
  rw [h, deriv_mono5]
  unfold D4p a4
  norm_num [dq4, ac4, Finset.sum_range_succ]
  ring

/-! ## The explicit expansion of `A₅` -/

theorem Aang5_eq_mono (x α : ℝ) : Aang5 x α = ∑ j ∈ Finset.range 7, c5 j α * x ^ j := by
  rw [Aang5, deriv_Aang_four]
  unfold D4p c5
  norm_num [cc5, dq4, Aang_four, Finset.sum_range_succ]
  ring

theorem differentiable_Aang5 (α : ℝ) : Differentiable ℝ (fun y : ℝ => Aang5 y α) := by
  rw [show (fun y : ℝ => Aang5 y α) = fun y : ℝ => ∑ j ∈ Finset.range 7, c5 j α * y ^ j from
    funext (fun y => Aang5_eq_mono y α)]
  fun_prop

/-! ## The pointwise bounds -/

/-- `|D₄(x,α)| ≤ 4325808` on `[0,1] × (0,1]`. -/
theorem abs_D4p_le (x α : ℝ) (hx : x ∈ Set.Icc 0 1) (hα : 0 < α) (hα1 : α ≤ 1) :
    |D4p x α| ≤ 4325808 := by
  have hx0 := hx.1
  have hx1 := hx.2
  have hβ0 : 0 ≤ α / 3 := by linarith
  have hβ1 : α / 3 ≤ 1 := by linarith
  have h2 : |∑ k ∈ Finset.range 5, (∑ j ∈ Finset.range 5, dq4 k j * x ^ j) * (α/3)^k|
      ≤ 4325808 := by
    calc |∑ k ∈ Finset.range 5, (∑ j ∈ Finset.range 5, dq4 k j * x ^ j) * (α/3)^k|
        ≤ ∑ k ∈ Finset.range 5, |(∑ j ∈ Finset.range 5, dq4 k j * x ^ j) * (α/3)^k| :=
          Finset.abs_sum_le_sum_abs _ _
      _ = ∑ k ∈ Finset.range 5, |(∑ j ∈ Finset.range 5, dq4 k j * x ^ j)| * (α/3)^k := by
          apply Finset.sum_congr rfl
          intro k hk
          rw [abs_mul, abs_of_nonneg (pow_nonneg hβ0 k)]
      _ ≤ ∑ k ∈ Finset.range 5, (∑ j ∈ Finset.range 5, |dq4 k j|) * 1 := by
          apply Finset.sum_le_sum
          intro k hk
          have hk1 : |∑ j ∈ Finset.range 5, dq4 k j * x ^ j| ≤ ∑ j ∈ Finset.range 5, |dq4 k j| :=
            abs_sum_mul_pow_le 5 x (dq4 k) hx0 hx1
          have hk2 : (α/3)^k ≤ 1 := pow_le_one₀ hβ0 hβ1
          exact mul_le_mul hk1 hk2 (pow_nonneg hβ0 k) (by positivity)
      _ = 4325808 := by norm_num [Finset.sum_range_succ, dq4]
  rw [D4p]
  exact h2

/-- `|A₅(x,α)| ≤ 24325808·(α + 4x(1-x))` on `[0,1] × (0,1]`. -/
theorem Aang5_bound (x α : ℝ) (hx : x ∈ Set.Icc 0 1) (hα : 0 < α) (hα1 : α ≤ 1) :
    |Aang5 x α| ≤ 24325808 * (α + 4 * x * (1 - x)) := by
  have hx0 := hx.1
  have hx1 := hx.2
  have h4 : 0 ≤ 4 * x * (1 - x) := by nlinarith
  have hβ0 : 0 ≤ α / 3 := by linarith
  have hD4 : |D4p x α| ≤ 4325808 := abs_D4p_le x α hx hα hα1
  have hA : |Aang 4 x α| ≤ 10 ^ 7 * (α + 4 * x * (1 - x)) := glop_Aang_bound_four x α hx hα hα1
  have hx4 : |6 * x - 4| ≤ 4 := by
    rw [abs_le]; constructor <;> linarith
  rw [Aang5, deriv_Aang_four]
  have hsplit : |(-4) * x * (1 - x) * D4p x α + (α/3) * (6 * x - 4) * Aang 4 x α|
      ≤ 4 * x * (1 - x) * 4325808 + (α/3) * 4 * (10^7 * (α + 4 * x * (1 - x))) := by
    have h1 : |(-4) * x * (1 - x) * D4p x α| = 4 * x * (1 - x) * |D4p x α| := by
      rw [abs_mul, abs_of_nonpos (by nlinarith : (-4) * x * (1 - x) ≤ 0)]
      ring
    have h2 : |(α/3) * (6 * x - 4) * Aang 4 x α| = (α/3) * |6 * x - 4| * |Aang 4 x α| := by
      rw [abs_mul, abs_mul, abs_of_nonneg hβ0]
    have h3 : 4 * x * (1 - x) * |D4p x α| ≤ 4 * x * (1 - x) * 4325808 :=
      mul_le_mul_of_nonneg_left hD4 h4
    have h5 : (α/3) * |6 * x - 4| * |Aang 4 x α|
        ≤ (α/3) * 4 * (10^7 * (α + 4 * x * (1 - x))) := by
      have h6 : |6*x - 4| * |Aang 4 x α| ≤ 4 * (10^7 * (α + 4*x*(1-x))) :=
        mul_le_mul hx4 hA (abs_nonneg _) (by norm_num)
      have := mul_le_mul_of_nonneg_left h6 hβ0
      linarith [this]
    calc |(-4) * x * (1 - x) * D4p x α + (α/3) * (6 * x - 4) * Aang 4 x α|
        ≤ |(-4) * x * (1 - x) * D4p x α| + |(α/3) * (6 * x - 4) * Aang 4 x α| := abs_add_le _ _
      _ = 4 * x * (1 - x) * |D4p x α| + (α/3) * |6 * x - 4| * |Aang 4 x α| := by rw [h1, h2]
      _ ≤ 4 * x * (1 - x) * 4325808 + (α/3) * 4 * (10^7 * (α + 4 * x * (1 - x))) :=
          add_le_add h3 h5
  have hfin : 4 * x * (1 - x) * 4325808 + (α/3) * 4 * (10^7 * (α + 4 * x * (1 - x)))
      ≤ 24325808 * (α + 4 * x * (1 - x)) := by
    nlinarith [h4, hα, hα1, sq_nonneg (1 - x)]
  linarith [hsplit, hfin]

/-- `|∂ₓA₅(x,α)| ≤ 196578816` on `[0,1] × (0,1]`. -/
theorem deriv_Aang5_bound (x α : ℝ) (hx : x ∈ Set.Icc 0 1) (hα : 0 < α) (hα1 : α ≤ 1) :
    |deriv (fun y : ℝ => Aang5 y α) x| ≤ 196578816 := by
  have hx0 := hx.1
  have hx1 := hx.2
  have hβ0 : 0 ≤ α / 3 := by linarith
  have hβ1 : α / 3 ≤ 1 := by linarith
  have hfun : (fun y : ℝ => Aang5 y α) = fun y : ℝ => ∑ j ∈ Finset.range (6+1), c5 j α * y ^ j :=
    funext (fun y => Aang5_eq_mono y α)
  rw [hfun, deriv_mono_succ 6 (fun j => c5 j α) x]
  calc |∑ j ∈ Finset.range 6, ((j:ℝ) + 1) * c5 (j + 1) α * x ^ j|
      ≤ ∑ j ∈ Finset.range 6, |((j:ℝ) + 1) * c5 (j + 1) α| :=
        abs_sum_mul_pow_le 6 x (fun j => ((j:ℝ) + 1) * c5 (j+1) α) hx0 hx1
    _ = ∑ j ∈ Finset.range 6, ((j:ℝ) + 1) * |c5 (j + 1) α| := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ (j:ℝ) + 1)]
    _ ≤ ∑ j ∈ Finset.range 6, ((j:ℝ) + 1) * (∑ k ∈ Finset.range 6, |cc5 k (j+1)|) := by
        apply Finset.sum_le_sum
        intro j hj
        have hc : |c5 (j+1) α| ≤ ∑ k ∈ Finset.range 6, |cc5 k (j+1)| := by
          rw [c5]
          exact abs_sum_mul_pow_le 6 (α/3) (fun k => cc5 k (j+1)) hβ0 hβ1
        exact mul_le_mul_of_nonneg_left hc (by positivity)
    _ = 196578816 := by norm_num [Finset.sum_range_succ, cc5]

/-- `|A₆(x,α)| ≤ 245230432·(α + 4x(1-x))` on `[0,1] × (0,1]`. -/
theorem Aang6_bound (x α : ℝ) (hx : x ∈ Set.Icc 0 1) (hα : 0 < α) (hα1 : α ≤ 1) :
    |Aang6 x α| ≤ 245230432 * (α + 4 * x * (1 - x)) := by
  have hx0 := hx.1
  have hx1 := hx.2
  have h4 : 0 ≤ 4 * x * (1 - x) := by nlinarith
  have hβ0 : 0 ≤ α / 3 := by linarith
  have hd5 : |deriv (fun y : ℝ => Aang5 y α) x| ≤ 196578816 := deriv_Aang5_bound x α hx hα hα1
  have hA : |Aang5 x α| ≤ 24325808 * (α + 4 * x * (1 - x)) := Aang5_bound x α hx hα hα1
  have hx4 : |6 * x - 4| ≤ 4 := by rw [abs_le]; constructor <;> linarith
  rw [Aang6]
  have hsplit : |(-4) * x * (1 - x) * deriv (fun y : ℝ => Aang5 y α) x
        + (α/3) * (6 * x - 4) * Aang5 x α|
      ≤ 4 * x * (1 - x) * 196578816 + (α/3) * 4 * (24325808 * (α + 4 * x * (1 - x))) := by
    have h1 : |(-4) * x * (1 - x) * deriv (fun y : ℝ => Aang5 y α) x|
        = 4 * x * (1 - x) * |deriv (fun y : ℝ => Aang5 y α) x| := by
      rw [abs_mul, abs_of_nonpos (by nlinarith : (-4) * x * (1 - x) ≤ 0)]
      ring
    have h2 : |(α/3) * (6 * x - 4) * Aang5 x α| = (α/3) * |6 * x - 4| * |Aang5 x α| := by
      rw [abs_mul, abs_mul, abs_of_nonneg hβ0]
    have h3 : 4 * x * (1 - x) * |deriv (fun y : ℝ => Aang5 y α) x|
        ≤ 4 * x * (1 - x) * 196578816 :=
      mul_le_mul_of_nonneg_left hd5 h4
    have h5 : (α/3) * |6 * x - 4| * |Aang5 x α|
        ≤ (α/3) * 4 * (24325808 * (α + 4 * x * (1 - x))) := by
      have h6 : |6*x - 4| * |Aang5 x α| ≤ 4 * (24325808 * (α + 4*x*(1-x))) :=
        mul_le_mul hx4 hA (abs_nonneg _) (by norm_num)
      have := mul_le_mul_of_nonneg_left h6 hβ0
      linarith [this]
    calc |(-4) * x * (1 - x) * deriv (fun y : ℝ => Aang5 y α) x
          + (α/3) * (6 * x - 4) * Aang5 x α|
        ≤ |(-4) * x * (1 - x) * deriv (fun y : ℝ => Aang5 y α) x|
          + |(α/3) * (6 * x - 4) * Aang5 x α| := abs_add_le _ _
      _ = 4 * x * (1 - x) * |deriv (fun y : ℝ => Aang5 y α) x|
          + (α/3) * |6 * x - 4| * |Aang5 x α| := by rw [h1, h2]
      _ ≤ 4 * x * (1 - x) * 196578816 + (α/3) * 4 * (24325808 * (α + 4 * x * (1 - x))) :=
          add_le_add h3 h5
  have hfin : 4 * x * (1 - x) * 196578816 + (α/3) * 4 * (24325808 * (α + 4 * x * (1 - x)))
      ≤ 245230432 * (α + 4 * x * (1 - x)) := by
    nlinarith [h4, hα, hα1]
  linarith [hsplit, hfin]

/-! ## The fifth and sixth iterates -/

theorem Lop_iter_psiA5 (α : ℝ) (hα : 0 < α) :
    ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      (Work.Spaces.Lop^[5] (psiA α)) θ = Work.Spaces.Gam α θ * Aang5 (Real.cos θ ^ 2) α := by
  intro θ hθ
  have h4 : (Work.Spaces.Lop^[4] (psiA α))
      =ᶠ[𝓝 θ] fun y => Work.Spaces.Gam α y * Aang 4 (Real.cos y ^ 2) α := by
    filter_upwards [Ioo_mem_nhds hθ.1 hθ.2] with y hy
    exact glop_Lop_iter_psiA α hα 4 le_rfl y hy
  rw [Function.iterate_succ_apply']
  rw [show Work.Spaces.Lop (Work.Spaces.Lop^[4] (psiA α)) θ
      = Work.Spaces.Lop (fun y => Work.Spaces.Gam α y * Aang 4 (Real.cos y ^ 2) α) θ from by
    show Real.sin (2 * θ) * deriv (Work.Spaces.Lop^[4] (psiA α)) θ
        = Real.sin (2 * θ) * deriv (fun y => Work.Spaces.Gam α y * Aang 4 (Real.cos y ^ 2) α) θ
    rw [h4.deriv_eq]]
  rw [glop_step α hα (fun y : ℝ => Aang 4 y α) (differentiable_Aang 4 le_rfl α) θ hθ]
  simp only [Aang5]

theorem Lop_iter_psiA6 (α : ℝ) (hα : 0 < α) :
    ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      (Work.Spaces.Lop^[6] (psiA α)) θ = Work.Spaces.Gam α θ * Aang6 (Real.cos θ ^ 2) α := by
  intro θ hθ
  have h5 : (Work.Spaces.Lop^[5] (psiA α))
      =ᶠ[𝓝 θ] fun y => Work.Spaces.Gam α y * Aang5 (Real.cos y ^ 2) α := by
    filter_upwards [Ioo_mem_nhds hθ.1 hθ.2] with y hy
    exact Lop_iter_psiA5 α hα y hy
  rw [Function.iterate_succ_apply']
  rw [show Work.Spaces.Lop (Work.Spaces.Lop^[5] (psiA α)) θ
      = Work.Spaces.Lop (fun y => Work.Spaces.Gam α y * Aang5 (Real.cos y ^ 2) α) θ from by
    show Real.sin (2 * θ) * deriv (Work.Spaces.Lop^[5] (psiA α)) θ
        = Real.sin (2 * θ) * deriv (fun y => Work.Spaces.Gam α y * Aang5 (Real.cos y ^ 2) α) θ
    rw [h5.deriv_eq]]
  rw [glop_step α hα (fun y : ℝ => Aang5 y α) (differentiable_Aang5 α) θ hθ]
  simp only [Aang6]

/-! ## The target theorem -/

theorem H6N_GammaTerm_Lop_bound :
    ∃ D : ℝ, 0 < D ∧ ∀ α : ℝ, 0 < α → α ≤ 1 → ∀ i : ℕ, 1 ≤ i → i ≤ 6 →
      ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
        |(Work.Spaces.Lop^[i] (Work.Construction.psiA α)) θ|
          ≤ D * Work.Spaces.Gam α θ * (Real.sin (2 * θ) ^ 2 + α) := by
  refine ⟨10 ^ 9, by norm_num, ?_⟩
  intro α hα hα1 i hi1 hi6 θ hθ
  have hGam0 : 0 ≤ Work.Spaces.Gam α θ :=
    (Work.Spaces.Gam_bounds α θ hα (Set.Ioo_subset_Icc_self hθ)).1
  have hxc : Real.cos θ ^ 2 ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨sq_nonneg _, by linarith [Real.cos_sq_le_one θ]⟩
  have hsin2 : 4 * Real.cos θ ^ 2 * (1 - Real.cos θ ^ 2) = Real.sin (2 * θ) ^ 2 := by
    rw [Real.sin_two_mul]; ring_nf; rw [Real.sin_sq]; ring
  have step : ∀ (j : ℕ) (a : ℝ → ℝ)
      (hh : (Work.Spaces.Lop^[j] (psiA α)) θ = Work.Spaces.Gam α θ * a (Real.cos θ ^ 2))
      (C : ℝ) (hC : |a (Real.cos θ ^ 2)| ≤ C * (α + 4 * Real.cos θ ^ 2 * (1 - Real.cos θ ^ 2)))
      (hC9 : C ≤ 10 ^ 9),
      |(Work.Spaces.Lop^[j] (psiA α)) θ|
        ≤ 10 ^ 9 * Work.Spaces.Gam α θ * (Real.sin (2 * θ) ^ 2 + α) := by
    intro j a hh C hC hC9
    rw [hh]
    calc |Work.Spaces.Gam α θ * a (Real.cos θ ^ 2)|
        = Work.Spaces.Gam α θ * |a (Real.cos θ ^ 2)| := by
          rw [abs_mul, abs_of_nonneg hGam0]
      _ ≤ Work.Spaces.Gam α θ * (C * (α + 4 * Real.cos θ ^ 2 * (1 - Real.cos θ ^ 2))) :=
          mul_le_mul_of_nonneg_left hC hGam0
      _ = C * Work.Spaces.Gam α θ * (Real.sin (2 * θ) ^ 2 + α) := by rw [hsin2]; ring
      _ ≤ 10 ^ 9 * Work.Spaces.Gam α θ * (Real.sin (2 * θ) ^ 2 + α) := by
          have hpos : 0 ≤ Work.Spaces.Gam α θ * (Real.sin (2 * θ) ^ 2 + α) :=
            mul_nonneg hGam0 (by nlinarith [sq_nonneg (Real.sin (2 * θ)), hα])
          nlinarith [hpos, hC9]
  interval_cases i
  · exact step 1 (fun x => Aang 1 x α) (glop_Lop_iter_psiA α hα 1 (by norm_num) θ hθ) (10^7)
      (glop_Aang_bound_one _ _ hxc hα hα1) (by norm_num)
  · exact step 2 (fun x => Aang 2 x α) (glop_Lop_iter_psiA α hα 2 (by norm_num) θ hθ) (10^7)
      (glop_Aang_bound_two _ _ hxc hα hα1) (by norm_num)
  · exact step 3 (fun x => Aang 3 x α) (glop_Lop_iter_psiA α hα 3 (by norm_num) θ hθ) (10^7)
      (glop_Aang_bound_three _ _ hxc hα hα1) (by norm_num)
  · exact step 4 (fun x => Aang 4 x α) (glop_Lop_iter_psiA α hα 4 le_rfl θ hθ) (10^7)
      (glop_Aang_bound_four _ _ hxc hα hα1) (by norm_num)
  · exact step 5 (fun x => Aang5 x α) (Lop_iter_psiA5 α hα θ hθ) 24325808
      (Aang5_bound _ _ hxc hα hα1) (by norm_num)
  · exact step 6 (fun x => Aang6 x α) (Lop_iter_psiA6 α hα θ hθ) 245230432
      (Aang6_bound _ _ hxc hα hα1) (by norm_num)

end Work.Construction
