/-
# Auxiliary polynomials for the `D_θ`-bound on `ψ = c2m·Γ`

The target `Work.Construction.H4N_GammaTerm_Lop_bound` states that the iterates
`D_θ^i ψ`, `1 ≤ i ≤ 4`, of the angular factor `ψ(θ) = c2m(θ)·Γ(θ)` of the `Γ`-term
are bounded by `D·Γ(θ)·(sin²(2θ) + α)`, uniformly in `0 < α ≤ 1`.

The mechanism is that on the open quadrant `D_θ = sin(2θ)∂_θ` acts, after writing
`x = cos²θ`, as the polynomial operator
`M = -4x(1-x)∂_x` on the first factor and as the multiplication
`(α/3)·(6x-4)` on the second (this is `D_θ(Γ) = (α/3)(6cos²θ-4)·Γ`), so that

  `D_θ^i ψ = Γ(θ) · Aᵢ(cos²θ, α)`

with `Aᵢ` the explicit polynomials defined below
(`Aᵢ₊₁ = M Aᵢ + (α/3)(6x-4)Aᵢ`, `A₀ = 3x-2 = c2m`).

Each `Aᵢ` is written in the form

  `Aᵢ = 4x(1-x)·Vᵢ(x) + ∑_{k=1}^{i} (α/3)^k P_{i,k}(x)`

(so that the `k = 0` part automatically carries the factor `sin²(2θ) = 4cos²θ sin²θ`
and the remaining parts carry a factor `α`), which makes the pointwise bound
`|Aᵢ| ≤ 10^7·(α + 4x(1-x))` on `[0,1]` elementary.

The file also contains the two general tools used for the bounds:
`deriv_mono5`, the derivative of a degree `≤ 5` monomial sum, and
`abs_mono5_le`, its bound on `[0,1]` by the sum of the absolute values of the
coefficients.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.InnerProductSpace.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

namespace Work.Construction

set_option autoImplicit false

/-- The `i`-th angular polynomial `Aᵢ(x,α)` of the `θ`-calculation, `i ≤ 4`
(written in the split form `4x(1-x)Vᵢ + ∑_{k≥1}(α/3)^k P_{i,k}`). -/
def Aang (i : ℕ) : ℝ → ℝ → ℝ := fun x α =>
  match i with
  | 0 => 3 * x - 2
  | 1 => 4 * x * (1 - x) * (-3)
      + (α / 3) * (18 * x ^ 2 - 24 * x + 8)
  | 2 => 4 * x * (1 - x) * (12 - 24 * x)
      + (α / 3) * (216 * x ^ 3 - 360 * x ^ 2 + 144 * x)
      + (α / 3) ^ 2 * (108 * x ^ 3 - 216 * x ^ 2 + 144 * x - 32)
  | 3 => 4 * x * (1 - x) * (-48 + 288 * x - 288 * x ^ 2)
      + (α / 3) * (3168 * x ^ 4 - 6720 * x ^ 3 + 4320 * x ^ 2 - 768 * x)
      + (α / 3) ^ 2 * (2592 * x ^ 4 - 6048 * x ^ 3 + 4608 * x ^ 2 - 1152 * x)
      + (α / 3) ^ 3 * (648 * x ^ 4 - 1728 * x ^ 3 + 1728 * x ^ 2 - 768 * x + 128)
  | 4 => 4 * x * (1 - x) * (192 - 2688 * x + 6912 * x ^ 2 - 4608 * x ^ 3)
      + (α / 3) * (57600 * x ^ 5 - 149760 * x ^ 4 + 132480 * x ^ 3 - 44160 * x ^ 2 + 3840 * x)
      + (α / 3) ^ 2 * (60480 * x ^ 5 - 167040 * x ^ 4 + 162240 * x ^ 3 - 63360 * x ^ 2 + 7680 * x)
      + (α / 3) ^ 3 * (25920 * x ^ 5 - 77760 * x ^ 4 + 86400 * x ^ 3 - 42240 * x ^ 2 + 7680 * x)
      + (α / 3) ^ 4 * (3888 * x ^ 5 - 12960 * x ^ 4 + 17280 * x ^ 3 - 11520 * x ^ 2 + 3840 * x - 512)
  | _ => 0

@[simp] theorem Aang_zero (x α : ℝ) : Aang 0 x α = 3 * x - 2 := rfl

@[simp] theorem Aang_one (x α : ℝ) : Aang 1 x α =
    4 * x * (1 - x) * (-3) + (α / 3) * (18 * x ^ 2 - 24 * x + 8) := rfl

@[simp] theorem Aang_two (x α : ℝ) : Aang 2 x α =
    4 * x * (1 - x) * (12 - 24 * x)
      + (α / 3) * (216 * x ^ 3 - 360 * x ^ 2 + 144 * x)
      + (α / 3) ^ 2 * (108 * x ^ 3 - 216 * x ^ 2 + 144 * x - 32) := rfl

@[simp] theorem Aang_three (x α : ℝ) : Aang 3 x α =
    4 * x * (1 - x) * (-48 + 288 * x - 288 * x ^ 2)
      + (α / 3) * (3168 * x ^ 4 - 6720 * x ^ 3 + 4320 * x ^ 2 - 768 * x)
      + (α / 3) ^ 2 * (2592 * x ^ 4 - 6048 * x ^ 3 + 4608 * x ^ 2 - 1152 * x)
      + (α / 3) ^ 3 * (648 * x ^ 4 - 1728 * x ^ 3 + 1728 * x ^ 2 - 768 * x + 128) := rfl

@[simp] theorem Aang_four (x α : ℝ) : Aang 4 x α =
    4 * x * (1 - x) * (192 - 2688 * x + 6912 * x ^ 2 - 4608 * x ^ 3)
      + (α / 3) * (57600 * x ^ 5 - 149760 * x ^ 4 + 132480 * x ^ 3 - 44160 * x ^ 2 + 3840 * x)
      + (α / 3) ^ 2 * (60480 * x ^ 5 - 167040 * x ^ 4 + 162240 * x ^ 3 - 63360 * x ^ 2 + 7680 * x)
      + (α / 3) ^ 3 * (25920 * x ^ 5 - 77760 * x ^ 4 + 86400 * x ^ 3 - 42240 * x ^ 2 + 7680 * x)
      + (α / 3) ^ 4 * (3888 * x ^ 5 - 12960 * x ^ 4 + 17280 * x ^ 3 - 11520 * x ^ 2 + 3840 * x - 512) := rfl

/-! ## Two general tools -/

/-- The derivative of a monomial sum of degree at most `5`. -/
theorem deriv_mono5 (a0 a1 a2 a3 a4 a5 x : ℝ) :
    deriv (fun y : ℝ => a0 + a1 * y + a2 * y ^ 2 + a3 * y ^ 3 + a4 * y ^ 4 + a5 * y ^ 5) x
      = a1 + 2 * a2 * x + 3 * a3 * x ^ 2 + 4 * a4 * x ^ 3 + 5 * a5 * x ^ 4 := by
  set P : Polynomial ℝ := Polynomial.C a0 + Polynomial.C a1 * Polynomial.X
      + Polynomial.C a2 * Polynomial.X ^ 2 + Polynomial.C a3 * Polynomial.X ^ 3
      + Polynomial.C a4 * Polynomial.X ^ 4 + Polynomial.C a5 * Polynomial.X ^ 5 with hP
  have hfun : (fun y : ℝ => a0 + a1 * y + a2 * y ^ 2 + a3 * y ^ 3 + a4 * y ^ 4 + a5 * y ^ 5)
      = fun y => Polynomial.eval y P := by
    funext y
    simp only [hP, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
      Polynomial.eval_pow] <;> try ring
  rw [hfun, (Polynomial.hasDerivAt P x).deriv]
  simp only [hP, Polynomial.derivative_add, Polynomial.derivative_mul, Polynomial.derivative_C,
    Polynomial.derivative_X, Polynomial.derivative_pow, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_pow, Polynomial.eval_one,
    Polynomial.eval_zero]
  ring

/-- A monomial sum of degree at most `5` is bounded on `[0,1]` by the sum of the
absolute values of its coefficients. -/
theorem abs_mono5_le (a0 a1 a2 a3 a4 a5 x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    |a0 + a1 * x + a2 * x ^ 2 + a3 * x ^ 3 + a4 * x ^ 4 + a5 * x ^ 5|
      ≤ |a0| + |a1| + |a2| + |a3| + |a4| + |a5| := by
  have hx : ∀ m : ℕ, |x ^ m| ≤ 1 := by
    intro m
    rw [abs_of_nonneg (pow_nonneg hx0 m)]
    exact pow_le_one₀ hx0 hx1
  have h1 : |a0 + a1 * x + a2 * x ^ 2 + a3 * x ^ 3 + a4 * x ^ 4 + a5 * x ^ 5|
      ≤ |a0 + a1 * x + a2 * x ^ 2 + a3 * x ^ 3 + a4 * x ^ 4| + |a5 * x ^ 5| :=
    abs_add_le _ _
  have h2 : |a0 + a1 * x + a2 * x ^ 2 + a3 * x ^ 3 + a4 * x ^ 4|
      ≤ |a0 + a1 * x + a2 * x ^ 2 + a3 * x ^ 3| + |a4 * x ^ 4| := abs_add_le _ _
  have h3 : |a0 + a1 * x + a2 * x ^ 2 + a3 * x ^ 3|
      ≤ |a0 + a1 * x + a2 * x ^ 2| + |a3 * x ^ 3| := abs_add_le _ _
  have h4 : |a0 + a1 * x + a2 * x ^ 2| ≤ |a0 + a1 * x| + |a2 * x ^ 2| := abs_add_le _ _
  have h5 : |a0 + a1 * x| ≤ |a0| + |a1 * x| := abs_add_le _ _
  have h6 : |a1 * x| + |a2 * x ^ 2| + |a3 * x ^ 3| + |a4 * x ^ 4| + |a5 * x ^ 5|
      ≤ |a1| + |a2| + |a3| + |a4| + |a5| := by
    simp only [abs_mul]
    have hh1 := hx 1
    have hh2 := hx 2
    have hh3 := hx 3
    have hh4 := hx 4
    have hh5 := hx 5
    simp only [pow_one] at hh1
    nlinarith [abs_nonneg a1, abs_nonneg a2, abs_nonneg a3, abs_nonneg a4, abs_nonneg a5,
      abs_nonneg x, abs_nonneg (x ^ 2), abs_nonneg (x ^ 3), abs_nonneg (x ^ 4), abs_nonneg (x ^ 5)]
  linarith

end Work.Construction
