/-
# `H6Pair6Aux/Defs` — the two coefficients of the `N₀` zero-mode estimate

The zero-mode estimate `|L₁₂(N₀)(0)| ≤ K α^{-9}(1+M)^4` of `Work.FTS.StrongPersist.H6Pair6Aux`
proceeds through the pointwise bound, valid for `r > 0`, `θ ∈ (0,π/2)`,

`(N₀ α (F_*+g) g r θ)² · w r ≤ 7 · (A · HkIntegrand α 4 g r θ + B · (1/(1+r))²)`

where the two coefficients are the ones of the sibling `Work.FTS.Nonlinear.Pieces.rowsAux`
(the level-four estimate `rl0_bound`):

* `A` collects the four terms of `N₀` whose angular factor is (at least) one extra `sin(2θ)`,
  so that they are dominated by the `ℋ⁴`-integrand of `g`;
* `B` collects the four terms whose radial factor is exactly `z ↦ z/(1+r)²` (`F_*`-terms), whose
  square times the Hardy weight `w r = (1+r)²/r²` is *exactly* `(1/(1+r))²`
  (`Work.Spaces.sq_div_shape_eq`).

They are exposed here (rather than being introduced by `set` inside the estimate) so that the
pointwise bound and its consumers can be stated in a single, stable notation.
-/
import Mathlib.Algebra.Order.Star.Real

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology

namespace Work.FTS.StrongPersist.H6Pair6Aux

set_option autoImplicit false

/-- The `ℋ⁴`-coefficient of the pointwise bound for `N₀`: it prices the terms of `N₀` which are
dominated slot by slot by the `ℋ⁴`-integrand of `g` (the two `L₁₂(g)`-terms and the
`L₁₂(F_*)`-term, together with the `(1/α)L₁₂(g)g`-term). -/
def A₀ (α X : ℝ) : ℝ := 9 * X ^ 2 / α ^ 2 + 81 * X ^ 2 / (4 * α ^ 2) + 36 * X ^ 2 + 16 * α ^ 2

/-- The radial coefficient of the pointwise bound for `N₀`: it prices the terms whose `z`-dependence
is exactly `z/(1+z)²` (the `F_*`-terms and the collapse `N₀₁ + N₀₂ = 8α²c2m z²Γ/(c(1+z)⁴)`), so
that after multiplication by the Hardy weight `w` they contribute the integrable profile
`(1/(1+r))²`. -/
def B₀ (α X : ℝ) : ℝ := (160 * α ^ 2) ^ 2 + (180 * α * X) ^ 2 + (240 * α * X) ^ 2

theorem A₀_nonneg (α X : ℝ) : 0 ≤ A₀ α X := by
  have h1 : (0 : ℝ) ≤ 9 * X ^ 2 / α ^ 2 :=
    div_nonneg (mul_nonneg (by norm_num) (sq_nonneg X)) (sq_nonneg α)
  have h2 : (0 : ℝ) ≤ 81 * X ^ 2 / (4 * α ^ 2) :=
    div_nonneg (mul_nonneg (by norm_num) (sq_nonneg X)) (by positivity)
  have h3 : (0 : ℝ) ≤ 36 * X ^ 2 := mul_nonneg (by norm_num) (sq_nonneg X)
  have h4 : (0 : ℝ) ≤ 16 * α ^ 2 := mul_nonneg (by norm_num) (sq_nonneg α)
  rw [A₀]
  linarith

theorem B₀_nonneg (α X : ℝ) : 0 ≤ B₀ α X := by
  rw [B₀]
  nlinarith [sq_nonneg (160 * α ^ 2), sq_nonneg (180 * α * X), sq_nonneg (240 * α * X)]

/-- The crude upper bound for `A₀` used in the final arithmetic: with `α ≤ 1` one has
`9 + 81/4 + 36 = 261/4 ≤ 90` after pushing the `36 X²` term into `X²/α²`. -/
theorem A₀_le {α X : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    A₀ α X ≤ 90 * X ^ 2 / α ^ 2 + 16 * α ^ 2 := by
  have h4 : (0 : ℝ) < 4 * α ^ 2 := by positivity
  have hα2le : α ^ 2 ≤ 1 := by nlinarith
  have hprod : α ^ 2 * X ^ 2 ≤ X ^ 2 := by
    simpa using mul_le_mul_of_nonneg_right hα2le (sq_nonneg X)
  have hcross : A₀ α X * (4 * α ^ 2) ≤ (90 * X ^ 2 / α ^ 2 + 16 * α ^ 2) * (4 * α ^ 2) := by
    have e1 : A₀ α X * (4 * α ^ 2) = 36 * X ^ 2 + 81 * X ^ 2 + 144 * α ^ 2 * X ^ 2
        + 64 * α ^ 4 := by
      rw [A₀]; field_simp; ring
    have e2 : (90 * X ^ 2 / α ^ 2 + 16 * α ^ 2) * (4 * α ^ 2) = 360 * X ^ 2 + 64 * α ^ 4 := by
      field_simp; ring
    rw [e1, e2]
    nlinarith [hprod]
  exact le_of_mul_le_mul_right hcross h4

/-- The exact value of the `B₀`-constants: `180² + 240² = 90000`. -/
theorem B₀_le (α X : ℝ) : B₀ α X ≤ 25600 * α ^ 4 + 90000 * α ^ 2 * X ^ 2 := by
  rw [B₀]
  have h1 : (160 * α ^ 2) ^ 2 = 25600 * α ^ 4 := by ring
  have h2 : (180 * α * X) ^ 2 + (240 * α * X) ^ 2 = 90000 * α ^ 2 * X ^ 2 := by ring
  linarith

end Work.FTS.StrongPersist.H6Pair6Aux
