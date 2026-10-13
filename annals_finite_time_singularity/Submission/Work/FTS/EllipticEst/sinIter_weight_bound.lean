/-
Copyright: work module for the Elgindi finite-time singularity project.

# The weight bound for `D_θ^i (sin 2θ)`

The paper's `H^k`-norm carries the angular weight `w_θ = sin(2θ)^{-γ/2}` with
`γ = 1 + α/10 ∈ (1, 11/10]`, which is singular at the endpoints `θ = 0`, `θ = π/2`
of `Iθ = [0, π/2]`.  The angular profile `sinIter i θ = D_θ^i (sin 2θ)` of the
iterated operator `D_θ = sin(2θ) ∂_θ` therefore has to vanish fast enough at the
endpoints for the weight to be integrable: this module proves

`sinIter i θ ^ 2 * sin(2θ) ^ (-γ) ≤ C_i` for all `θ ∈ Iθ`, `0 < α ≤ 1`,

with a constant `C_i` depending only on `i` (and not on `α`).

## The mechanism

`D_θ (sin 2θ) = sin(2θ) · 2 cos 2θ`, so `sinIter i` always carries a factor
`sin 2θ`; the remaining factor is a *polynomial in* `cos 2θ`:

`sinIter i θ = sin(2θ) · pᵢ (cos 2θ)`,

where `p₀ = 1` and `p_{i+1} = 2 X pᵢ - 2 (1 - X²) pᵢ'` (the recursion obtained from
`s² = 1 - c²` and `G ↦ 2c G + s G'`).  Since `|cos 2θ| ≤ 1`, the factor is bounded by
the sum `sinBound i` of the absolute values of the coefficients of `pᵢ`, and then
`sin(2θ)² · sin(2θ)^{-γ} = sin(2θ)^{2-γ} ≤ 1` because `0 ≤ sin 2θ ≤ 1` and
`0 ≤ 2 - γ ≤ 1`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.EllipticEst.GbarSetup
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst

set_option linter.unusedVariables false

/-! ## The polynomial describing `D_θ^i (sin 2θ) / sin 2θ` -/

/-- The sequence of polynomials `pᵢ` with
`D_θ^i (sin 2θ) = sin(2θ) · pᵢ (cos 2θ)`, defined by `p₀ = 1` and
`p_{i+1} = 2 X pᵢ - 2 (1 - X²) pᵢ'`. -/
def sinPoly : ℕ → Polynomial ℝ
  | 0 => 1
  | (i+1) => 2 * Polynomial.X * sinPoly i - 2 * (1 - Polynomial.X^2) * (sinPoly i).derivative

/-- The evaluation of the defining recursion of `sinPoly`. -/
theorem sinPoly_eval_succ (i : ℕ) (t : ℝ) :
    (sinPoly (i+1)).eval t =
      2 * t * (sinPoly i).eval t - 2 * (1 - t^2) * (sinPoly i).derivative.eval t := by
  simp [sinPoly, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_pow]

/-- One step of the recursion `sinIter (i+1) θ = sin(2θ) · (sinIter i)' θ`. -/
theorem sinIter_succ (i : ℕ) (θ : ℝ) :
    sinIter (i+1) θ = Real.sin (2*θ) * deriv (fun t : ℝ => sinIter i t) θ := by
  simp [sinIter, Work.Spaces.DthIter, Work.Spaces.Dth, Work.Spaces.pth]

/-- The derivative of `θ ↦ sin(2θ) · p (cos 2θ)`, computed with the chain rule. -/
theorem deriv_sin_mul_eval (p : Polynomial ℝ) (θ : ℝ) :
    deriv (fun t : ℝ => Real.sin (2*t) * p.eval (Real.cos (2*t))) θ
      = 2 * Real.cos (2*θ) * p.eval (Real.cos (2*θ))
        - 2 * (Real.sin (2*θ))^2 * p.derivative.eval (Real.cos (2*θ)) := by
  have hsin : HasDerivAt (fun t : ℝ => Real.sin (2*t)) (2 * Real.cos (2*θ)) θ := by
    have h := (Real.hasDerivAt_sin (2*θ)).comp θ ((hasDerivAt_id θ).const_mul (2:ℝ))
    simpa [Function.comp_def, mul_comm] using h
  have hcos : HasDerivAt (fun t : ℝ => Real.cos (2*t)) (-2 * Real.sin (2*θ)) θ := by
    have h := (Real.hasDerivAt_cos (2*θ)).comp θ ((hasDerivAt_id θ).const_mul (2:ℝ))
    simpa [Function.comp_def, mul_comm] using h
  have hpc : HasDerivAt (fun t : ℝ => p.eval (Real.cos (2*t)))
      (p.derivative.eval (Real.cos (2*θ)) * (-2*Real.sin (2*θ))) θ := by
    have h := (Polynomial.hasDerivAt p (Real.cos (2*θ))).comp θ hcos
    simpa [Function.comp_def] using h
  have hmul := hsin.mul hpc
  change deriv ((fun t : ℝ => Real.sin (2*t)) * fun t : ℝ => p.eval (Real.cos (2*t))) θ
      = 2 * Real.cos (2*θ) * p.eval (Real.cos (2*θ))
        - 2 * (Real.sin (2*θ))^2 * p.derivative.eval (Real.cos (2*θ))
  rw [hmul.deriv]
  ring

/-- The fundamental factorisation `sinIter i θ = sin(2θ) · pᵢ (cos 2θ)`. -/
theorem sinIter_eq_sinPoly (i : ℕ) :
    ∀ θ, sinIter i θ = Real.sin (2*θ) * (sinPoly i).eval (Real.cos (2*θ)) := by
  induction i with
  | zero => intro θ; simp [sinIter, sinPoly]
  | succ i ih =>
    intro θ
    rw [sinIter_succ]
    have hfun : (fun t : ℝ => sinIter i t)
        = fun t => Real.sin (2*t) * (sinPoly i).eval (Real.cos (2*t)) := by
      funext t; exact ih t
    rw [hfun, deriv_sin_mul_eval]
    have hs : (Real.sin (2*θ))^2 = 1 - (Real.cos (2*θ))^2 := by
      have h := Real.sin_sq_add_cos_sq (2*θ); linarith
    rw [hs, sinPoly_eval_succ]

/-! ## Uniform bounds -/

/-- A polynomial is bounded on `[-1,1]` by the sum of the absolute values of its
coefficients. -/
theorem poly_eval_abs_le (p : Polynomial ℝ) (t : ℝ) (ht : |t| ≤ 1) :
    |p.eval t| ≤ ∑ n ∈ p.support, |p.coeff n| := by
  rw [Polynomial.eval_eq_sum, Polynomial.sum_def]
  calc |∑ n ∈ p.support, p.coeff n * t ^ n| ≤ ∑ n ∈ p.support, |p.coeff n * t ^ n| := by
        exact Finset.abs_sum_le_sum_abs _ _
    _ = ∑ n ∈ p.support, |p.coeff n| * |t| ^ n := by
        refine Finset.sum_congr rfl ?_
        intro n _; rw [abs_mul, abs_pow]
    _ ≤ ∑ n ∈ p.support, |p.coeff n| * 1 := by
        refine Finset.sum_le_sum ?_
        intro n _
        exact mul_le_mul_of_nonneg_left (pow_le_one₀ (abs_nonneg t) ht) (abs_nonneg _)
    _ = ∑ n ∈ p.support, |p.coeff n| := by simp

/-- The universal constant bounding `pᵢ` on `[-1,1]`: the sum of the absolute values of
the coefficients of `sinPoly i`. -/
def sinBound (i : ℕ) : ℝ := ∑ n ∈ (sinPoly i).support, |(sinPoly i).coeff n|

theorem sinBound_nonneg (i : ℕ) : 0 ≤ sinBound i :=
  Finset.sum_nonneg (fun n _ => abs_nonneg _)

/-- `|sinIter i θ| ≤ sin(2θ) · sinBound i` for `θ` with `sin 2θ ≥ 0`. -/
theorem sinIter_abs_le (i : ℕ) (θ : ℝ) (h : 0 ≤ Real.sin (2*θ)) :
    |sinIter i θ| ≤ Real.sin (2*θ) * sinBound i := by
  rw [sinIter_eq_sinPoly i θ, abs_mul, abs_of_nonneg h]
  exact mul_le_mul_of_nonneg_left (poly_eval_abs_le _ _ (Real.abs_cos_le_one _)) h

/-- The squared form of `sinIter_abs_le`. -/
theorem sinIter_sq_le (i : ℕ) (θ : ℝ) (h : 0 ≤ Real.sin (2*θ)) :
    (sinIter i θ)^2 ≤ (sinBound i)^2 * (Real.sin (2*θ))^2 := by
  have h1 := sinIter_abs_le i θ h
  have h2 : (sinIter i θ)^2 = |sinIter i θ|^2 := by rw [sq_abs]
  rw [h2]
  have h3 : (Real.sin (2*θ) * sinBound i)^2 = (sinBound i)^2 * (Real.sin (2*θ))^2 := by
    ring
  calc |sinIter i θ|^2 ≤ (Real.sin (2*θ) * sinBound i)^2 :=
        pow_le_pow_left₀ (abs_nonneg _) h1 2
    _ = (sinBound i)^2 * (Real.sin (2*θ))^2 := h3

/-- For `0 < s ≤ 1` and `1 ≤ γ ≤ 2`: `s² · s^{-γ} ≤ 1`. -/
theorem sq_mul_rpow_neg_le_one (s γ : ℝ) (hs : 0 < s) (hs1 : s ≤ 1)
    (h1 : 1 ≤ γ) (h2 : γ ≤ 2) : s ^ 2 * s ^ (-γ) ≤ 1 := by
  have hs0 : 0 ≤ s := le_of_lt hs
  calc s ^ 2 * s ^ (-γ) = s ^ (2:ℝ) * s ^ (-γ) := by rw [← Real.rpow_ofNat s 2]
    _ = s ^ ((2:ℝ) + -γ) := by rw [Real.rpow_add hs]
    _ ≤ 1 := Real.rpow_le_one hs0 hs1 (by linarith)

/-! ## The target bound -/

theorem sinIter_weight_bound (i : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ θ ∈ Work.Spaces.Iθ,
      (Work.FTS.EllipticEst.sinIter i θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) ≤ C := by
  refine ⟨(sinBound i)^2, sq_nonneg _, ?_⟩
  intro α hα hα1 θ hθ
  have hsin_nonneg : 0 ≤ Real.sin (2*θ) := by
    have h1 : 0 ≤ θ := hθ.1
    have h2 : θ ≤ π/2 := hθ.2
    exact Real.sin_nonneg_of_mem_Icc ⟨by linarith, by linarith⟩
  have hgam1 : 1 ≤ Work.Spaces.gam α := by simp [Work.Spaces.gam]; linarith
  have hgam2 : Work.Spaces.gam α ≤ 2 := by simp [Work.Spaces.gam]; linarith
  rcases lt_or_eq_of_le hsin_nonneg with hpos | hzero
  · have hsq := sinIter_sq_le i θ hsin_nonneg
    have hpow_nonneg : 0 ≤ (Real.sin (2*θ)) ^ (-(Work.Spaces.gam α)) :=
      Real.rpow_nonneg hsin_nonneg _
    calc (sinIter i θ)^2 * (Real.sin (2*θ)) ^ (-(Work.Spaces.gam α))
        ≤ ((sinBound i)^2 * (Real.sin (2*θ))^2)
            * (Real.sin (2*θ)) ^ (-(Work.Spaces.gam α)) :=
          mul_le_mul_of_nonneg_right hsq hpow_nonneg
      _ = (sinBound i)^2 * ((Real.sin (2*θ))^2
            * (Real.sin (2*θ)) ^ (-(Work.Spaces.gam α))) := by ring
      _ ≤ (sinBound i)^2 * 1 := by
          refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
          exact sq_mul_rpow_neg_le_one _ _ hpos (Real.sin_le_one _) hgam1 hgam2
      _ = (sinBound i)^2 := mul_one _
  · have hz : Real.sin (2*θ) = 0 := hzero.symm
    rw [hz, Real.zero_rpow (by linarith : -(Work.Spaces.gam α) ≠ 0), mul_zero]
    exact sq_nonneg _

end Work.FTS.EllipticEst
