import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.EllipticEst.AngSecond.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The slice objects of the honest `I₄` upper bound

This module owns the vocabulary of the single-slice estimate
`Work.FTS.EllipticEst.Honest.I4SliceBound`: the angular slice `Φ` of a stream function,
`ψ = Φ / cos θ`, `b = Φ''`, `u = ∂_θ(tan θ · Φ)`, `P = cos²θ · ψ'`, the angular weight
`σ = sin(2θ)^{-99/100}`, the coefficient `Σ = (1-η)cos²θ + (3+η)sin²θ` (`η = 99/100`) and the
boundary primitive `G = ½ (sin θ / cos³θ) · σ · P²` together with its un-halved version `H`
(the quantity whose vanishing at `π/2⁻` is the hypothesis `hBound` of the target).

Everything is defined with the *literal* expressions of the target statement, so that
`simp only [I4sig, I4Σ, ...]` unfolds these abbreviations to the text of
`Work.FTS.EllipticEst.Honest.I4SliceBound`.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Honest

set_option autoImplicit false

/-- The angular weight `σ θ = sin(2θ)^{-99/100}` of the `I₄` slice estimate. -/
def I4sig (θ : ℝ) : ℝ := (Real.sin (2 * θ)) ^ (-(99 / 100 : ℝ))

/-- The angle coefficient `Σ θ = (1-η)cos²θ + (3+η)sin²θ`, `η = 99/100`. -/
def I4Sig (θ : ℝ) : ℝ := (1 - 99 / 100) * (Real.cos θ) ^ 2 + (3 + 99 / 100) * (Real.sin θ) ^ 2

/-- `ψ = Φ / cos θ`. -/
def I4psi (Φ : ℝ → ℝ) : ℝ → ℝ := fun θ => Φ θ / Real.cos θ

/-- `b = Φ''`. -/
def I4b (Φ : ℝ → ℝ) : ℝ → ℝ := fun θ => deriv (deriv Φ) θ

/-- `u = ∂_θ(tan θ · Φ)`. -/
def I4u (Φ : ℝ → ℝ) : ℝ → ℝ := fun θ => deriv (fun θ' => Real.tan θ' * Φ θ') θ

/-- `P = cos²θ · ψ'`. -/
def I4P (Φ : ℝ → ℝ) : ℝ → ℝ := fun θ => (Real.cos θ) ^ 2 * deriv (I4psi Φ) θ

/-- `G θ = ½ · (sin θ / cos³θ) · σ θ · P θ²`, the primitive of the `I₄` boundary term. -/
def I4G (Φ : ℝ → ℝ) : ℝ → ℝ :=
  fun θ => (1 / 2) * (Real.sin θ / (Real.cos θ) ^ 3) * I4sig θ * (I4P Φ θ) ^ 2

/-- The boundary quantity of `hBound`: `H = (sin θ / cos³θ) · (cos²θ · ψ')² · σ`. -/
def I4H (Φ : ℝ → ℝ) : ℝ → ℝ :=
  fun θ => Real.sin θ / (Real.cos θ) ^ 3 * ((Real.cos θ) ^ 2 * deriv (I4psi Φ) θ) ^ 2
    * I4sig θ

/-! ## Elementary pointwise facts -/

theorem I4sig_nonneg {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ I4sig θ := by
  rw [I4sig]
  refine Real.rpow_nonneg ?_ _
  exact Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

theorem I4sig_pos {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) : 0 < I4sig θ := by
  rw [I4sig]
  exact Real.rpow_pos_of_pos
    (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])) _

theorem I4Sig_ge (θ : ℝ) : 1 / 100 ≤ I4Sig θ := by
  have hs := Real.sin_sq_add_cos_sq θ
  rw [I4Sig]
  nlinarith [sq_nonneg (Real.cos θ), sq_nonneg (Real.sin θ)]

theorem I4Sig_pos (θ : ℝ) : 0 < I4Sig θ := lt_of_lt_of_le (by norm_num) (I4Sig_ge θ)

theorem I4H_eq_two_mul_I4G (Φ : ℝ → ℝ) (θ : ℝ) :
    I4H Φ θ = 2 * I4G Φ θ := by
  simp only [I4H, I4G, I4P]
  ring

theorem I4G_nonneg (Φ : ℝ → ℝ) {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    0 ≤ I4G Φ θ := by
  have hc : 0 < Real.cos θ :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
  have hs : 0 < Real.sin θ :=
    Real.sin_pos_of_mem_Ioo ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩
  simp only [I4G]
  have hσ : 0 ≤ I4sig θ := le_of_lt (I4sig_pos hθ)
  have h1 : 0 ≤ Real.sin θ / (Real.cos θ) ^ 3 :=
    div_nonneg (le_of_lt hs) (by positivity)
  have h2 : 0 ≤ (I4P Φ θ) ^ 2 := sq_nonneg _
  have h3 : (0:ℝ) ≤ 1 / 2 := by norm_num
  exact mul_nonneg (mul_nonneg (mul_nonneg h3 h1) hσ) h2

theorem I4psi_mul_cos {Φ : ℝ → ℝ} {θ : ℝ} (hcos : Real.cos θ ≠ 0) :
    I4psi Φ θ * Real.cos θ = Φ θ := by
  rw [I4psi]
  field_simp

end Work.FTS.EllipticEst.Honest
