import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.WProductRule
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Stability.CutFactorFderivZero
-- ===== merged: Submission.Work.FTS.H2.WPQ.Defs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.H2.WPQ

set_option autoImplicit false

/-- `Aang α g d z = ∫_θ (D_z^d D_θ g(z,θ) · W(z,θ))²`, the squared angular `L²`-norm (with the
`ℋ⁴` weight `W = w·sin(2θ)^{-γ/2}`) of the mixed slot `D_z^d D_θ g`, at fixed `z`. -/
def Aang (α : ℝ) (g : ℝ → ℝ → ℝ) (d : ℕ) (z : ℝ) : ℝ :=
  ∫ σ in Work.Spaces.Iθ, (Work.Spaces.mixed d 1 g z σ * Work.Spaces.Wt α z σ) ^ 2


/-! ## Elementary facts -/

theorem Aang_nonneg (α : ℝ) (g : ℝ → ℝ → ℝ) (d : ℕ) (z : ℝ) : 0 ≤ Aang α g d z :=
  setIntegral_nonneg measurableSet_Icc fun σ _ => sq_nonneg _

theorem sum_Aang_nonneg (α : ℝ) (g : ℝ → ℝ → ℝ) (z : ℝ) :
    0 ≤ ∑ d ∈ Finset.range 4, Aang α g d z :=
  Finset.sum_nonneg fun d _ => Aang_nonneg α g d z



theorem sin_two_pos_of_Ioo {θ : ℝ} (h : θ ∈ Set.Ioo 0 (π / 2)) : 0 < Real.sin (2 * θ) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [h.1]) (by linarith [h.2, Real.pi_pos])

/-- On the open quadrant, `(W)² = w² sin(2θ)^{-γ}`.  (The exponent bookkeeping is done with
`Real.rpow_add` against the *positive* base `sin(2θ)`.) -/
theorem Wt_sq_of_Ioo (α z θ : ℝ) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    (Work.Spaces.Wt α z θ) ^ 2
      = (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
  have hs : 0 < Real.sin (2 * θ) := sin_two_pos_of_Ioo hθ
  have hstep : ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))) ^ 2
      = (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
    rw [pow_two, ← Real.rpow_add hs]
    congr 1
    ring
  simp only [Work.Spaces.Wt, Work.Spaces.wTheta, mul_pow, hstep]

/-- The `ℋ^k`-integrand vanishes whenever `sin(2θ) = 0`: both weights carry a factor
`sin(2θ)^{c}` with `c > 0` (Lean's totalised `x ^ y` is `0` at `x = 0` for `y ≠ 0`). -/
theorem HkIntegrand_eq_zero_of_sin_two_eq_zero {α : ℝ} (hα : Work.Spaces.gam α ≠ 0)
    {F : ℝ → ℝ → ℝ} {z θ : ℝ} (h : Real.sin (2 * θ) = 0) :
    Work.Spaces.HkIntegrand α 4 F z θ = 0 := by
  have hη : (Work.Spaces.eta / 2 : ℝ) ≠ 0 := by norm_num [Work.Spaces.eta]
  have hg : -(Work.Spaces.gam α / 2) ≠ 0 := by
    intro hc
    exact hα (by linarith [neg_eq_zero.mp hc])
  simp only [Work.Spaces.HkIntegrand, Work.Spaces.Wt, Work.Spaces.wTheta]
  rw [h, Real.zero_rpow hη, Real.zero_rpow hg]
  simp

end Work.FTS.H2.WPQ
end
end
-- ===== merged: Submission.Work.FTS.LocData.integral_sin_two_rpow_neg =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.LocData

/-- The angular singularity `sin(2θ)^{-p}` of the weights is integrable on `Iθ = [0,π/2]`
for `0 < p < 1`, with an explicit bound `100/(1-p)` for its integral.

This is the case `q = -p ∈ (-1,0)` of `Work.Spaces.sin_two_rpow`, which controls
`sin(2θ)^q` on `Iθ` by the endpoint majorant `(π/4)^q (θ^q + (π/2-θ)^q)`. -/
theorem integral_sin_two_rpow_neg (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    MeasureTheory.IntegrableOn (fun θ => (Real.sin (2 * θ)) ^ (-p)) Work.Spaces.Iθ ∧
      ∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-p) ≤ 100 / (1 - p) := by
  have h := Work.Spaces.sin_two_rpow (-p) (by linarith) (by linarith)
  simpa only [neg_add_eq_sub] using h

end Work.FTS.LocData
end
