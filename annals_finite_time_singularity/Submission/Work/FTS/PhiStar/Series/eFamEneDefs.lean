import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Submission.Work.FTS.PhiStar.RadGreenSupport.ibp_upper
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.Spaces.sq_mul_div_rpow

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real

namespace Work.FTS.PhiStar.Series

set_option autoImplicit false

/-- `M = (n+1)(n+2)` for `n = 2m+1`, i.e. `M = (2m+2)(2m+3)`; the spectral constant of the
`θ`-equation of `eFam m`. -/
def eM (m : ℕ) : ℝ := (2 * (m : ℝ) + 2) * (2 * (m : ℝ) + 3)



/-- The energy of `eFam m`:
`eEne m θ = cos θ f'² - sin θ f f' + (M cos θ - 1/(2 cos θ)) f²`, `f = eFam m`. -/
def eEne (m : ℕ) (θ : ℝ) : ℝ :=
  Real.cos θ * (deriv (Work.FTS.PhiStar.Gegenbauer.eFam m) θ) ^ 2
    - Real.sin θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ
        * deriv (Work.FTS.PhiStar.Gegenbauer.eFam m) θ
    + (eM m * Real.cos θ - 1 / (2 * Real.cos θ))
        * (Work.FTS.PhiStar.Gegenbauer.eFam m θ) ^ 2

/-- `gC (2m+1) 0 = 0`: the odd Gegenbauer polynomials vanish at the origin. -/
lemma gC_odd_zero (m : ℕ) : Work.FTS.PhiStar.Gegenbauer.gC (2 * m + 1) 0 = 0 := by
  induction m with
  | zero => rw [show Work.FTS.PhiStar.Gegenbauer.gC 1
        = (fun x : ℝ => 3 * x) from rfl]; norm_num
  | succ m ih =>
    have h := Work.FTS.PhiStar.Gegenbauer.gC_rec (2 * m + 1) 0
    have h1 : (2 * m + 1) + 2 = 2 * (m + 1) + 1 := by omega
    rw [h1] at h
    have h3 : (((2 * m + 1 : ℕ) : ℝ) + 3) * Work.FTS.PhiStar.Gegenbauer.gC (2 * m + 1) 0
        = 0 := by rw [ih]; ring
    simp only [mul_zero, zero_mul] at h
    rw [h3, sub_zero] at h
    have hne : (((2 * m + 1 : ℕ) : ℝ) + 2) ≠ 0 := by positivity
    exact (mul_eq_zero.mp h).resolve_left hne

/-- `eFam m 0 = 0`. -/
lemma eFam_zero (m : ℕ) : Work.FTS.PhiStar.Gegenbauer.eFam m 0 = 0 := by
  rw [Work.FTS.PhiStar.Gegenbauer.eFam]
  simp only [Real.cos_zero, Real.sin_zero]
  simpa using gC_odd_zero m

/-- `eFam m (π/2) = 0`. -/
lemma eFam_pi_half (m : ℕ) : Work.FTS.PhiStar.Gegenbauer.eFam m (Real.pi / 2) = 0 := by
  rw [Work.FTS.PhiStar.Gegenbauer.eFam, Real.cos_pi_div_two, zero_mul]

/-- `eFam m` is continuous (indeed smooth): `gC (2m+1)` is a polynomial. -/
lemma continuous_eFam (m : ℕ) : Continuous (Work.FTS.PhiStar.Gegenbauer.eFam m) := by
  rw [show Work.FTS.PhiStar.Gegenbauer.eFam m
      = (fun θ : ℝ => Real.cos θ
          * Work.FTS.PhiStar.Gegenbauer.gC (2 * m + 1) (Real.sin θ)) from rfl]
  exact Real.continuous_cos.mul
    ((Work.FTS.PhiStar.Gegenbauer.contDiff_gC (2 * m + 1)).continuous.comp Real.continuous_sin)

/-- `eFam m` is differentiable everywhere. -/
lemma differentiable_eFam (m : ℕ) : Differentiable ℝ (Work.FTS.PhiStar.Gegenbauer.eFam m) := by
  have h := (Work.FTS.PhiStar.Gegenbauer.contDiff_gC (2 * m + 1)).differentiable (by norm_num)
  rw [show Work.FTS.PhiStar.Gegenbauer.eFam m
      = (fun θ : ℝ => Real.cos θ
          * Work.FTS.PhiStar.Gegenbauer.gC (2 * m + 1) (Real.sin θ)) from rfl]
  exact Real.differentiable_cos.mul (h.comp Real.differentiable_sin)

end Work.FTS.PhiStar.Series
