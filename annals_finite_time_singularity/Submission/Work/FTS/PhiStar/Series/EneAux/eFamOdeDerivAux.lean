import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Submission.Work.FTS.PhiStar.Series.eFamEneDefs
import Submission.Work.FTS.PhiStar.Gegenbauer.eFam_Lzero

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real

namespace Work.FTS.PhiStar.Series.EneAux

set_option autoImplicit false

/-- The product rule for `θ ↦ cos θ * g θ`. -/
lemma deriv_cos_mul_apply (g : ℝ → ℝ) (θ : ℝ) (hg : DifferentiableAt ℝ g θ) :
    deriv (fun θ' => Real.cos θ' * g θ') θ = -Real.sin θ * g θ + Real.cos θ * deriv g θ := by
  rw [show (fun θ' => Real.cos θ' * g θ') = Real.cos * g from by
    funext θ'
    rw [Pi.mul_apply]]
  rw [deriv_mul Real.differentiableAt_cos hg, Real.deriv_cos]

/-- The Sturm–Liouville form of the `θ`-equation of the Gegenbauer family `eFam m`: for
`cos θ ≠ 0`,

  `(cos θ · (eFam m)')' = (1 / cos θ - eM m · cos θ) · eFam m θ`.

Both sides are `cos θ` times the Gegenbauer equation
`(1 - s²) q'' - 4 s q' + n(n+3) q = 0` (`gC_ode`, `q = gC (2m+1)`, `n = 2m+1`, `s = sin θ`),
using `eM m = n(n+3) + 2` and `sin² + cos² = 1`. -/
theorem eFamOdeDerivAux (m : ℕ) :
    ∀ θ : ℝ, Real.cos θ ≠ 0 →
      deriv (fun θ' => Real.cos θ' * deriv (Work.FTS.PhiStar.Gegenbauer.eFam m) θ') θ
        = (1 / Real.cos θ - Work.FTS.PhiStar.Series.eM m * Real.cos θ)
            * Work.FTS.PhiStar.Gegenbauer.eFam m θ := by
  intro θ hθ
  have hq : ContDiff ℝ 3 (Work.FTS.PhiStar.Gegenbauer.gC (2 * m + 1)) :=
    Work.FTS.PhiStar.Gegenbauer.contDiff_gC _
  have heFam : Work.FTS.PhiStar.Gegenbauer.eFam m
      = fun θ' : ℝ => Real.cos θ' * Work.FTS.PhiStar.Gegenbauer.gC (2 * m + 1) (Real.sin θ') := by
    funext θ'
    simp only [Work.FTS.PhiStar.Gegenbauer.eFam]
  have hderiv1 : deriv (Work.FTS.PhiStar.Gegenbauer.eFam m) θ
      = -Real.sin θ * Work.FTS.PhiStar.Gegenbauer.gC (2 * m + 1) (Real.sin θ)
        + Real.cos θ ^ 2 * deriv (Work.FTS.PhiStar.Gegenbauer.gC (2 * m + 1)) (Real.sin θ) := by
    rw [heFam]
    exact congrFun (Work.FTS.PhiStar.Gegenbauer.deriv_cos_comp_sin
      (Work.FTS.PhiStar.Gegenbauer.gC (2 * m + 1)) hq) θ
  have hderiv2 : deriv (deriv (Work.FTS.PhiStar.Gegenbauer.eFam m)) θ
      = -Real.cos θ * Work.FTS.PhiStar.Gegenbauer.gC (2 * m + 1) (Real.sin θ)
        - 3 * Real.sin θ * Real.cos θ
            * deriv (Work.FTS.PhiStar.Gegenbauer.gC (2 * m + 1)) (Real.sin θ)
        + Real.cos θ ^ 3
            * deriv (deriv (Work.FTS.PhiStar.Gegenbauer.gC (2 * m + 1))) (Real.sin θ) := by
    rw [heFam]
    exact Work.FTS.PhiStar.Gegenbauer.deriv2_cos_comp_sin
      (Work.FTS.PhiStar.Gegenbauer.gC (2 * m + 1)) hq θ
  have hcd : ContDiff ℝ 3 (Work.FTS.PhiStar.Gegenbauer.eFam m) := by
    rw [heFam]
    exact Real.contDiff_cos.mul (hq.comp Real.contDiff_sin)
  have hdiff : DifferentiableAt ℝ (deriv (Work.FTS.PhiStar.Gegenbauer.eFam m)) θ :=
    ((ContDiff.deriv' (n := 2) hcd).differentiable (by norm_num)).differentiableAt
  have hM : Work.FTS.PhiStar.Series.eM m
      = ((2 * m + 1 : ℕ) : ℝ) * (((2 * m + 1 : ℕ) : ℝ) + 3) + 2 := by
    unfold Work.FTS.PhiStar.Series.eM
    push_cast
    ring
  have hval : Work.FTS.PhiStar.Gegenbauer.eFam m θ
      = Real.cos θ * Work.FTS.PhiStar.Gegenbauer.gC (2 * m + 1) (Real.sin θ) := by
    simp only [Work.FTS.PhiStar.Gegenbauer.eFam]
  rw [deriv_cos_mul_apply (deriv (Work.FTS.PhiStar.Gegenbauer.eFam m)) θ hdiff,
    hderiv1, hderiv2, hM, hval]
  have hode := (Work.FTS.PhiStar.Gegenbauer.gC_ode (2 * m + 1)).2 (Real.sin θ)
  have hsq : Real.sin θ ^ 2 + Real.cos θ ^ 2 = 1 := Real.sin_sq_add_cos_sq θ
  have hcos2 : (1 : ℝ) - Real.sin θ ^ 2 = Real.cos θ ^ 2 := by linarith
  have hode2 : Real.cos θ ^ 2
        * deriv (deriv (Work.FTS.PhiStar.Gegenbauer.gC (2 * m + 1))) (Real.sin θ)
      - 4 * Real.sin θ * deriv (Work.FTS.PhiStar.Gegenbauer.gC (2 * m + 1)) (Real.sin θ)
      + ((2 * m + 1 : ℕ) : ℝ) * (((2 * m + 1 : ℕ) : ℝ) + 3)
          * Work.FTS.PhiStar.Gegenbauer.gC (2 * m + 1) (Real.sin θ) = 0 := by
    rw [hcos2] at hode
    exact hode
  have hR1 : (1 / Real.cos θ
        - (((2 * m + 1 : ℕ) : ℝ) * (((2 * m + 1 : ℕ) : ℝ) + 3) + 2) * Real.cos θ)
        * (Real.cos θ * Work.FTS.PhiStar.Gegenbauer.gC (2 * m + 1) (Real.sin θ))
      = (1 - (((2 * m + 1 : ℕ) : ℝ) * (((2 * m + 1 : ℕ) : ℝ) + 3) + 2) * Real.cos θ ^ 2)
          * Work.FTS.PhiStar.Gegenbauer.gC (2 * m + 1) (Real.sin θ) := by
    have h1 : (1 / Real.cos θ)
        * (Real.cos θ * Work.FTS.PhiStar.Gegenbauer.gC (2 * m + 1) (Real.sin θ))
        = Work.FTS.PhiStar.Gegenbauer.gC (2 * m + 1) (Real.sin θ) := by
      rw [one_div, ← mul_assoc, inv_mul_cancel₀ hθ, one_mul]
    rw [sub_mul, h1]
    ring
  rw [hR1]
  linear_combination (Real.cos θ ^ 2) * hode2
    + (Work.FTS.PhiStar.Gegenbauer.gC (2 * m + 1) (Real.sin θ)) * hsq

end Work.FTS.PhiStar.Series.EneAux
