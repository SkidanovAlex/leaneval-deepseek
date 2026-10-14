import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.H2.T1Q.IbpCutoff
import Submission.Work.Spaces.sin_two_rpow

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology BigOperators
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Series

set_option autoImplicit false

/-! ## Elementary helpers -/



/-- The angular eigenfunctions are `C³`. -/
lemma contDiff_eFam (m : ℕ) : ContDiff ℝ 3 (Gegenbauer.eFam m) := by
  have h1 : ContDiff ℝ 3 (fun θ : ℝ => Gegenbauer.gC (2 * m + 1) (Real.sin θ)) :=
    (Gegenbauer.contDiff_gC (2 * m + 1)).comp Real.contDiff_sin
  have h2 : ContDiff ℝ 3 (fun θ : ℝ => Real.cos θ) := Real.contDiff_cos
  exact h2.mul h1

/-! ## Differentiation of finite sums of separable terms -/


/-- `∂_θ` of a finite sum of separable terms. -/
theorem deriv_sum_sep_theta (s : Finset ℕ) (b e : ℕ → ℝ → ℝ) (z θ : ℝ)
    (he : ∀ m ∈ s, DifferentiableAt ℝ (e m) θ) :
    deriv (fun θ' : ℝ => ∑ m ∈ s, b m z * e m θ') θ = ∑ m ∈ s, b m z * deriv (e m) θ := by
  have hfun : (fun θ' : ℝ => ∑ m ∈ s, b m z * e m θ')
      = ∑ m ∈ s, (fun θ' : ℝ => b m z * e m θ') := by
    funext θ'; rw [Finset.sum_apply]
  rw [hfun, deriv_sum (fun m hm => (he m hm).const_mul (b m z))]
  exact Finset.sum_congr rfl fun m hm => deriv_const_mul (b m z) (he m hm)

/-- `∂_θ(tan θ · ·)` of a finite sum of separable terms. -/
theorem deriv_sum_tan_sep (s : Finset ℕ) (b e : ℕ → ℝ → ℝ) (z θ : ℝ)
    (hcos : Real.cos θ ≠ 0) (he : ∀ m ∈ s, DifferentiableAt ℝ (e m) θ) :
    deriv (fun θ' : ℝ => Real.tan θ' * (∑ m ∈ s, b m z * e m θ')) θ
      = ∑ m ∈ s, b m z * deriv (fun θ' : ℝ => Real.tan θ' * e m θ') θ := by
  have htan : DifferentiableAt ℝ Real.tan θ := Real.differentiableAt_tan.mpr hcos
  have hfun : (fun θ' : ℝ => Real.tan θ' * (∑ m ∈ s, b m z * e m θ'))
      = ∑ m ∈ s, (fun θ' : ℝ => Real.tan θ' * (b m z * e m θ')) := by
    funext θ'
    rw [Finset.sum_apply, Finset.mul_sum]
  have hstep : deriv (∑ m ∈ s, (fun θ' : ℝ => Real.tan θ' * (b m z * e m θ'))) θ
      = ∑ m ∈ s, deriv (fun θ' : ℝ => Real.tan θ' * (b m z * e m θ')) θ :=
    deriv_sum (fun m hm => htan.mul ((he m hm).const_mul (b m z)))
  rw [hfun, hstep]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [show (fun θ' : ℝ => Real.tan θ' * (b m z * e m θ'))
      = fun θ' : ℝ => b m z * (Real.tan θ' * e m θ') from by funext θ'; ring]
  exact deriv_const_mul (b m z) (htan.mul (he m hm))


/-- `∂_θθ` of a finite sum of separable terms. -/
theorem pthIter_two_sum_sep (s : Finset ℕ) (b e : ℕ → ℝ → ℝ) (z θ : ℝ)
    (he : ∀ m ∈ s, ∀ θ' : ℝ, DifferentiableAt ℝ (e m) θ')
    (he1 : ∀ m ∈ s, DifferentiableAt ℝ (deriv (e m)) θ) :
    Work.Spaces.pthIter 2 (fun z' θ' => ∑ m ∈ s, b m z' * e m θ') z θ
      = ∑ m ∈ s, b m z * deriv (deriv (e m)) θ := by
  have hev : (fun θ' : ℝ => Work.Spaces.pth (fun z' θ' => ∑ m ∈ s, b m z' * e m θ') z θ')
      =ᶠ[𝓝 θ] fun θ' : ℝ => ∑ m ∈ s, b m z * deriv (e m) θ' := by
    filter_upwards with θ'
    exact deriv_sum_sep_theta s b e z θ' (fun m hm => he m hm θ')
  change deriv (fun θ' : ℝ => Work.Spaces.pth (fun z' θ' => ∑ m ∈ s, b m z' * e m θ') z θ') θ
    = ∑ m ∈ s, b m z * deriv (deriv (e m)) θ
  rw [hev.deriv_eq]
  exact deriv_sum_sep_theta s b (fun m => deriv (e m)) z θ (fun m hm => he1 m hm)

/-- `∂_θ(tan θ · ·)` of a finite sum of separable terms, in `Work.Spaces.pth` form. -/
theorem pth_tan_sum_sep (s : Finset ℕ) (b e : ℕ → ℝ → ℝ) (z θ : ℝ)
    (hcos : Real.cos θ ≠ 0) (he : ∀ m ∈ s, DifferentiableAt ℝ (e m) θ) :
    Work.Spaces.pth (fun z' θ' => Real.tan θ' * (∑ m ∈ s, b m z' * e m θ')) z θ
      = ∑ m ∈ s, b m z * deriv (fun θ' : ℝ => Real.tan θ' * e m θ') θ := by
  show deriv (fun θ' : ℝ => Real.tan θ' * (∑ m ∈ s, b m z * e m θ')) θ = _
  exact deriv_sum_tan_sep s b e z θ hcos he


/-! ## The truncated series solves the truncated equation -/


end Work.FTS.PhiStar.Series
