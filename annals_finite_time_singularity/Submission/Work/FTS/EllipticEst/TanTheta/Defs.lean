/-
Copyright: work module for the Elgindi finite-time singularity project.

# The weights of the `∂_θ(tan θ Ψ)` estimate

Definitions shared by the proof of `Work.FTS.EllipticEst.tanTheta_bound` and its auxiliary
lemmas: the angular weight `qEta θ = sin(2θ)^{-η}` (the square of the weight
`Wg z θ = w z / sin(2θ)^{η/2}` used in the statement), and the combination
`Acoef θ = ((1-η)/2)·cos 2θ + 2 sin²θ` of the paper's `I₄`-identity, together with the
elementary algebraic facts about them.

Nothing here contains a `sorry`; the module is imported both by the proof of the main theorem
and by the auxiliary slice lemmas (which must not inherit `sorryAx`).
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
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

set_option autoImplicit false
set_option linter.unusedSimpArgs false

/-- The angular weight `qEta θ = sin(2θ)^{-η}` with `η = 99/100`: the square of the weight
`w z / sin(2θ)^{η/2}` appearing in the statement of `tanTheta_bound`. -/
def qEta (θ : ℝ) : ℝ := (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))

/-- The product weight `Wg z θ = w z / sin(2θ)^{η/2}` of the statement of `tanTheta_bound`. -/
abbrev Wg (z θ : ℝ) : ℝ := Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)

/-- The coefficient `Acoef θ = ((1-η)/2)·cos 2θ + 2 sin²θ` of the `I₄`-identity.  It is
positive, and dominates `((1-η)/2)·sin²θ`. -/
def Acoef (θ : ℝ) : ℝ :=
  ((1 - Work.Spaces.eta) / 2) * Real.cos (2 * θ) + 2 * (Real.sin θ) ^ 2

theorem sin_two_nonneg {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

theorem qEta_nonneg {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ qEta θ :=
  Real.rpow_nonneg (sin_two_nonneg hθ) _

theorem sin_two_pos {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) : 0 < Real.sin (2 * θ) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

theorem Wg_nonneg {z θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Wg z θ :=
  div_nonneg (by rw [Work.Spaces.w]; positivity)
    (Real.rpow_nonneg (sin_two_nonneg hθ) _)

/-- The square of the product weight is `w²·qEta`, on the angular interval. -/
theorem Wg_sq {z θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    Wg z θ ^ 2 = Work.Spaces.w z ^ 2 * qEta θ := by
  have hs : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg hθ
  have h2 : ((Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2
      = (Real.sin (2 * θ)) ^ (Work.Spaces.eta) := by
    rcases eq_or_lt_of_le hs with h | h
    · have hη2 : (0:ℝ) < Work.Spaces.eta / 2 := by rw [Work.Spaces.eta]; norm_num
      have hη : (0:ℝ) < Work.Spaces.eta := by rw [Work.Spaces.eta]; norm_num
      rw [← h, Real.zero_rpow (ne_of_gt hη2), Real.zero_rpow (ne_of_gt hη)]
      ring
    · rw [sq, ← Real.rpow_add h (Work.Spaces.eta / 2) (Work.Spaces.eta / 2),
        show Work.Spaces.eta / 2 + Work.Spaces.eta / 2 = Work.Spaces.eta by ring]
  rw [Wg, div_pow, h2, qEta, Real.rpow_neg hs, div_eq_mul_inv]
  try ring

theorem Acoef_lower (θ : ℝ) :
    ((1 - Work.Spaces.eta) / 2) * (Real.sin θ) ^ 2 ≤ Acoef θ := by
  have hc : Real.cos (2 * θ) = 2 * (Real.cos θ) ^ 2 - 1 := Real.cos_two_mul θ
  have h1 : (Real.cos θ) ^ 2 + (Real.sin θ) ^ 2 = 1 := Real.cos_sq_add_sin_sq θ
  have he : Work.Spaces.eta = 99 / 100 := rfl
  rw [Acoef, hc]
  nlinarith [sq_nonneg (Real.sin θ), sq_nonneg (Real.cos θ), h1, he]

theorem sub_eta_half_le_Acoef (θ : ℝ) : (1 - Work.Spaces.eta) / 2 ≤ Acoef θ := by
  have hc : Real.cos (2 * θ) = 1 - 2 * (Real.sin θ) ^ 2 := by
    have h1 := Real.cos_sq_add_sin_sq θ
    have h2 := Real.cos_two_mul' θ
    linarith [h1, h2]
  have he : Work.Spaces.eta = 99 / 100 := rfl
  rw [Acoef, hc]
  nlinarith [sq_nonneg (Real.sin θ), he]

theorem Acoef_nonneg (θ : ℝ) : 0 ≤ Acoef θ :=
  le_trans (mul_nonneg (by norm_num [Work.Spaces.eta]) (sq_nonneg _)) (Acoef_lower θ)

theorem Acoef_le_two (θ : ℝ) : Acoef θ ≤ 2 := by
  have hc : Real.cos (2 * θ) = 2 * (Real.cos θ) ^ 2 - 1 := Real.cos_two_mul θ
  have h1 : (Real.cos θ) ^ 2 + (Real.sin θ) ^ 2 = 1 := Real.cos_sq_add_sin_sq θ
  have he : Work.Spaces.eta = 99 / 100 := rfl
  rw [Acoef, hc]
  nlinarith [sq_nonneg (Real.sin θ), sq_nonneg (Real.cos θ), h1, he]

theorem one_sub_eta_pos : 0 < 1 - Work.Spaces.eta := by
  rw [Work.Spaces.eta]; norm_num

theorem one_sub_eta_pos' : 0 < (1 - Work.Spaces.eta) / 2 := by
  have := one_sub_eta_pos; linarith

end Work.FTS.EllipticEst
