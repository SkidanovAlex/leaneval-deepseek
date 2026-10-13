import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.Order.Interval.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.Defs
import Submission.Work.FTS.EllipticEst.StraightDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology Interval
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.H2W.Ae

set_option autoImplicit false

/-!
# Elementary facts about the weight `sEta θ = sin(2θ)^{-η}` (`η = 99/100`)

These are the pointwise and measurability facts used by the proof that a weighted `L²` bound
on `f''` forces `f` to be bounded on `(0, π/2)` with one-sided limits at both endpoints.
-/

lemma sin_two_nonneg_of_mem_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Real.sin (2 * θ) := by
  rw [Work.Spaces.Iθ] at hθ
  exact Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1],
    by linarith [hθ.2, Real.pi_pos]⟩

lemma sEta_nonneg_of_mem_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ sEta θ := by
  rw [Work.FTS.EllipticEst.sEta]
  exact Real.rpow_nonneg (sin_two_nonneg_of_mem_Iθ hθ) _

/-- `sEta θ = sin(2θ)^{-η} ≥ 1` on the open interval. -/
lemma one_le_sEta {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) : 1 ≤ sEta θ := by
  rw [Work.FTS.EllipticEst.sEta]
  have h0 : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have h1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have h2 : -(Work.Spaces.eta) ≤ 0 := by
    rw [Work.Spaces.eta]; norm_num
  calc (1 : ℝ) = 1 ^ (-(Work.Spaces.eta)) := by rw [Real.one_rpow]
    _ ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
        Real.rpow_le_rpow_of_nonpos h0 h1 h2

lemma measurable_sEta : Measurable sEta :=
  (Real.measurable_sin.comp (by fun_prop : Measurable fun θ : ℝ => 2 * θ)).pow measurable_const

/-- The weighted square of the second derivative is measurable. -/
lemma measurable_secDeriv_sq (f : ℝ → ℝ) :
    Measurable (fun θ : ℝ => ((deriv (deriv f)) θ) ^ 2 * sEta θ) :=
  ((measurable_deriv (deriv f)).pow measurable_const).mul measurable_sEta

/-- The pointwise AM–GM inequality which converts the weighted `L²` bound into an `L¹`
bound on the second derivative. -/
lemma two_mul_abs_le_sq_mul_sEta_add_one (x θ : ℝ) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    2 * |x| ≤ x ^ 2 * sEta θ + 1 := by
  have h1 : 1 ≤ sEta θ := one_le_sEta hθ
  have h2 : 0 ≤ |x| ^ 2 * (sEta θ - 1) := mul_nonneg (sq_nonneg _) (by linarith)
  have h3 : 0 ≤ (|x| - 1) ^ 2 := sq_nonneg _
  rw [sq_abs] at h2
  nlinarith [abs_nonneg x, sq_abs x, h2, h3]

end Work.FTS.EllipticEst.H2W.Ae
