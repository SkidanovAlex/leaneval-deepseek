/-
# The angular constant `∫_θ 9 K(θ)² sin(2θ)^η ≤ 162`

`K(θ) = 3 sin θ cos²θ` lies in `[0,3]` on the angular interval `Iθ = [0,π/2]`, and
`0 ≤ sin(2θ) ≤ 1` there with `η = 99/100 > 0`; hence the integrand is pointwise `≤ 81`
and the integral is at most `81·|Iθ| = 81·π/2 < 162`.

This is the crude, but sufficient, bound: the sharp value of the integral is
`9 ∫₀^{π/2} sin²θ cos⁴θ dθ = 9·π/32 ≈ 0.88`, so there is a lot of room.  The only
analytic ingredients are `sin ≤ 1`, `sin ≥ 0` on `[0,π]`, `K ≤ 3`, and `π < 4`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityFix.Transfer.E2norm

set_option autoImplicit false

/-- On the angular interval, `sin(2θ) ≥ 0`. -/
private lemma sin_two_nonneg_of_mem {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩

/-- `K(θ) = 3 sin θ cos²θ ≥ 0` on the angular interval. -/
private lemma K_nonneg_of_mem {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Work.Spaces.K θ := by
  have hs : 0 ≤ Real.sin θ :=
    Real.sin_nonneg_of_mem_Icc ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩
  have hc : 0 ≤ Real.cos θ :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos, hθ.1], hθ.2⟩
  rw [Work.Spaces.K]
  positivity

/-- `K(θ) = 3 sin θ cos²θ ≤ 3` on the angular interval. -/
private lemma K_le_three_of_mem {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : Work.Spaces.K θ ≤ 3 := by
  have hs : Real.sin θ ≤ 1 := Real.sin_le_one θ
  have hc : Real.cos θ ^ 2 ≤ 1 := by
    have h := Real.cos_sq_le_one θ
    linarith
  have hs0 : 0 ≤ Real.sin θ :=
    Real.sin_nonneg_of_mem_Icc ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩
  have hc0 : 0 ≤ Real.cos θ ^ 2 := sq_nonneg _
  rw [Work.Spaces.K]
  nlinarith

/-- The pointwise bound: on the angular interval the integrand is at most `81 = 9·3²·1`. -/
private lemma main_le {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    9 * (Work.Spaces.K θ) ^ 2 * (Real.sin (2 * θ)) ^ Work.Spaces.eta ≤ 81 := by
  have hs0 := sin_two_nonneg_of_mem hθ
  have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have hse : (Real.sin (2 * θ)) ^ Work.Spaces.eta ≤ 1 :=
    Real.rpow_le_one hs0 hs1 (le_of_lt Work.Spaces.eta_pos)
  have hse0 : 0 ≤ (Real.sin (2 * θ)) ^ Work.Spaces.eta := Real.rpow_nonneg hs0 _
  have hK0 := K_nonneg_of_mem hθ
  have hK3 := K_le_three_of_mem hθ
  have hK2 : (Work.Spaces.K θ) ^ 2 ≤ 9 := by nlinarith
  calc 9 * (Work.Spaces.K θ) ^ 2 * (Real.sin (2 * θ)) ^ Work.Spaces.eta
      = (9 * (Work.Spaces.K θ) ^ 2) * (Real.sin (2 * θ)) ^ Work.Spaces.eta := by ring
    _ ≤ 81 * 1 := by
        refine mul_le_mul ?_ hse hse0 (by norm_num)
        nlinarith
    _ = 81 := by norm_num

/-- The integral of the constant integrand over the angular interval is `81·π/2 ≤ 162`. -/
private lemma integral_const_le :
    ∫ _θ in Work.Spaces.Iθ, (81 : ℝ) ≤ 162 := by
  rw [Work.Spaces.Iθ, MeasureTheory.setIntegral_const]
  simp
  rw [max_eq_left (by positivity : (0 : ℝ) ≤ Real.pi / 2)]
  nlinarith [Real.pi_lt_four]

/-- **The angular constant of the `E₂`-estimate is at most `162`.** -/
theorem theta_A2_int_le :
    ∫ θ in Work.Spaces.Iθ, 9 * (Work.Spaces.K θ) ^ 2 * (Real.sin (2 * θ)) ^ Work.Spaces.eta ≤ 162 := by
  have hmeas : MeasurableSet Work.Spaces.Iθ := measurableSet_Icc
  have hInt81 : IntegrableOn (fun _ : ℝ => (81 : ℝ)) Work.Spaces.Iθ :=
    integrableOn_const (by rw [Work.Spaces.Iθ, Real.volume_Icc]; simp)
  have hmono : ∫ θ in Work.Spaces.Iθ,
        9 * (Work.Spaces.K θ) ^ 2 * (Real.sin (2 * θ)) ^ Work.Spaces.eta
      ≤ ∫ _θ in Work.Spaces.Iθ, (81 : ℝ) :=
    integral_mono_of_nonneg
      (ae_restrict_of_forall_mem hmeas fun θ hθ =>
        mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _))
          (Real.rpow_nonneg (sin_two_nonneg_of_mem hθ) _))
      hInt81
      (ae_restrict_of_forall_mem hmeas fun θ hθ => main_le hθ)
  linarith [hmono, integral_const_le]

end Work.FTS.CoercivityFix.Transfer.E2norm
