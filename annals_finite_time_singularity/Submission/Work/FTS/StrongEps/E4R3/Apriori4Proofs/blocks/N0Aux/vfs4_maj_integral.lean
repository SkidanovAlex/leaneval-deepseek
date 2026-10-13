import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Coercivity.integral_sin_two_neg_rpow_le
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N0Aux

open scoped Real
open MeasureTheory

theorem vfs4_maj_integral {A Bm α : ℝ} (hA : 0 ≤ A) (hBm : 0 ≤ Bm)
    (hα : 0 < α) (hα1 : α ≤ 1) :
    MeasureTheory.IntegrableOn
        (fun θ : ℝ => A * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
          + Bm * (Real.sin (2 * θ)) ^ (-(1 - 17 * α / 30))) Work.Spaces.Iθ ∧
      (∫ θ in Work.Spaces.Iθ,
          (A * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
            + Bm * (Real.sin (2 * θ)) ^ (-(1 - 17 * α / 30))))
        ≤ A * 400 + Bm * (120 / (17 * α)) := by
  have hEta := Work.Coercivity.integral_sin_two_neg_rpow_le Work.Spaces.eta
      Work.Spaces.eta_pos Work.Spaces.eta_lt_one
  have hq0 : 0 < 1 - 17 * α / 30 := by linarith
  have hq1 : 1 - 17 * α / 30 < 1 := by linarith
  have hQ := Work.Coercivity.integral_sin_two_neg_rpow_le (1 - 17 * α / 30) hq0 hq1
  have hIntA : MeasureTheory.IntegrableOn
      (fun θ : ℝ => A * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) Work.Spaces.Iθ :=
    hEta.1.const_mul A
  have hIntB : MeasureTheory.IntegrableOn
      (fun θ : ℝ => Bm * (Real.sin (2 * θ)) ^ (-(1 - 17 * α / 30))) Work.Spaces.Iθ :=
    hQ.1.const_mul Bm
  have e1 : (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) ≤ 400 := by
    refine le_trans hEta.2 ?_
    norm_num [Work.Spaces.eta]
  have e2 : (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(1 - 17 * α / 30)))
      ≤ 120 / (17 * α) := by
    have hpos : (0 : ℝ) < 17 * α / 30 := by positivity
    have hpos' : (0 : ℝ) < 17 * α := by positivity
    have key : 4 / (1 - (1 - 17 * α / 30)) ≤ 120 / (17 * α) := by
      rw [show 1 - (1 - 17 * α / 30) = 17 * α / 30 by ring]
      rw [div_le_div_iff₀ hpos hpos']
      ring_nf
      linarith
    exact le_trans hQ.2 key
  refine ⟨hIntA.add hIntB, ?_⟩
  rw [integral_add hIntA hIntB, integral_const_mul, integral_const_mul]
  exact add_le_add (mul_le_mul_of_nonneg_left e1 hA) (mul_le_mul_of_nonneg_left e2 hBm)

end Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N0Aux
