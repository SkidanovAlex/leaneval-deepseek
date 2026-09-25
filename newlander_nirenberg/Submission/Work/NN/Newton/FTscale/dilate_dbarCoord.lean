import Mathlib
import Submission.Work.NN.Newton.FTdefs

namespace Work.NN.Newton.FTscale

/-- `∂̄` of a constant multiple, with no differentiability hypothesis: both sides
vanish (or are computed by `fderiv_const_mul`) according to whether the function
is differentiable at the point. -/
lemma dbarCoord_const_mul_gen {n : ℕ} (a : Fin n) (c : ℂ) (u : (Fin n → ℂ) → ℂ)
    (z : Fin n → ℂ) :
    Work.CR.Flat.dbarCoord a (fun z => c * u z) z = c * Work.CR.Flat.dbarCoord a u z := by
  by_cases hc : c = 0
  · rw [hc]
    simp [Work.CR.Flat.dbarCoord]
  · by_cases hu : DifferentiableAt ℝ u z
    · rw [Work.CR.Flat.dbarCoord, Work.CR.Flat.dbarCoord, fderiv_const_mul hu c]
      simp only [smul_apply, smul_eq_mul]
      ring
    · have hnot : ¬ DifferentiableAt ℝ (fun z => c * u z) z := by
        intro h
        apply hu
        have h2 : DifferentiableAt ℝ (fun y => c⁻¹ * (c * u y)) z := h.const_mul c⁻¹
        convert h2 using 1
        funext y
        field_simp
      rw [Work.CR.Flat.dbarCoord, Work.CR.Flat.dbarCoord,
        fderiv_zero_of_not_differentiableAt hnot, fderiv_zero_of_not_differentiableAt hu]
      simp only [zero_apply]
      ring

theorem dilate_dbarCoord {n : ℕ} {lam : ℝ} (hlam : 0 < lam) (a : Fin n) {c : ℂ}
    (f : (Fin n → ℂ) → ℂ) (z : Fin n → ℂ) :
    Work.CR.Flat.dbarCoord a (fun z : Fin n → ℂ => c * f (lam • z)) z
      = c * (lam : ℂ) * Work.CR.Flat.dbarCoord a f (lam • z) := by
  have _h : 0 < lam := hlam
  rw [dbarCoord_const_mul_gen a c (fun w => f (lam • w)) z,
    Work.NN.Newton.dbarCoord_comp_smul a lam f z]
  ring

end Work.NN.Newton.FTscale
