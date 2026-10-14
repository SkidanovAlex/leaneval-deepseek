import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS_RegExport.RXT.contDiffOn_two_integral_Itheta
import Submission.Work.Spaces.pz_mixed_mul_le_4
import Submission.Work.Spaces.sq_mul_div_rpow
-- ===== merged: Submission.Work.FTS.EllipticEst.GfunContDiff =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst

/-- Helper: `θ ↦ Real.cos (2 * θ)` is smooth. -/
theorem contDiff_cos_two : ContDiff ℝ ⊤ (fun θ : ℝ => Real.cos (2 * θ)) :=
  Real.contDiff_cos.comp (contDiff_const.mul contDiff_id)

/-- Helper: `θ ↦ Real.sin (2 * θ)` is smooth. -/
theorem contDiff_sin_two : ContDiff ℝ ⊤ (fun θ : ℝ => Real.sin (2 * θ)) :=
  Real.contDiff_sin.comp (contDiff_const.mul contDiff_id)

/-- Helper: the function `θ ↦ c * Real.cos (2 * θ)` is smooth. -/
theorem contDiff_const_mul_cos_two (c : ℝ) :
    ContDiff ℝ ⊤ (fun θ : ℝ => c * Real.cos (2 * θ)) :=
  contDiff_const.mul contDiff_cos_two

/-- Every coefficient `gfun n` of the recursion `gfun 0 = 1`,
`gfun (n+1) θ = 4 cos(2θ) gfun n θ + sin(2θ) (gfun n)'(θ)` is smooth on `ℝ`. -/
theorem GfunContDiff (n : ℕ) : ContDiff ℝ ⊤ (Work.FTS.EllipticEst.gfun n) := by
  induction n with
  | zero => exact contDiff_const
  | succ n ih =>
      rw [gfun_succ]
      have hd : ContDiff ℝ ⊤ (deriv (gfun n)) := ContDiff.deriv' ih
      exact ContDiff.add ((contDiff_const_mul_cos_two 4).mul ih) (contDiff_sin_two.mul hd)

end Work.FTS.EllipticEst
end
-- ===== merged: Submission.Work.FTS_RegExport.RXT.Slots.v2_paramC2 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-! A copy of `v2_contDiffOn_two_integral_Itheta` under a namespace-local name, used by the
copy `Slots.v2_velPert` of the perturbation producer. -/

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_RegExport.RXT.Slots

theorem v2_paramC2 {F : ℝ → ℝ → ℝ} {φ : ℝ → ℝ} {C : ℝ}
    (hφ : ContinuousOn φ Work.Spaces.Iθ)
    (hF : ContDiffOn ℝ 2 (Function.uncurry F) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hb : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |F z θ| ≤ C ∧ |Work.Spaces.Dz F z θ| ≤ C ∧ |Work.Spaces.DzIter 2 F z θ| ≤ C) :
    ContDiffOn ℝ 2 (fun z => ∫ θ in Work.Spaces.Iθ, F z θ * φ θ) (Set.Ioi 0) :=
  Work.FTS_RegExport.RXT.contDiffOn_two_integral_Itheta hφ hF hb

end Work.FTS_RegExport.RXT.Slots
end
end
