import Mathlib.Algebra.Order.Ring.Star
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.H2W.Ae.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.ThetaPoincareDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Prop.Ang2

open MeasureTheory Set Filter
open scoped Real Topology

set_option autoImplicit false

/-- `HkIntegrand` is independent of `α` at level `0`. -/
theorem HkIntegrand_zero_eq (α : ℝ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.HkIntegrand α 0 f z θ = Work.Spaces.HkIntegrand 1 0 f z θ := by
  simp only [Work.Spaces.HkIntegrand]
  norm_num

theorem HkSq_zero_eq (α : ℝ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.HkSq α 0 f = Work.Spaces.HkSq 1 0 f := by
  rw [Work.Spaces.HkSq, Work.Spaces.HkSq]
  exact setIntegral_congr_fun measurableSet_Ici
    (fun z _ => setIntegral_congr_fun measurableSet_Icc (fun θ _ => HkIntegrand_zero_eq α f z θ))

theorem HkMem_zero_iff (α : ℝ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.HkMem α 0 f ↔ Work.Spaces.HkMem 1 0 f := by
  constructor
  · intro h
    refine ⟨fun z hz => ?_, ?_⟩
    · exact (h.1 z hz).congr_fun (fun θ _ => HkIntegrand_zero_eq α f z θ) measurableSet_Icc
    · refine h.2.congr_fun (fun z _ => ?_) measurableSet_Ici
      exact setIntegral_congr_fun measurableSet_Icc (fun θ _ => HkIntegrand_zero_eq α f z θ)
  · intro h
    refine ⟨fun z hz => ?_, ?_⟩
    · exact (h.1 z hz).congr_fun (fun θ _ => (HkIntegrand_zero_eq α f z θ).symm) measurableSet_Icc
    · refine h.2.congr_fun (fun z _ => ?_) measurableSet_Ici
      exact setIntegral_congr_fun measurableSet_Icc (fun θ _ => (HkIntegrand_zero_eq α f z θ).symm)

end Work.FTS.EllipticEst.Prop.Ang2
