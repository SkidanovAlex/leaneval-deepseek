import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.Spaces.dthU_Gam
import Submission.Work.Spaces.mixed_mul_le
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.StabilityFar.Profile.exists_Fstar_add_ge

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

/-! ## Slices of a `SmoothNbhd` function -/



/-! ## Identifications of the operators -/


/-- `LopIter` applied to a slice is the corresponding `D_θ`-iterate of the two-variable
function. -/
lemma LopIter_slice (i : ℕ) (g : ℝ → ℝ → ℝ) (z : ℝ) :
    LopIter i (fun θ => g z θ) = fun θ => Work.Spaces.DthIter i g z θ := by
  funext θ
  show (Work.Spaces.Lop^[i]) (fun θ => g z θ) θ = Work.Spaces.DthIter i g z θ
  rw [← Work.Spaces.DthIter_eq_iterate_Lop i g z]



/-! ## The weight identifications -/

lemma w_div_sin_sq {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) (z : ℝ) :
    (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2
      = (Work.Spaces.w z) ^ 2 * thEta θ := by
  have hs : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg hθ
  have h1 : ((Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2
      = (Real.sin (2 * θ)) ^ (Work.Spaces.eta) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hs]
    norm_num
  have h2 : (thEta θ)⁻¹ = (Real.sin (2 * θ)) ^ (Work.Spaces.eta) := by
    rw [thEta, Real.rpow_neg hs, inv_inv]
  rw [div_pow, h1, div_eq_mul_inv, ← h2, inv_inv]

lemma Wt_sq {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) (α z : ℝ) :
    (Work.Spaces.Wt α z θ) ^ 2 = (Work.Spaces.w z) ^ 2 * thGam α θ := by
  have hs : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg hθ
  have h1 : ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))) ^ 2
      = (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hs]
    norm_num
  rw [Work.Spaces.Wt, Work.Spaces.wTheta, mul_pow, h1, thGam]

/-- At `z = 0` the weight `w` vanishes, hence the whole `H^k`-integrand. -/
lemma w_zero : Work.Spaces.w 0 = 0 := by
  simp [Work.Spaces.w]

lemma Wt_zero (α θ : ℝ) : Work.Spaces.Wt α 0 θ = 0 := by
  simp [Work.Spaces.Wt, w_zero]

lemma HkIntegrand_zero_left (α : ℝ) (k : ℕ) (g : ℝ → ℝ → ℝ) (θ : ℝ) :
    Work.Spaces.HkIntegrand α k g 0 θ = 0 := by
  rw [Work.Spaces.HkIntegrand, w_zero, Wt_zero]
  simp

end Work.FTS.EllipticEst
