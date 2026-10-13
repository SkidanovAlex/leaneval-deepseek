import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.PhiStar.Honesty.CptApp.EstDefs
import Submission.Work.FTS.PhiStar.Honesty.CptApp.EstAux.ZetaBound
import Submission.Work.FTS.PhiStar.Honesty.CptApp.EstAux.PlateauZero
import Submission.Work.FTS.PhiStar.Honesty.CptApp.EstAux.SmoothErr
import Submission.Work.FTS.PhiStar.Honesty.CptApp.LamAux.chiR_dzIter_boundAux
import Submission.Work.FTS.PhiStar.Honesty.CptApp.LamEst.lamContDiffOn
import Submission.Work.FTS.EllipticEst.SmoothOpenAdd
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.FTS.FinalClock.HkIntegrandMulDthSmooth
import Submission.Work.Spaces.DthIter_mul

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Honesty.CptApp.Est

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1600000
/-! ## Elementary identities for the weights

`Wt α z θ = w z · sin(2θ)^{-γ/2}` with `γ = gam α`, so its square is
`w z ^ 2 · sin(2θ)^{-γ}`, the weight occurring in the second group of `Good`. -/

theorem ems_sq_rpow {x : ℝ} (hx : 0 ≤ x) (y : ℝ) : (x ^ y) ^ 2 = x ^ (2 * y) := by
  rw [← Real.rpow_natCast (x := x ^ y) (n := 2)]
  rw [show ((2 : ℕ) : ℝ) = 2 from by norm_num]
  rw [← Real.rpow_mul hx]
  ring

theorem ems_Wt_sq {α z θ : ℝ} (hθ : 0 ≤ Real.sin (2 * θ)) :
    Work.Spaces.Wt α z θ ^ 2
      = (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
  rw [Work.Spaces.Wt, Work.Spaces.wTheta, mul_pow, ems_sq_rpow hθ]
  congr 1
  ring

/-- The weight `w` vanishes at `z = 0`. -/
theorem ems_w_zero : Work.Spaces.w 0 = 0 := by
  rw [Work.Spaces.w]; norm_num

/-- `wTheta` vanishes where `sin(2θ) = 0` (`gam α ≠ 0`). -/
theorem ems_wTheta_zero_of_sin_eq_zero {α θ : ℝ} (hα : Work.Spaces.gam α ≠ 0)
    (hs : Real.sin (2 * θ) = 0) : Work.Spaces.wTheta α θ = 0 := by
  rw [Work.Spaces.wTheta, hs,
    Real.zero_rpow (neg_ne_zero.mpr (div_ne_zero hα (by norm_num)))]

/-! ## `omegaInd · HkIntegrand = omegaPart`, and the `Good`-majorants -/

theorem ems_omegaInd_mul_HkIntegrand (α : ℝ) (k n : ℕ) (F : ℝ → ℝ → ℝ) (z θ : ℝ) :
    omegaInd n z θ * Work.Spaces.HkIntegrand α k F z θ = omegaPart α k n F z θ := by
  rw [omegaInd, omegaPart]
  split_ifs with h <;> ring

theorem ems_omegaPart_le_Good (α : ℝ) (k n : ℕ) (F : ℝ → ℝ → ℝ) {z θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) : omegaPart α k n F z θ ≤ Good α k n F z θ := by
  rw [Good]
  have h2 : 0 ≤ thShrink n θ
        * (∑ s ∈ Finset.range k, (Work.Spaces.DzIter s F z θ) ^ 2 * (Work.Spaces.w z) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) :=
    mul_nonneg (thShrink_nonneg n θ) (hkZsum_nonneg α k F z hθ)
  have h3 : 0 ≤ (∑ m ∈ Finset.range (k + 1),
        (Work.Spaces.DzIter m (fun z' _ : ℝ => mu n F z') z 0) ^ 2)
      * ((Work.Spaces.w z) ^ 2 * rhoProf α k θ) :=
    mul_nonneg (Finset.sum_nonneg fun m _ => sq_nonneg _)
      (mul_nonneg (sq_nonneg _) (rhoProf_nonneg α k hθ))
  exact le_trans (le_add_of_nonneg_right h2) (le_add_of_nonneg_right h3)

theorem ems_thShrink_sum_le_Good (α : ℝ) (k n : ℕ) (F : ℝ → ℝ → ℝ) {z θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) :
    thShrink n θ
        * (∑ s ∈ Finset.range k, (Work.Spaces.DzIter s F z θ) ^ 2 * (Work.Spaces.w z) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
      ≤ Good α k n F z θ := by
  rw [Good]
  have h1 : 0 ≤ omegaPart α k n F z θ := omegaPart_nonneg α k n F z θ
  have h3 : 0 ≤ (∑ m ∈ Finset.range (k + 1),
        (Work.Spaces.DzIter m (fun z' _ : ℝ => mu n F z') z 0) ^ 2)
      * ((Work.Spaces.w z) ^ 2 * rhoProf α k θ) :=
    mul_nonneg (Finset.sum_nonneg fun m _ => sq_nonneg _)
      (mul_nonneg (sq_nonneg _) (rhoProf_nonneg α k hθ))
  exact le_trans (le_add_of_nonneg_left h1) (le_add_of_nonneg_right h3)

/-- A single `z`-slot of the second group of `Good`, multiplied by `thShrink`. -/
theorem ems_zslot_le_thShrinkSum {α : ℝ} {k n s : ℕ} {F : ℝ → ℝ → ℝ} (hs : s < k)
    {z θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    thShrink n θ * ((Work.Spaces.DzIter s F z θ) ^ 2 * (Work.Spaces.w z) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
      ≤ thShrink n θ * (∑ s' ∈ Finset.range k, (Work.Spaces.DzIter s' F z θ) ^ 2
          * (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) := by
  refine mul_le_mul_of_nonneg_left ?_ (thShrink_nonneg n θ)
  exact Finset.single_le_sum
    (f := fun s' => (Work.Spaces.DzIter s' F z θ) ^ 2 * (Work.Spaces.w z) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
    (fun s' _ => mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))
      (Real.rpow_nonneg (sin_two_nonneg_of_mem_Iθ hθ) _))
    (Finset.mem_range.mpr hs)

end Work.FTS.PhiStar.Honesty.CptApp.Est
