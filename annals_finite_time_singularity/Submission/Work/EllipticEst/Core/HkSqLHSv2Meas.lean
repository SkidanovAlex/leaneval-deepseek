import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.aesm_of_continuousOn_Qd
import Submission.Work.Spaces.aesm_slice_of_continuousOn_Qd

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Measurability of the weighted angular slices used by `HkSqLHS_le_summands_v2`

Two facts are needed to compare the iterated Bochner integral `HkSq` with the sum of its
summands:

* `v2_aesm_slice` — for `u` of class `C^∞` on the open quadrant and every real exponent `e`,
  the function `θ ↦ (u z θ)² (w z)² sin(2θ)^e` is `AEMeasurable` on `[0,π/2]`;
* `v2_aesm_integral` — the same expression integrated in `θ` is `AEMeasurable` as a function
  of `z` on `[0,∞)`.

Both are instances of the general principle "continuity on the open quadrant gives a.e. strong
measurability for the restricted measures" (`Work.Spaces.aesm_of_continuousOn_Qd`,
`Work.Spaces.aesm_slice_of_continuousOn_Qd`), together with
`MeasureTheory.AEStronglyMeasurable.integral_prod_right'` for the second one.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.EllipticEst.Core

set_option autoImplicit false

/-- The squared radial weight `(w z)²` is continuous on the open quadrant. -/
theorem continuousOn_w_sq_Q0 :
    ContinuousOn (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
  have hfun : (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2)
      = fun p : ℝ × ℝ => (((1 + p.1) ^ 2 / p.1 ^ 2) ^ 2) := by
    funext p
    simp only [Work.Spaces.w]
  rw [hfun]
  exact (((continuousOn_const.add continuousOn_fst).pow 2).div (continuousOn_fst.pow 2)
    (fun p hp => pow_ne_zero 2 (ne_of_gt hp.1))).pow 2

/-- `θ ↦ sin(2θ)^e` is continuous on the open quadrant, for every real exponent `e`. -/
theorem continuousOn_sin_rpow_Q0 (e : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ e)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
  have hsinpos : ∀ p ∈ Set.Ioi (0 : ℝ) ×ˢ Set.Ioo 0 (π / 2), 0 < Real.sin (2 * p.2) := by
    rintro ⟨z, θ⟩ ⟨-, hθ0, hθ1⟩
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  exact ((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn).rpow_const
    (fun p hp => Or.inl (ne_of_gt (hsinpos p hp)))

/-- **Measurability of the weighted angular slice.**  For `u` of class `C^∞` on the open
quadrant, any real exponent `e` and every `z ∈ [0,∞)`, the function
`θ ↦ (u z θ)² (w z)² sin(2θ)^e` is `AEMeasurable` for `volume.restrict [0,π/2]`. -/
theorem v2_aesm_slice {u : ℝ → ℝ → ℝ}
    (hu : Work.FTS.EllipticEst.SmoothOpen u) (e : ℝ) :
    ∀ z ∈ Work.Spaces.Iz,
      AEMeasurable
        (fun θ : ℝ => (u z θ) ^ 2 * (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ e)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
  intro z hz
  rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with hz0 | hzpos
  · have hzero : (fun θ : ℝ => (u z θ) ^ 2 * (Work.Spaces.w z) ^ 2
        * (Real.sin (2 * θ)) ^ e) = fun _ : ℝ => (0 : ℝ) := by
      rw [← hz0]
      funext θ
      simp only [Work.Spaces.w]
      norm_num
    rw [hzero]
    exact aemeasurable_const
  · have hcont : ContinuousOn (fun p : ℝ × ℝ =>
        (u p.1 p.2) ^ 2 * (Work.Spaces.w p.1) ^ 2 * (Real.sin (2 * p.2)) ^ e)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
      ((hu.continuousOn.pow 2).mul continuousOn_w_sq_Q0).mul (continuousOn_sin_rpow_Q0 e)
    exact (Work.Spaces.aesm_slice_of_continuousOn_Qd _ hcont hzpos).aemeasurable

/-- **Measurability in `z` of the weighted angular integral.**  For `u` of class `C^∞` on the
open quadrant and any real exponent `e`, the function
`z ↦ (w z)² ∫_θ (u z θ)² sin(2θ)^e dθ` is `AEMeasurable` for `volume.restrict [0,∞)`. -/
theorem v2_aesm_integral {u : ℝ → ℝ → ℝ}
    (hu : Work.FTS.EllipticEst.SmoothOpen u) (e : ℝ) :
    AEMeasurable
      (fun z : ℝ => (Work.Spaces.w z) ^ 2
        * ∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2 * (Real.sin (2 * θ)) ^ e)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
  have hcont : ContinuousOn (fun p : ℝ × ℝ =>
      (Work.Spaces.w p.1) ^ 2 * ((u p.1 p.2) ^ 2 * (Real.sin (2 * p.2)) ^ e))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
    continuousOn_w_sq_Q0.mul ((hu.continuousOn.pow 2).mul (continuousOn_sin_rpow_Q0 e))
  have haesm : AEStronglyMeasurable (fun p : ℝ × ℝ =>
      (Work.Spaces.w p.1) ^ 2 * ((u p.1 p.2) ^ 2 * (Real.sin (2 * p.2)) ^ e))
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    Work.Spaces.aesm_of_continuousOn_Qd _ hcont
  have h2 : AEStronglyMeasurable
      (fun z : ℝ => ∫ θ, ((Work.Spaces.w z) ^ 2
        * ((u z θ) ^ 2 * (Real.sin (2 * θ)) ^ e))
        ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
    haesm.integral_prod_right'
  have heq : (fun z : ℝ => (Work.Spaces.w z) ^ 2
        * ∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2 * (Real.sin (2 * θ)) ^ e)
      = fun z : ℝ => ∫ θ, ((Work.Spaces.w z) ^ 2
        * ((u z θ) ^ 2 * (Real.sin (2 * θ)) ^ e))
        ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    funext z
    rw [MeasureTheory.integral_const_mul]
  rw [heq]
  exact h2.aemeasurable

end Work.EllipticEst.Core
