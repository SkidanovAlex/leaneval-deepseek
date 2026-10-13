import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllSol.PkgK5.radialAuxInt

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-!
# Radial profiles vs. their `sin (2θ)`-multiples: the `H^k`-integrands

Part 4 of the proof of `Work.FTS.EllSol.PkgK5.radialHkNorm_le_sinMul`: the evaluation of the
`H^k`-integrand of a radial profile and of its `sin(2θ)`-multiple, and of the corresponding
`θ`-integrals.
-/

namespace Work.FTS.EllSol.PkgK5

namespace Radial

theorem HkIntegrand_radial (α : ℝ) (k : ℕ) (Λ : ℝ → ℝ)
    (hΛ : ∀ n : ℕ, ContDiffOn ℝ n Λ (Set.Ioi 0)) (z θ : ℝ) (hz : 0 < z)
    (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.HkIntegrand α k (fun z θ => Λ z) z θ
      = Phi k Λ z * Real.sin (2 * θ) ^ (-Work.Spaces.eta) := by
  have heta : Work.Spaces.eta ≠ 0 := by norm_num [Work.Spaces.eta]
  rw [Work.Spaces.HkIntegrand]
  have hzsum : (∑ i ∈ Finset.range (k + 1),
      (Work.Spaces.DzIter i (fun z θ => Λ z) z θ
        * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2)
      = Phi k Λ z * Real.sin (2 * θ) ^ (-Work.Spaces.eta) := by
    rw [Phi, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [DzIter_radial Λ i hz θ,
      Work.Spaces.sq_mul_div_rpow (RIter i Λ z) (Work.Spaces.w z) (Real.sin (2 * θ))
        Work.Spaces.eta (sin_two_nonneg hθ) heta]
    ring
  have hmix : (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
      (if 1 ≤ i ∧ i + j ≤ k then
        (Work.Spaces.mixed j i (fun z θ => Λ z) z θ * Work.Spaces.Wt α z θ) ^ 2 else 0)) = 0 := by
    refine Finset.sum_eq_zero (fun i hi => Finset.sum_eq_zero (fun j hj => ?_))
    split_ifs with h
    · rw [mixed_radial_zero Λ j i h.1 z θ]; ring
    · rfl
  rw [hzsum, hmix, add_zero]

theorem HkIntegrand_sinMul (α : ℝ) (k : ℕ) (Λ : ℝ → ℝ) (hα : 0 < α)
    (hΛ : ∀ n : ℕ, ContDiffOn ℝ n Λ (Set.Ioi 0)) (z θ : ℝ) (hz : 0 < z)
    (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.HkIntegrand α k (fun z θ => Λ z * Real.sin (2 * θ)) z θ
      = Phi k Λ z * Real.sin (2 * θ) ^ (2 - Work.Spaces.eta)
        + ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
            (if 1 ≤ i ∧ i + j ≤ k then
              (RIter j Λ z * Work.Spaces.w z) ^ 2
                * ((Work.FTS.EllipticEst.LopIter i (fun θ : ℝ => Real.sin (2 * θ)) θ) ^ 2
                    * Real.sin (2 * θ) ^ (-(Work.Spaces.gam α)))
             else 0) := by
  have hgam : Work.Spaces.gam α ≠ 0 := by
    rw [Work.Spaces.gam]; intro h; linarith
  have heta : Work.Spaces.eta ≠ 2 := by norm_num [Work.Spaces.eta]
  have heta0 : Work.Spaces.eta ≠ 0 := by norm_num [Work.Spaces.eta]
  have hS : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg hθ
  have hhalf : (Real.sin (2 * θ) ^ (-(Work.Spaces.gam α / 2))) ^ 2
      = Real.sin (2 * θ) ^ (-(Work.Spaces.gam α)) := rpow_neg_half_sq _ hgam hS
  rw [Work.Spaces.HkIntegrand]
  have hzsum : (∑ i ∈ Finset.range (k + 1),
      (Work.Spaces.DzIter i (fun z θ => Λ z * Real.sin (2 * θ)) z θ
        * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2)
      = Phi k Λ z * Real.sin (2 * θ) ^ (2 - Work.Spaces.eta) := by
    rw [Phi, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [DzIter_mul_theta Λ hΛ (fun θ : ℝ => Real.sin (2 * θ)) i hz θ,
      Work.Spaces.sq_mul_div_rpow (RIter i Λ z * Real.sin (2 * θ)) (Work.Spaces.w z) (Real.sin (2 * θ))
        Work.Spaces.eta hS heta0]
    calc (RIter i Λ z * Real.sin (2 * θ)) ^ 2 * (Work.Spaces.w z) ^ 2
          * Real.sin (2 * θ) ^ (-(Work.Spaces.eta))
        = (RIter i Λ z * Work.Spaces.w z) ^ 2
            * (Real.sin (2 * θ) ^ 2 * Real.sin (2 * θ) ^ (-(Work.Spaces.eta))) := by ring
      _ = (RIter i Λ z * Work.Spaces.w z) ^ 2 * Real.sin (2 * θ) ^ (2 - Work.Spaces.eta) := by
          rw [sq_mul_rpow_neg Work.Spaces.eta heta hS]
  have hmix : (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
      (if 1 ≤ i ∧ i + j ≤ k then
        (Work.Spaces.mixed j i (fun z θ => Λ z * Real.sin (2 * θ)) z θ
          * Work.Spaces.Wt α z θ) ^ 2 else 0))
      = ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
          (if 1 ≤ i ∧ i + j ≤ k then
            (RIter j Λ z * Work.Spaces.w z) ^ 2
              * ((Work.FTS.EllipticEst.LopIter i (fun θ : ℝ => Real.sin (2 * θ)) θ) ^ 2
                  * Real.sin (2 * θ) ^ (-(Work.Spaces.gam α)))
           else 0) := by
    refine Finset.sum_congr rfl (fun i hi => Finset.sum_congr rfl (fun j hj => ?_))
    by_cases h : 1 ≤ i ∧ i + j ≤ k
    · rw [if_pos h, if_pos h, mixed_sinMul Λ hΛ j i hz θ]
      simp only [Work.Spaces.Wt, Work.Spaces.wTheta]
      calc (RIter j Λ z * Work.FTS.EllipticEst.LopIter i (fun θ : ℝ => Real.sin (2 * θ)) θ
            * (Work.Spaces.w z * Real.sin (2 * θ) ^ (-(Work.Spaces.gam α / 2)))) ^ 2
          = ((RIter j Λ z * Work.FTS.EllipticEst.LopIter i (fun θ : ℝ => Real.sin (2 * θ)) θ) ^ 2)
              * ((Work.Spaces.w z) ^ 2
                * (Real.sin (2 * θ) ^ (-(Work.Spaces.gam α / 2))) ^ 2) := by ring
        _ = (RIter j Λ z * Work.Spaces.w z) ^ 2
              * ((Work.FTS.EllipticEst.LopIter i (fun θ : ℝ => Real.sin (2 * θ)) θ) ^ 2
                  * Real.sin (2 * θ) ^ (-(Work.Spaces.gam α))) := by
              rw [hhalf]; ring
    · rw [if_neg h, if_neg h]
  rw [hzsum, hmix]

/-- The `θ`-integral of the `H^k`-integrand of the radial function `Λ`. -/
theorem thetaIntegral_radial (α : ℝ) (k : ℕ) (Λ : ℝ → ℝ)
    (hΛ : ∀ n : ℕ, ContDiffOn ℝ n Λ (Set.Ioi 0)) {z : ℝ} (hz : 0 < z) :
    (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k (fun z θ => Λ z) z θ)
      = Phi k Λ z * Aeta := by
  rw [show (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k (fun z θ => Λ z) z θ)
      = ∫ θ in Work.Spaces.Iθ, Phi k Λ z * Real.sin (2 * θ) ^ (-Work.Spaces.eta) from
    MeasureTheory.setIntegral_congr_fun measurableSet_Icc
      (fun θ hθ => HkIntegrand_radial α k Λ hΛ z θ hz hθ)]
  rw [MeasureTheory.integral_const_mul]
  rfl

/-- The `θ`-integral of the `H^k`-integrand of `(z,θ) ↦ Λ z · sin(2θ)`. -/
theorem thetaIntegral_sinMul (α : ℝ) (k : ℕ) (Λ : ℝ → ℝ)
    (hα : 0 < α) (hα1 : α ≤ 1 / 4)
    (hΛ : ∀ n : ℕ, ContDiffOn ℝ n Λ (Set.Ioi 0)) {z : ℝ} (hz : 0 < z) :
    (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k (fun z θ => Λ z * Real.sin (2 * θ)) z θ)
      = Phi k Λ z * Aeta2 + W α k Λ z := by
  obtain ⟨A, hApos, hAbound⟩ := Work.FTS.EllipticEst.Lop_iter_sin_bound k
  have heta1 : -1 < 2 - Work.Spaces.eta := by norm_num [Work.Spaces.eta]
  have heta2 : 2 - Work.Spaces.eta ≤ 2 := by norm_num [Work.Spaces.eta]
  rw [show (∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α k (fun z θ => Λ z * Real.sin (2 * θ)) z θ)
      = ∫ θ in Work.Spaces.Iθ, (Phi k Λ z * Real.sin (2 * θ) ^ (2 - Work.Spaces.eta)
          + ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
              (if 1 ≤ i ∧ i + j ≤ k then
                (RIter j Λ z * Work.Spaces.w z) ^ 2
                  * ((Work.FTS.EllipticEst.LopIter i (fun θ : ℝ => Real.sin (2 * θ)) θ) ^ 2
                      * Real.sin (2 * θ) ^ (-(Work.Spaces.gam α)))
               else 0)) from
    MeasureTheory.setIntegral_congr_fun measurableSet_Icc
      (fun θ hθ => HkIntegrand_sinMul α k Λ hα hΛ z θ hz hθ)]
  have hInt1 : Integrable (fun θ : ℝ => Phi k Λ z * Real.sin (2 * θ) ^ (2 - Work.Spaces.eta))
      (volume.restrict Work.Spaces.Iθ) := (integrable_sin_rpow heta1 heta2).const_mul _
  have hterm : ∀ i j : ℕ, Integrable (fun θ : ℝ =>
      (if 1 ≤ i ∧ i + j ≤ k then
        (RIter j Λ z * Work.Spaces.w z) ^ 2
          * ((Work.FTS.EllipticEst.LopIter i (fun θ : ℝ => Real.sin (2 * θ)) θ) ^ 2
              * Real.sin (2 * θ) ^ (-(Work.Spaces.gam α)))
       else 0)) (volume.restrict Work.Spaces.Iθ) := by
    intro i j
    by_cases h : 1 ≤ i ∧ i + j ≤ k
    · have hfun : (fun θ : ℝ => (if 1 ≤ i ∧ i + j ≤ k then
          (RIter j Λ z * Work.Spaces.w z) ^ 2
            * ((Work.FTS.EllipticEst.LopIter i (fun θ : ℝ => Real.sin (2 * θ)) θ) ^ 2
                * Real.sin (2 * θ) ^ (-(Work.Spaces.gam α)))
         else 0))
          = (fun θ : ℝ => (RIter j Λ z * Work.Spaces.w z) ^ 2
            * ((Work.FTS.EllipticEst.LopIter i (fun θ : ℝ => Real.sin (2 * θ)) θ) ^ 2
                * Real.sin (2 * θ) ^ (-(Work.Spaces.gam α)))) := by
        funext θ; rw [if_pos h]
      rw [hfun]
      exact (integrable_angCoef hα hα1 hApos.le (fun θ hθ => hAbound i (by omega) θ hθ)).const_mul _
    · have hfun : (fun θ : ℝ => (if 1 ≤ i ∧ i + j ≤ k then
          (RIter j Λ z * Work.Spaces.w z) ^ 2
            * ((Work.FTS.EllipticEst.LopIter i (fun θ : ℝ => Real.sin (2 * θ)) θ) ^ 2
                * Real.sin (2 * θ) ^ (-(Work.Spaces.gam α)))
         else 0)) = (fun _ : ℝ => (0 : ℝ)) := by
        funext θ; rw [if_neg h]
      rw [hfun]
      exact integrable_zero _ _ _
  have hInt2 : Integrable (fun θ : ℝ =>
      ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
        (if 1 ≤ i ∧ i + j ≤ k then
          (RIter j Λ z * Work.Spaces.w z) ^ 2
            * ((Work.FTS.EllipticEst.LopIter i (fun θ : ℝ => Real.sin (2 * θ)) θ) ^ 2
                * Real.sin (2 * θ) ^ (-(Work.Spaces.gam α)))
         else 0)) (volume.restrict Work.Spaces.Iθ) :=
    integrable_finsetSum _ (fun i hi => integrable_finsetSum _ (fun j hj => hterm i j))
  rw [MeasureTheory.integral_add hInt1 hInt2]
  have hsum : (∫ θ in Work.Spaces.Iθ, ∑ i ∈ Finset.range (k + 1),
        ∑ j ∈ Finset.range (k + 1),
        (if 1 ≤ i ∧ i + j ≤ k then
          (RIter j Λ z * Work.Spaces.w z) ^ 2
            * ((Work.FTS.EllipticEst.LopIter i (fun θ : ℝ => Real.sin (2 * θ)) θ) ^ 2
                * Real.sin (2 * θ) ^ (-(Work.Spaces.gam α)))
         else 0))
      = W α k Λ z := by
    rw [MeasureTheory.integral_finsetSum _
      (fun i hi => integrable_finsetSum _ (fun j hj => hterm i j))]
    rw [show W α k Λ z = ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
        (if 1 ≤ i ∧ i + j ≤ k then
          (RIter j Λ z * Work.Spaces.w z) ^ 2 * Bcoef α i else 0) from rfl]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [MeasureTheory.integral_finsetSum _ (fun j hj => hterm i j)]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    by_cases h : 1 ≤ i ∧ i + j ≤ k
    · have hfun : (fun θ : ℝ => (if 1 ≤ i ∧ i + j ≤ k then
          (RIter j Λ z * Work.Spaces.w z) ^ 2
            * ((Work.FTS.EllipticEst.LopIter i (fun θ : ℝ => Real.sin (2 * θ)) θ) ^ 2
                * Real.sin (2 * θ) ^ (-(Work.Spaces.gam α)))
         else 0))
          = (fun θ : ℝ => (RIter j Λ z * Work.Spaces.w z) ^ 2
            * ((Work.FTS.EllipticEst.LopIter i (fun θ : ℝ => Real.sin (2 * θ)) θ) ^ 2
                * Real.sin (2 * θ) ^ (-(Work.Spaces.gam α)))) := by
        funext θ; rw [if_pos h]
      rw [hfun, MeasureTheory.integral_const_mul, if_pos h]
      rfl
    · have hfun : (fun θ : ℝ => (if 1 ≤ i ∧ i + j ≤ k then
          (RIter j Λ z * Work.Spaces.w z) ^ 2
            * ((Work.FTS.EllipticEst.LopIter i (fun θ : ℝ => Real.sin (2 * θ)) θ) ^ 2
                * Real.sin (2 * θ) ^ (-(Work.Spaces.gam α)))
         else 0)) = (fun _ : ℝ => (0 : ℝ)) := by
        funext θ; rw [if_neg h]
      rw [hfun, if_neg h]
      exact MeasureTheory.integral_zero _ _
  rw [MeasureTheory.integral_const_mul, hsum]
  rfl

end Radial

end Work.FTS.EllSol.PkgK5
